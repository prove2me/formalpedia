-- Prove2me | solution 1 for FunctionalInequalities.Analysis.volume_subgradient_two_points_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:27.761008+00:00
-- url     : https://prove2.me/submissions/31fe6563-b6e7-4d0c-93ff-4afb4c6da114

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
import Theorems.Thm_FunctionalInequalities_Analysis_ConvexOn_ae_differentiableAt_of_isOpen_readable
import Theorems.Thm_FunctionalInequalities_Analysis_conjugate_maximizer_eq_gradient_readable
import Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_legendre_readable

section
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- One finite value excludes `-∞` for the entire Legendre transform. -/
theorem FunctionalInequalities.Analysis.legendre_ne_bot (φ : E → EReal) (hφ : ProperPotential φ) (y : E) :
    legendre φ y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hφ.2
  have hb := hφ.1 x
  lift φ x to ℝ using ⟨hx, hb⟩ with r hr
  have hle : ((inner ℝ x y - r : ℝ) : EReal) ≤ legendre φ y := by
    change ((inner ℝ x y - r : ℝ) : EReal) ≤
      ⨆ z : E, (inner ℝ z y : EReal) - φ z
    simpa only [← hr, EReal.coe_sub] using
      (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hle)
end
end
end

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT14ASubgradientAeInjective
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem FunctionalInequalities.Analysis.legendre_eq_of_subgradient (u : E → ℝ) (x p : E)
    (hsub : ∀ z, u x + ⟪p, z - x⟫ ≤ u z) :
    (⟪x, p⟫ : EReal) - (u x : EReal) =
      legendre (fun z => (u z : EReal)) p := by
  apply le_antisymm
  · change (⟪x, p⟫ : EReal) - (u x : EReal) ≤
      ⨆ z : E, (⟪z, p⟫ : EReal) - (u z : EReal)
    exact le_iSup (fun z : E => (⟪z, p⟫ : EReal) - (u z : EReal)) x
  · change (⨆ z : E, (⟪z, p⟫ : EReal) - (u z : EReal)) ≤
      (⟪x, p⟫ : EReal) - (u x : EReal)
    apply iSup_le
    intro z
    have hz := hsub z
    rw [inner_sub_right] at hz
    rw [← real_inner_comm p z, ← real_inner_comm p x] at hz
    have hz' : ⟪z, p⟫ - u z ≤ ⟪x, p⟫ - u x := by
      linarith
    simpa only [EReal.coe_sub] using
      (EReal.coe_le_coe_iff.mpr hz')
private theorem FunctionalInequalities.Analysis.convex_legendre_finite_domain (φ : E → EReal) (hφ : ProperPotential φ) :
    Convex ℝ {q : E | legendre φ q ≠ ⊤} := by
  intro q₁ hq₁ q₂ hq₂ a b ha hb hab
  have hq₁bot : legendre φ q₁ ≠ ⊥ := legendre_ne_bot φ hφ q₁
  have hq₂bot : legendre φ q₂ ≠ ⊥ := legendre_ne_bot φ hφ q₂
  have hq₁epi :
      (q₁, (legendre φ q₁).toReal) ∈
        {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)} := by
    change legendre φ q₁ ≤ ((legendre φ q₁).toReal : EReal)
    rw [EReal.coe_toReal hq₁ hq₁bot]
  have hq₂epi :
      (q₂, (legendre φ q₂).toReal) ∈
        {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)} := by
    change legendre φ q₂ ≤ ((legendre φ q₂).toReal : EReal)
    rw [EReal.coe_toReal hq₂ hq₂bot]
  have hcomb := (convex_epigraph_legendre_readable φ) hq₁epi hq₂epi ha hb hab
  change legendre φ (a • q₁ + b • q₂) ≤
    ((a * (legendre φ q₁).toReal + b * (legendre φ q₂).toReal : ℝ) : EReal) at hcomb
  intro htop
  rw [htop] at hcomb
  exact (not_le_of_gt (EReal.coe_lt_top _)) hcomb
/-- **Almost every subgradient belongs to a single point** (weak Letwin route, the
Alexandrov identity): for a convex Lipschitz `u` on a finite-dimensional inner product space, the
set of `p` that are subgradients of `u` at two distinct points is Lebesgue-null (such `p` are
non-differentiability points of the conjugate `u*`, or frontier points of its domain). -/
theorem solution [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u) :
    (volume : Measure E) {p : E | ∃ x y : E, x ≠ y ∧ (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧
      (∀ z, u y + ⟪p, z - y⟫ ≤ u z)} = 0 := by
  have _ := hu
  have _ := hconv
  classical
  let φ : E → EReal := fun x => (u x : EReal)
  let Dom : Set E := {q | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤}
  let g : E → ℝ := fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal
  let S : Set E := {p : E | ∃ x y : E, x ≠ y ∧
    (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧
    (∀ z, u y + ⟪p, z - y⟫ ≤ u z)}
  change (volume : Measure E) S = 0
  have hφ : FunctionalInequalities.Analysis.ProperPotential φ := by
    refine ⟨?_, ⟨0, ?_⟩⟩
    · intro x
      exact EReal.coe_ne_bot _
    · exact EReal.coe_ne_top _
  have hDom : Convex ℝ Dom := by
    simpa only [Dom] using FunctionalInequalities.Analysis.convex_legendre_finite_domain φ hφ
  have hconvG : ConvexOn ℝ (interior Dom) g := by
    refine ⟨hDom.interior, ?_⟩
    intro q₁ hq₁ q₂ hq₂ a b ha hb hab
    have hq₁D : q₁ ∈ Dom := interior_subset hq₁
    have hq₂D : q₂ ∈ Dom := interior_subset hq₂
    have hqD : a • q₁ + b • q₂ ∈ Dom :=
      hDom hq₁D hq₂D ha hb hab
    have hq₁bot : FunctionalInequalities.Analysis.legendre φ q₁ ≠ ⊥ := FunctionalInequalities.Analysis.legendre_ne_bot φ hφ q₁
    have hq₂bot : FunctionalInequalities.Analysis.legendre φ q₂ ≠ ⊥ := FunctionalInequalities.Analysis.legendre_ne_bot φ hφ q₂
    have hqbot : FunctionalInequalities.Analysis.legendre φ (a • q₁ + b • q₂) ≠ ⊥ :=
      FunctionalInequalities.Analysis.legendre_ne_bot φ hφ (a • q₁ + b • q₂)
    have hq₁epi :
        (q₁, g q₁) ∈ {p : E × ℝ | FunctionalInequalities.Analysis.legendre φ p.1 ≤ (p.2 : EReal)} := by
      change FunctionalInequalities.Analysis.legendre φ q₁ ≤ ((FunctionalInequalities.Analysis.legendre φ q₁).toReal : EReal)
      rw [EReal.coe_toReal hq₁D hq₁bot]
    have hq₂epi :
        (q₂, g q₂) ∈ {p : E × ℝ | FunctionalInequalities.Analysis.legendre φ p.1 ≤ (p.2 : EReal)} := by
      change FunctionalInequalities.Analysis.legendre φ q₂ ≤ ((FunctionalInequalities.Analysis.legendre φ q₂).toReal : EReal)
      rw [EReal.coe_toReal hq₂D hq₂bot]
    have hE := (FunctionalInequalities.Analysis.convex_epigraph_legendre_readable φ) hq₁epi hq₂epi ha hb hab
    change FunctionalInequalities.Analysis.legendre φ (a • q₁ + b • q₂) ≤
      ((a * g q₁ + b * g q₂ : ℝ) : EReal) at hE
    have hcoe :
        (g (a • q₁ + b • q₂) : EReal) =
          FunctionalInequalities.Analysis.legendre φ (a • q₁ + b • q₂) := by
      dsimp [g]
      exact EReal.coe_toReal hqD hqbot
    have hreal :
        g (a • q₁ + b • q₂) ≤ a * g q₁ + b * g q₂ := by
      apply EReal.coe_le_coe_iff.mp
      rw [hcoe]
      exact hE
    simpa only [smul_eq_mul] using hreal
  have hae :
      ∀ᵐ q : E ∂(volume : Measure E),
        q ∈ interior Dom → DifferentiableAt ℝ g q :=
    FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen_readable
      (volume : Measure E) isOpen_interior hconvG
  let B : Set E := {q | q ∈ interior Dom ∧ ¬ DifferentiableAt ℝ g q}
  have hB : (volume : Measure E) B = 0 := by
    have hnot : ∀ᵐ q : E ∂(volume : Measure E), q ∉ B := by
      filter_upwards [hae] with q hq
      intro hqB
      change q ∈ interior Dom ∧ ¬ DifferentiableAt ℝ g q at hqB
      exact hqB.2 (hq hqB.1)
    have hz := ae_iff.mp hnot
    have hset : {q : E | ¬ q ∉ B} = B := by
      ext q
      simp
    rw [hset] at hz
    exact hz
  have hfrontier : (volume : Measure E) (frontier Dom) = 0 :=
    Convex.addHaar_frontier (volume : Measure E) hDom
  have hsubset : S ⊆ frontier Dom ∪ B := by
    intro p hp
    rcases hp with ⟨x, y, hxy, hx, hy⟩
    have hxEq : (⟪x, p⟫ : EReal) - φ x = FunctionalInequalities.Analysis.legendre φ p := by
      simpa only [φ] using FunctionalInequalities.Analysis.legendre_eq_of_subgradient u x p hx
    have hyEq : (⟪y, p⟫ : EReal) - φ y = FunctionalInequalities.Analysis.legendre φ p := by
      simpa only [φ] using FunctionalInequalities.Analysis.legendre_eq_of_subgradient u y p hy
    have hterm : (⟪x, p⟫ : EReal) - φ x ≠ ⊤ := by
      intro ht
      have ht' : ((⟪x, p⟫ - u x : ℝ) : EReal) = ⊤ := by
        simpa only [φ, EReal.coe_sub] using ht
      exact EReal.coe_ne_top _ ht'
    have hpD : p ∈ Dom := by
      intro htop
      exact hterm (hxEq.trans htop)
    have hpcl : p ∈ closure Dom := subset_closure hpD
    rw [closure_eq_interior_union_frontier] at hpcl
    rcases hpcl with hpI | hpF
    · right
      change p ∈ interior Dom ∧ ¬ DifferentiableAt ℝ g p
      refine ⟨hpI, ?_⟩
      intro hd
      have hd' : DifferentiableAt ℝ
          (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) p := by
        simpa only [g] using hd
      have hxg := FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient_readable φ hφ hpI hd' x hxEq
      have hyg := FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient_readable φ hφ hpI hd' y hyEq
      exact hxy (hxg.trans hyg.symm)
    · left
      exact hpF
  exact measure_mono_null hsubset (measure_union_null hfrontier hB)
