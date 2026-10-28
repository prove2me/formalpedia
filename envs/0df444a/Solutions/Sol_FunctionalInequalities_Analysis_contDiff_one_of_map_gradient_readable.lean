-- Prove2me | solution 1 for FunctionalInequalities.Analysis.contDiff_one_of_map_gradient_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:08.348991+00:00
-- url     : https://prove2.me/submissions/195620a2-6b76-4e50-ad8d-b8aa9f5dac56

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_contDiff_one_of_convexOn_of_differentiable_readable
import Theorems.Thm_FunctionalInequalities_Analysis_convexOn_truncatedConjugate_readable
import Theorems.Thm_FunctionalInequalities_Analysis_eq_of_contact_of_sublevel_bounds_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_inverse_subgradient_volume_bounds_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_subgradient_slope_le_inner_add_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_truncatedConjugate_eq_readable
import Theorems.Thm_FunctionalInequalities_Analysis_isOpen_setOf_truncatedConjugate_maximizer_lt_readable
import Theorems.Thm_FunctionalInequalities_Analysis_strictConvexOn_of_map_gradient_readable
import Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_sub_inner_add_const_readable
import Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_truncatedConjugate_eq_readable
import Theorems.Thm_FunctionalInequalities_Analysis_subgradient_mem_interior_of_strictConvexOn_readable
import Theorems.Thm_FunctionalInequalities_Analysis_subgradient_mem_of_ae_gradient_mem_readable
import Theorems.Thm_FunctionalInequalities_Analysis_truncatedConjugate_centered_spec_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_of_convexOn_of_unique_subgradient_readable

section
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT5CUniqueSubgradientDifferentiable
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
/-- **A convex function with a unique subgradient at every point is differentiable** (weak Letwin
route: "singleton subdifferential ⇒ C¹", differentiability half): on a finite-dimensional
inner product space, if the subgradient inequality `u x + ⟪g, y - x⟫ ≤ u y` (all `y`) is satisfied by
exactly one `g` at every `x`, then `u` is differentiable (with that `g` as gradient; `C¹` then follows
from `contDiff_one_of_convexOn_of_differentiable`). -/
theorem FunctionalInequalities.Analysis.differentiable_of_convexOn_of_unique_subgradient {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hsub : ∀ x, ∃! g : E, ∀ y, u x + ⟪g, y - x⟫ ≤ u y) :
    Differentiable ℝ u := by
  intro x
  obtain ⟨g, hg, huniq⟩ := hsub x
  exact (hasFDerivAt_of_convexOn_of_unique_subgradient_readable hconv x g hg huniq).differentiableAt
end FiniteDimensional
end InnerProduct
end LT5CUniqueSubgradientDifferentiable
section LT5DUniqueSubgradientC1
section
/-- **Singleton subdifferential ⇒ `C¹`** (weak Letwin route): a
convex function on a finite-dimensional inner product space with exactly one subgradient at every
point is continuously differentiable. -/
theorem FunctionalInequalities.Analysis.contDiff_one_of_convexOn_of_unique_subgradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hsub : ∀ x, ∃! g : E, ∀ y, u x + ⟪g, y - x⟫ ≤ u y) :
    ContDiff ℝ 1 u := by
  exact contDiff_one_of_convexOn_of_differentiable_readable hconv
    (differentiable_of_convexOn_of_unique_subgradient hconv hsub)
end
end LT5DUniqueSubgradientC1
end
end

section
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11E6SubgradientimageSubAffine
open scoped RealInnerProductSpace
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.volume_subgradientImage_sub_inner_add_const [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (p : E) (c : ℝ) (G : Set E) :
    (volume : Measure E) (subgradientImage (fun x => u x - (⟪p, x⟫ + c)) G) =
      (volume : Measure E) (subgradientImage u G) := by
  rw [subgradientImage_sub_inner_add_const_readable]
  simp only [sub_eq_add_neg, Set.image_add_right, neg_neg]
  exact measure_preimage_add_right (volume : Measure E) p (subgradientImage u G)
end InnerProduct
end LT11E6SubgradientimageSubAffine
end
end

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F3TruncatedConjugateSubgradients
open scoped RealInnerProductSpace Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.n7_support_min {u : E → ℝ} {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    IsMinOn (fun y => u y - ⟪p, y⟫) univ x := by
  intro y _
  have h := hp y
  rw [inner_sub_right] at h
  dsimp
  linarith
private lemma FunctionalInequalities.Analysis.n7_conjugate_eq_of_support {u : E → ℝ} {M : ℝ} {x p : E}
    (hx : x ∈ closedBall (0 : E) M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    truncatedConjugate u M p = ⟪p, x⟫ - u x := by
  have hb : ∀ y, ⟪p, y⟫ - u y ≤ ⟪p, x⟫ - u x := by
    intro y
    have h := hp y
    rw [inner_sub_right] at h
    linarith
  apply le_antisymm
  · exact csSup_le ⟨_, ⟨x, hx, rfl⟩⟩ (by
      rintro _ ⟨y, _, rfl⟩
      exact hb y)
  · exact le_csSup ⟨_, by
      rintro _ ⟨y, _, rfl⟩
      exact hb y⟩ ⟨x, hx, rfl⟩
/-- For strictly convex `u`, a subgradient `p` at a point `x` of the open ball has `x` as its only ball
maximiser. -/
theorem FunctionalInequalities.Analysis.eq_of_truncatedConjugate_eq_of_subgradient [FiniteDimensional ℝ E] {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} {x p : E} (hx : ‖x‖ < M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) {x' : E} (hx' : x' ∈ closedBall (0 : E) M)
    (heq : truncatedConjugate u M p = ⟪p, x'⟫ - u x') : x' = x := by
  have hxeq := n7_conjugate_eq_of_support (mem_closedBall_zero_iff.mpr hx.le) hp
  have hp' : ∀ y, u x' + ⟪p, y - x'⟫ ≤ u y := by
    intro y
    have h := hp y
    rw [inner_sub_right] at h ⊢
    linarith [heq, hxeq]
  exact (hstrict.sub_concaveOn ((innerₗ E p).concaveOn convex_univ)).eq_of_isMinOn
    (n7_support_min hp') (n7_support_min hp)
    ((subset_univ (closedBall (0 : E) M)) hx') (mem_univ x)
end InnerProduct
end LT11F3TruncatedConjugateSubgradients
section LT11F7MomentC1
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal
private lemma FunctionalInequalities.Analysis.t11f7_small_sublevel {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (hcompact : IsCompact {x | f x ≤ 1})
    {A : Set X} (hA : IsOpen A) (hzero : ∀ x, f x = 0 → x ∈ A) :
    ∃ R : ℝ, 0 < R ∧ {x | f x ≤ R} ⊆ A := by
  classical
  by_cases hne : ({x | f x ≤ 1} \ A).Nonempty
  · obtain ⟨z, hz, hmin⟩ :=
      (hcompact.diff hA).exists_isMinOn hne hf.continuousOn
    have hzpos : 0 < f z := by
      have hznot : f z ≠ 0 := fun h => hz.2 (hzero z h)
      exact lt_of_le_of_ne (hnonneg z) (Ne.symm hznot)
    refine ⟨min 1 (f z / 2), lt_min zero_lt_one (by linarith), ?_⟩
    intro x hx
    change f x ≤ min 1 (f z / 2) at hx
    by_contra hxA
    have hxB : x ∈ {x | f x ≤ 1} \ A :=
      ⟨hx.trans (min_le_left _ _), hxA⟩
    have hzx : f z ≤ f x := hmin hxB
    have hhalf : f x ≤ f z / 2 := hx.trans (min_le_right _ _)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    by_contra hxA
    exact hne ⟨x, hx, hxA⟩
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.t11f7_support_unique {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {x z p : E}
    (hx : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
    (hz : ∀ y, u z + ⟪p, y - z⟫ ≤ u y) :
    x = z := by
  apply (hstrict.sub_concaveOn ((innerₗ E p).concaveOn convex_univ)).eq_of_isMinOn
    ?_ ?_ (mem_univ x) (mem_univ z)
  · intro y _
    change u x - ⟪p, x⟫ ≤ u y - ⟪p, y⟫
    have h := hx y
    rw [inner_sub_right] at h
    linarith
  · intro y _
    change u z - ⟪p, z⟫ ≤ u y - ⟪p, y⟫
    have h := hz y
    rw [inner_sub_right] at h
    linarith
set_option maxHeartbeats 800000 in
/-- **The moment potential is `C¹`** (weak Letwin route; KLS500
`moment_contDiff_one_closedTarget`): a convex Lipschitz `u` with `∫ e^{-u} = 1` whose gradient pushes
`e^{-u} dx` forward to `1_K e^{-V} dx` (`K` compact convex with nonempty interior, `V` continuous) has exactly
one subgradient at every point, hence is continuously differentiable. -/
theorem solution
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    {V : E → ℝ} (hV : Continuous V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    ContDiff ℝ 1 u := by
  classical
  have hstrict : StrictConvexOn ℝ univ u :=
    FunctionalInequalities.Analysis.strictConvexOn_of_map_gradient_readable hu hconv hnorm hK hKc
      (hKint.mono interior_subset) hV hmap
  let ρ : E → ℝ≥0∞ :=
    K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))
  let w : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-u x))
  have hρ : Measurable ρ :=
    hV.measurable.neg.exp.ennreal_ofReal.indicator hK.measurableSet
  have hw : Measurable w :=
    hu.continuous.measurable.neg.exp.ennreal_ofReal
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have htilt : (volume : Measure E).tilted (-u) = volume.withDensity w := by
    change (volume : Measure E).withDensity
      (fun x => ENNReal.ofReal
        (Real.exp (-u x) / ∫ y, Real.exp (-u y) ∂(volume : Measure E))) =
      volume.withDensity w
    simp only [hnorm, div_one, w]
  have hmap' :
      ((volume : Measure E).withDensity w).map (gradient u) =
        volume.withDensity ρ := by
    rw [← htilt]
    exact hmap
  have hμK : ∀ᵐ p ∂(volume : Measure E).withDensity ρ, p ∈ K := by
    apply (ae_withDensity_iff hρ).2
    exact Filter.Eventually.of_forall fun p hp => by
      by_contra h
      exact hp (Set.indicator_of_notMem h _)
  have hνK :
      ∀ᵐ x ∂(volume : Measure E).withDensity w, gradient u x ∈ K := by
    apply ae_of_ae_map hgrad.aemeasurable
    rw [hmap']
    exact hμK
  have hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K := by
    have h := (ae_withDensity_iff hw).1 hνK
    filter_upwards [h] with x hx
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-u x))))
  have hsubK : ∀ x p, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) → p ∈ K := by
    intro x p hp
    exact FunctionalInequalities.Analysis.subgradient_mem_of_ae_gradient_mem_readable hu hconv hK.isClosed hKc hae hp
  have hsubint : ∀ x p, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) →
      p ∈ interior K := by
    intro x p hp
    exact FunctionalInequalities.Analysis.subgradient_mem_interior_of_strictConvexOn_readable hstrict hKc hKint hsubK hp
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hV.continuousOn
  have hρK : ∀ p ∈ K,
      ENNReal.ofReal (Real.exp (-D)) ≤ ρ p ∧
        ρ p ≤ ENNReal.ofReal (Real.exp D) := by
    intro p hp
    have hbound : -D ≤ V p ∧ V p ≤ D :=
      abs_le.mp (by simpa only [Real.norm_eq_abs] using hD p hp)
    dsimp only [ρ]
    rw [Set.indicator_of_mem hp]
    constructor
    · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hbound.2]))
    · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hbound.1]))
  apply FunctionalInequalities.Analysis.contDiff_one_of_convexOn_of_unique_subgradient hconv
  intro xc
  obtain ⟨p₀, hp₀, _⟩ := FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_readable hconv xc (0 : E)
  let M : ℝ := ‖xc‖ + 1
  have hxc : ‖xc‖ < M := by dsimp only [M]; linarith
  have hM : 0 ≤ M := (norm_nonneg xc).trans hxc.le
  let f : E → ℝ := fun p => FunctionalInequalities.Analysis.truncatedConjugate u M p - ⟪p, xc⟫ + u xc
  have hspec := FunctionalInequalities.Analysis.truncatedConjugate_centered_spec_readable hconv hxc
  have hfnonneg : ∀ p, 0 ≤ f p := hspec.1
  have hfzero : ∀ p, f p = 0 ↔ ∀ y, u xc + ⟪p, y - xc⟫ ≤ u y :=
    hspec.2.1
  have hfcompact : ∀ R : ℝ, IsCompact {p | f p ≤ R} := hspec.2.2
  have hfeq :
      f = fun p => FunctionalInequalities.Analysis.truncatedConjugate u M p - (⟪xc, p⟫ + (-u xc)) := by
    funext p
    dsimp only [f]
    rw [real_inner_comm p xc]
    ring
  have hfconv : ConvexOn ℝ univ f := by
    rw [hfeq]
    exact (FunctionalInequalities.Analysis.convexOn_truncatedConjugate_readable hu.continuous hM).sub
      (((innerₗ E xc).concaveOn convex_univ).add_const (-u xc))
  have hfcont : Continuous f :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hfconv)
  let A : Set E := interior K ∩
    {p | ∀ x ∈ closedBall (0 : E) M,
      FunctionalInequalities.Analysis.truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M}
  have hAopen : IsOpen A :=
    isOpen_interior.inter
      (FunctionalInequalities.Analysis.isOpen_setOf_truncatedConjugate_maximizer_lt_readable hu.continuous hM)
  have hzeroA : ∀ p, f p = 0 → p ∈ A := by
    intro p hp
    have hpsub := (hfzero p).mp hp
    refine ⟨hsubint xc p hpsub, ?_⟩
    intro x hx heq
    have hxxc :=
      FunctionalInequalities.Analysis.eq_of_truncatedConjugate_eq_of_subgradient hstrict hxc hpsub hx heq
    rw [hxxc]
    exact hxc
  obtain ⟨R, hR, hRA⟩ :=
    FunctionalInequalities.Analysis.t11f7_small_sublevel hfcont hfnonneg (hfcompact 1) hAopen hzeroA
  obtain ⟨a, b, ha, hab⟩ :=
    FunctionalInequalities.Analysis.exists_inverse_subgradient_volume_bounds_readable hu hconv hnorm hmap hρ rfl
      hK.isClosed hKc (Real.exp_pos (-D)) hρK M
  have hB :
      ∀ Q : Set E, IsCompact Q → Q ⊆ {p | f p < R} →
        ∃ a b, 0 < a ∧
          ∀ G : Set E, IsOpen G → closure G ⊆ Q →
            ENNReal.ofReal a * volume G ≤ volume (FunctionalInequalities.Analysis.subgradientImage f G) ∧
              volume (FunctionalInequalities.Analysis.subgradientImage f G) ≤ ENNReal.ofReal b * volume G := by
    intro Q _ hQR
    refine ⟨a, b, ha, ?_⟩
    intro G hG hGQ
    have hGA : G ⊆ A := by
      intro p hp
      have hpR : f p < R := hQR (hGQ (subset_closure hp))
      exact hRA (show f p ≤ R from hpR.le)
    have hGK : G ⊆ K := fun p hp => interior_subset (hGA hp).1
    have hmax :
        ∀ p ∈ G, ∀ x ∈ closedBall (0 : E) M,
          FunctionalInequalities.Analysis.truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M := by
      intro p hp
      exact (hGA hp).2
    have hinv :
        {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ⊆
          closedBall (0 : E) M := by
      rintro x ⟨p, hpG, hpx⟩
      obtain ⟨z, hz, heq⟩ := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu.continuous hM p).1
      have hzlt : ‖z‖ < M := hmax p hpG z hz heq
      have hpz : ∀ y, u z + ⟪p, y - z⟫ ≤ u y := by
        apply ((FunctionalInequalities.Analysis.truncatedConjugate_centered_spec_readable hconv hzlt).2.1 p).mp
        linarith [heq]
      have hxz : x = z := FunctionalInequalities.Analysis.t11f7_support_unique hstrict hpx hpz
      exact hxz.symm ▸ hz
    have hvol :
        volume (FunctionalInequalities.Analysis.subgradientImage f G) =
          volume {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
      rw [hfeq, FunctionalInequalities.Analysis.volume_subgradientImage_sub_inner_add_const]
      rw [FunctionalInequalities.Analysis.subgradientImage_truncatedConjugate_eq_readable hu.continuous hstrict hM hmax]
    rw [hvol]
    exact hab G hG hGK hinv
  have hp₀zero : f p₀ = 0 := (hfzero p₀).mpr hp₀
  have hp₀f : ∀ q, f p₀ + ⟪(0 : E), q - p₀⟫ ≤ f q := by
    intro q
    simpa only [hp₀zero, inner_zero_left, add_zero] using hfnonneg q
  refine ⟨p₀, hp₀, ?_⟩
  intro p hp
  have hpzero : f p = 0 := (hfzero p).mpr hp
  apply FunctionalInequalities.Analysis.eq_of_contact_of_sublevel_bounds_readable hfconv hp₀f (hfcompact R) hB
  · simpa only [hpzero] using hR
  · simp only [hpzero, hp₀zero, inner_zero_left, add_zero]
