-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_8_7
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:45:47.205207+00:00
-- url     : https://prove2.me/submissions/19018634-968e-4484-83d5-3a0d3e3bfed8

import Definitions.Def_GL2QFT_Supplement_Wreath

noncomputable section

open Classical
open scoped Matrix ComplexConjugate
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.Wreath OddOrder.Isaacs.Ch03

namespace GL2QFT.Supplement.Thm87Helpers

/-! ### Section 1: Basic matrix representation facts, Maschke, and Schur's lemma -/

lemma isUnitaryRep_mul_conjTranspose {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g * (R g)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hR.2 g)

lemma isUnitaryRep_conjTranspose_mul {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    (R g)ᴴ * R g = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hR.2 g)

lemma isUnitaryRep_inv_eq_conjTranspose {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g⁻¹ = (R g)ᴴ := by
  have h1 : R g * R g⁻¹ = 1 := by rw [← hR.1.2, mul_inv_cancel, hR.1.1]
  have h2 : (R g)ᴴ * R g = 1 := isUnitaryRep_conjTranspose_mul hR g
  calc R g⁻¹ = 1 * R g⁻¹ := (Matrix.one_mul _).symm
    _ = ((R g)ᴴ * R g) * R g⁻¹ := by rw [h2]
    _ = (R g)ᴴ * (R g * R g⁻¹) := Matrix.mul_assoc _ _ _
    _ = (R g)ᴴ := by rw [h1, Matrix.mul_one]

lemma isMatRep_mul_inv {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsMatRep R) (g : G) :
    R g * R g⁻¹ = 1 := by
  rw [← hR.2, mul_inv_cancel, hR.1]

lemma isMatRep_inv_mul {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsMatRep R) (g : G) :
    R g⁻¹ * R g = 1 := by
  rw [← hR.2, inv_mul_cancel, hR.1]

lemma repEquiv_refl {G ι : Type} [Fintype ι] [DecidableEq ι]
    (R : G → Matrix ι ι ℂ) : RepEquiv R R := by
  refine ⟨1, 1, Matrix.one_mul _, Matrix.one_mul _, fun g _ => ?_⟩
  rw [Matrix.one_mul, Matrix.mul_one]

lemma repEquiv_symm {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h : RepEquiv R₁ R₂) : RepEquiv R₂ R₁ := by
  obtain ⟨A, B, hAB, hBA, hinter⟩ := h
  refine ⟨B, A, hBA, hAB, fun g hg => ?_⟩
  calc B * R₂ g = B * R₂ g * (A * B) := by rw [hAB, Matrix.mul_one]
    _ = B * (R₂ g * A) * B := by simp only [Matrix.mul_assoc]
    _ = B * (A * R₁ g) * B := by rw [hinter g hg]
    _ = (B * A) * R₁ g * B := by simp only [Matrix.mul_assoc]
    _ = R₁ g * B := by rw [hBA, Matrix.one_mul]

lemma repEquiv_trans {G ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ} {R₃ : G → Matrix ι₃ ι₃ ℂ}
    (h12 : RepEquiv R₁ R₂) (h23 : RepEquiv R₂ R₃) : RepEquiv R₁ R₃ := by
  obtain ⟨A₁, B₁, hAB₁, hBA₁, hi₁⟩ := h12
  obtain ⟨A₂, B₂, hAB₂, hBA₂, hi₂⟩ := h23
  refine ⟨A₂ * A₁, B₁ * B₂, ?_, ?_, fun g hg => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₁, hAB₁, Matrix.one_mul, hAB₂]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc B₂, hBA₂, Matrix.one_mul, hBA₁]
  · rw [Matrix.mul_assoc, hi₁ g hg, ← Matrix.mul_assoc, hi₂ g hg, Matrix.mul_assoc]

lemma repEquiv_trace_eq {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h : RepEquiv R₁ R₂) (g : G) :
    Matrix.trace (R₁ g) = Matrix.trace (R₂ g) := by
  obtain ⟨A, B, hAB, hBA, hi⟩ := h
  have h1 : R₁ g = B * (R₂ g * A) := by
    calc R₁ g = (B * A) * R₁ g := by rw [hBA, Matrix.one_mul]
      _ = B * (A * R₁ g) := Matrix.mul_assoc _ _ _
      _ = B * (R₂ g * A) := by rw [hi g (Set.mem_univ _)]
  rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc, hAB, Matrix.mul_one]

lemma repEquiv_card_eq {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h : RepEquiv R₁ R₂) : Fintype.card ι₁ = Fintype.card ι₂ := by
  obtain ⟨A, B, hAB, hBA, _⟩ := h
  have hc : ((Fintype.card ι₁ : ℕ) : ℂ) = ((Fintype.card ι₂ : ℕ) : ℂ) := by
    calc ((Fintype.card ι₁ : ℕ) : ℂ)
        = (1 : Matrix ι₁ ι₁ ℂ).trace := by simp [Matrix.trace]
      _ = (B * A).trace := by rw [hBA]
      _ = (A * B).trace := Matrix.trace_mul_comm B A
      _ = (1 : Matrix ι₂ ι₂ ℂ).trace := by rw [hAB]
      _ = ((Fintype.card ι₂ : ℕ) : ℂ) := by simp [Matrix.trace]
  exact Nat.cast_injective hc

lemma ker_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₁ (LinearMap.ker A.mulVecLin) := by
  intro g v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← hA g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

lemma range_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₂ (LinearMap.range A.mulVecLin) := by
  intro g w hw
  rcases hw with ⟨v, rfl⟩
  refine ⟨R₁ g *ᵥ v, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hA g]

lemma mulVecLin_eq_zero_iff {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : Matrix ι₂ ι₁ ℂ) : (∀ v, A *ᵥ v = 0) ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have := congr_fun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  · intro h v
    subst h
    simp

lemma schur_zero_of_not_repEquiv {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (hi1 : IsIrreducibleRep R₁) (hi2 : IsIrreducibleRep R₂)
    (hne : ¬ RepEquiv R₁ R₂) {A : Matrix ι₂ ι₁ ℂ}
    (hA : ∀ g : G, A * R₁ g = R₂ g * A) : A = 0 := by
  have hA' : ∀ g : G, R₂ g * A = A * R₁ g := fun g => (hA g).symm
  by_contra hAne
  have hker_ne : LinearMap.ker A.mulVecLin ≠ ⊤ := by
    intro htop
    apply hAne
    rw [← mulVecLin_eq_zero_iff]
    intro v
    have hv : v ∈ LinearMap.ker A.mulVecLin := htop.symm ▸ Submodule.mem_top
    simpa [Matrix.mulVecLin_apply] using hv
  have hker : LinearMap.ker A.mulVecLin = ⊥ :=
    (hi1.2 _ (ker_invariant hA')).resolve_right hker_ne
  have hinj : Function.Injective A.mulVecLin := LinearMap.ker_eq_bot.mp hker
  have hrange_ne : LinearMap.range A.mulVecLin ≠ ⊥ := by
    intro hbot
    apply hAne
    rw [← mulVecLin_eq_zero_iff]
    intro v
    have hv : A.mulVecLin v ∈ (⊥ : Submodule ℂ (ι₂ → ℂ)) := hbot ▸ LinearMap.mem_range_self _ v
    simpa [Matrix.mulVecLin_apply] using hv
  have hrange : LinearMap.range A.mulVecLin = ⊤ :=
    (hi2.2 _ (range_invariant hA')).resolve_left hrange_ne
  have hsurj : Function.Surjective A.mulVecLin := LinearMap.range_eq_top.mp hrange
  let e : (ι₁ → ℂ) ≃ₗ[ℂ] (ι₂ → ℂ) := LinearEquiv.ofBijective A.mulVecLin ⟨hinj, hsurj⟩
  let B : Matrix ι₁ ι₂ ℂ := LinearMap.toMatrix' e.symm.toLinearMap
  have hA_eq : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
  have hc : A.mulVecLin.comp e.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun v => by
      change e (e.symm v) = v
      exact e.apply_symm_apply v
  have hAB : A * B = 1 := by
    rw [← hA_eq, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id]
  have hc' : e.symm.toLinearMap.comp A.mulVecLin = LinearMap.id :=
    LinearMap.ext fun v => by
      change e.symm (e v) = v
      exact e.symm_apply_apply v
  have hBA : B * A = 1 := by
    rw [← hA_eq, ← LinearMap.toMatrix'_comp, hc', LinearMap.toMatrix'_id]
  exact hne ⟨A, B, hAB, hBA, fun g _ => hA g⟩

lemma schur_eq_smul_one {G ι : Type} [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hi : IsIrreducibleRep R)
    {A : Matrix ι ι ℂ} (hA : ∀ g : G, R g * A = A * R g) :
    ∃ c : ℂ, A = c • (1 : Matrix ι ι ℂ) := by
  have : Nonempty ι := hi.1
  have : Nontrivial (ι → ℂ) := Function.nontrivial
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A.mulVecLin
  have hker_ne : LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin ≠ ⊥ := by
    rw [Module.End.hasEigenvalue_iff] at hc
    intro hbot
    apply hc
    rw [Submodule.eq_bot_iff] at hbot ⊢
    intro v hv
    apply hbot
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
    exact hv
  have hA' : ∀ g : G, R g * (A - c • (1 : Matrix ι ι ℂ)) =
      (A - c • (1 : Matrix ι ι ℂ)) * R g := by
    intro g
    simp [mul_sub, sub_mul, hA g]
  have hker_top : LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin = ⊤ :=
    (hi.2 _ (ker_invariant hA')).resolve_left hker_ne
  refine ⟨c, ?_⟩
  rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
  intro v
  have hv : v ∈ LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin :=
    hker_top.symm ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  exact hv

def repIP {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (u v : ι → ℂ) : ℂ :=
  ∑ g : G, ∑ i : ι, star ((ρ g *ᵥ u) i) * (ρ g *ᵥ v) i

lemma repIP_add_left {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (u₁ u₂ v : ι → ℂ) :
    repIP ρ (u₁ + u₂) v = repIP ρ u₁ v + repIP ρ u₂ v := by
  simp only [repIP, Matrix.mulVec_add, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

lemma repIP_smul_left {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (c : ℂ) (u v : ι → ℂ) :
    repIP ρ (c • u) v = star c * repIP ρ u v := by
  simp only [repIP, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => ?_
  ring

lemma repIP_add_right {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (u v₁ v₂ : ι → ℂ) :
    repIP ρ u (v₁ + v₂) = repIP ρ u v₁ + repIP ρ u v₂ := by
  simp only [repIP, Matrix.mulVec_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma repIP_smul_right {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (c : ℂ) (u v : ι → ℂ) :
    repIP ρ u (c • v) = c * repIP ρ u v := by
  simp only [repIP, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => ?_
  ring

lemma repIP_self_eq_zero {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) (u : ι → ℂ)
    (hu : repIP ρ u u = 0) : u = 0 := by
  have hre : (repIP ρ u u).re = 0 := by rw [hu]; simp
  have hsum : ∑ g : G, ∑ i : ι,
      (((ρ g *ᵥ u) i).re * ((ρ g *ᵥ u) i).re + ((ρ g *ᵥ u) i).im * ((ρ g *ᵥ u) i).im) = 0 := by
    simpa [repIP, Complex.star_def, Complex.mul_re] using hre
  have hnn : ∀ g ∈ (Finset.univ : Finset G),
      0 ≤ ∑ i : ι, (((ρ g *ᵥ u) i).re * ((ρ g *ᵥ u) i).re +
        ((ρ g *ᵥ u) i).im * ((ρ g *ᵥ u) i).im) := fun g _ =>
    Finset.sum_nonneg fun i _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have h1 : ∑ i : ι, (((ρ 1 *ᵥ u) i).re * ((ρ 1 *ᵥ u) i).re +
      ((ρ 1 *ᵥ u) i).im * ((ρ 1 *ᵥ u) i).im) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum 1 (Finset.mem_univ 1)
  rw [hρ.1, Matrix.one_mulVec] at h1
  have hnni : ∀ i ∈ (Finset.univ : Finset ι),
      0 ≤ ((u i).re * (u i).re + (u i).im * (u i).im) := fun i _ =>
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  ext i
  simp only [Pi.zero_apply]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnni).mp h1 i (Finset.mem_univ i)
  have hre0 : (u i).re = 0 := by nlinarith
  have him0 : (u i).im = 0 := by nlinarith
  exact Complex.ext hre0 him0

lemma repIP_mulVec {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) (h : G) (u v : ι → ℂ) :
    repIP ρ (ρ h *ᵥ u) (ρ h *ᵥ v) = repIP ρ u v := by
  simp only [repIP, Matrix.mulVec_mulVec, ← hρ.2]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => rfl

def repOrtho {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (S : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {v | ∀ s ∈ S, repIP ρ s v = 0}
  zero_mem' := fun s _ => by simp [repIP]
  add_mem' := fun {v₁ v₂} h₁ h₂ s hs => by
    rw [repIP_add_right, h₁ s hs, h₂ s hs, add_zero]
  smul_mem' := fun c {v} hv s hs => by
    rw [repIP_smul_right, hv s hs, mul_zero]

lemma repOrtho_invariant {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {S : Submodule ℂ (ι → ℂ)}
    (hS : IsInvariantSubspace ρ S) : IsInvariantSubspace ρ (repOrtho ρ S) := by
  intro g v hv s hs
  have hs' : ρ g⁻¹ *ᵥ s ∈ S := hS g⁻¹ s hs
  have h1 : repIP ρ s (ρ g *ᵥ v) = repIP ρ (ρ g *ᵥ (ρ g⁻¹ *ᵥ s)) (ρ g *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, isMatRep_mul_inv hρ g, Matrix.one_mulVec]
  rw [h1, repIP_mulVec hρ g]
  exact hv _ hs'

lemma repOrtho_isCompl {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) (S : Submodule ℂ (ι → ℂ)) :
    IsCompl S (repOrtho ρ S) := by
  have hdisj : S ⊓ repOrtho ρ S = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v ⟨hvS, hvO⟩
    exact repIP_self_eq_zero hρ v (hvO v hvS)
  let k := Module.finrank ℂ S
  let b : Module.Basis (Fin k) ℂ S := Module.finBasisOfFinrankEq ℂ S rfl
  let T : (ι → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun v i => repIP ρ (b i : ι → ℂ) v
      map_add' := fun v₁ v₂ => by ext i; exact repIP_add_right ρ _ v₁ v₂
      map_smul' := fun c v => by ext i; exact repIP_smul_right ρ c _ v }
  have hker : LinearMap.ker T = repOrtho ρ S := by
    ext v
    simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply]
    constructor
    · intro hv s hs
      have hs_eq : s = ∑ i : Fin k, b.repr ⟨s, hs⟩ i • (b i : ι → ℂ) := by
        calc s = ((⟨s, hs⟩ : S) : ι → ℂ) := rfl
          _ = ((∑ i : Fin k, b.repr ⟨s, hs⟩ i • b i : S) : ι → ℂ) := by
                rw [b.sum_repr ⟨s, hs⟩]
          _ = ∑ i : Fin k, b.repr ⟨s, hs⟩ i • (b i : ι → ℂ) := by
                simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
      rw [hs_eq]
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty => simp [repIP]
      | @insert i t hi ih =>
        have hvi : repIP ρ (b i : ι → ℂ) v = 0 := hv i
        rw [Finset.sum_insert hi, repIP_add_left, repIP_smul_left, hvi, mul_zero, zero_add]
        exact ih
    · intro hv i
      exact hv (b i : ι → ℂ) (b i).2
  have : FiniteDimensional ℂ (ι → ℂ) := inferInstance
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [hker] at hrn
  have hrange_le : Module.finrank ℂ (LinearMap.range T) ≤ k := by
    calc Module.finrank ℂ (LinearMap.range T)
        ≤ Module.finrank ℂ (Fin k → ℂ) := Submodule.finrank_le _
      _ = k := Module.finrank_fin_fun ℂ
  have hsup_ge : Module.finrank ℂ (ι → ℂ) ≤ Module.finrank ℂ ↥(S ⊔ repOrtho ρ S) := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (repOrtho ρ S)
    have hbot0 : Module.finrank ℂ (⊥ : Submodule ℂ (ι → ℂ)) = 0 := finrank_bot ℂ (ι → ℂ)
    rw [hdisj, hbot0, add_zero] at hsum
    have hk : Module.finrank ℂ S = k := rfl
    omega
  have hsup : S ⊔ repOrtho ρ S = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le _) hsup_ge
  exact ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩

lemma linearProj_invariant_eq {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {S : Submodule ℂ (ι → ℂ)}
    (hS : IsInvariantSubspace ρ S) (g : G) (v : ι → ℂ) :
    let hcompl := repOrtho_isCompl hρ S
    let π := Submodule.projectionOnto S (repOrtho ρ S) hcompl
    (π (ρ g *ᵥ v) : ι → ℂ) = ρ g *ᵥ (π v : ι → ℂ) := by
  intro hcompl π
  have hmem : v ∈ S ⊔ repOrtho ρ S := hcompl.codisjoint.eq_top ▸ Submodule.mem_top
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hmem
  have hπv : π (s + t) = ⟨s, hs⟩ := by
    rw [map_add, Submodule.projectionOnto_apply_left hcompl ⟨s, hs⟩,
      Submodule.projectionOnto_apply_right hcompl ⟨t, ht⟩, add_zero]
  have hgs : ρ g *ᵥ s ∈ S := hS g s hs
  have hgt : ρ g *ᵥ t ∈ repOrtho ρ S := repOrtho_invariant hρ hS g t ht
  have hπgv : π (ρ g *ᵥ (s + t)) = ⟨ρ g *ᵥ s, hgs⟩ := by
    rw [Matrix.mulVec_add, map_add, Submodule.projectionOnto_apply_left hcompl ⟨ρ g *ᵥ s, hgs⟩,
      Submodule.projectionOnto_apply_right hcompl ⟨ρ g *ᵥ t, hgt⟩, add_zero]
  rw [hπgv, hπv]

lemma exists_invariant_proj {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {S : Submodule ℂ (ι → ℂ)}
    (hS : IsInvariantSubspace ρ S) :
    ∃ P : Matrix ι ι ℂ, P * P = P ∧ (∀ g : G, P * ρ g = ρ g * P) ∧
      (∀ v : ι → ℂ, P *ᵥ v ∈ S) ∧ (∀ v ∈ S, P *ᵥ v = v) := by
  let hcompl := repOrtho_isCompl hρ S
  let π := Submodule.projectionOnto S (repOrtho ρ S) hcompl
  let P_lin : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) := S.subtype.comp π
  let P : Matrix ι ι ℂ := LinearMap.toMatrix' P_lin
  have hP_apply : ∀ v, P *ᵥ v = (π v : ι → ℂ) := fun v => by
    change (Matrix.toLin' P) v = P_lin v
    rw [Matrix.toLin'_toMatrix']
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
    intro v
    simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    rw [hP_apply, hP_apply]
    have hvS : (π v : ι → ℂ) ∈ S := (π v).2
    rw [Submodule.projectionOnto_apply_left hcompl ⟨(π v : ι → ℂ), hvS⟩]
    simp
  · intro g
    rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
    intro v
    simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    rw [hP_apply, hP_apply, linearProj_invariant_eq hρ hS g v, sub_self]
  · intro v
    rw [hP_apply]
    exact (π v).2
  · intro v hv
    rw [hP_apply, Submodule.projectionOnto_apply_left hcompl ⟨v, hv⟩]

def subLin {G ι : Type} [Fintype ι] (ρ : G → Matrix ι ι ℂ)
    {U : Submodule ℂ (ι → ℂ)} (hU : IsInvariantSubspace ρ U) (g : G) : U →ₗ[ℂ] U where
  toFun u := ⟨ρ g *ᵥ u.1, hU g u.1 u.2⟩
  map_add' _ _ := Subtype.ext (Matrix.mulVec_add _ _ _)
  map_smul' _ _ := Subtype.ext (Matrix.mulVec_smul _ _ _)

def subRep {G ι : Type} [Fintype ι] (ρ : G → Matrix ι ι ℂ)
    {U : Submodule ℂ (ι → ℂ)} (hU : IsInvariantSubspace ρ U)
    {d : ℕ} (b : Module.Basis (Fin d) ℂ U) (g : G) : Matrix (Fin d) (Fin d) ℂ :=
  LinearMap.toMatrix b b (subLin ρ hU g)

lemma subRep_isMatRep {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {U : Submodule ℂ (ι → ℂ)}
    (hU : IsInvariantSubspace ρ U) {d : ℕ} (b : Module.Basis (Fin d) ℂ U) :
    IsMatRep (subRep ρ hU b) := by
  constructor
  · have h1 : subLin ρ hU 1 = LinearMap.id := by
      ext u i; simp [subLin, hρ.1]
    simp [subRep, h1]
  · intro x y
    have hm : subLin ρ hU (x * y) = (subLin ρ hU x).comp (subLin ρ hU y) := by
      ext u i; simp [subLin, hρ.2, Matrix.mulVec_mulVec]
    simp [subRep, hm, LinearMap.toMatrix_comp b b b]

lemma subRep_trace_eq {G ι : Type} [Fintype ι]
    {ρ : G → Matrix ι ι ℂ} {U : Submodule ℂ (ι → ℂ)}
    (hU : IsInvariantSubspace ρ U) {d : ℕ} (b : Module.Basis (Fin d) ℂ U) (g : G) :
    Matrix.trace (subRep ρ hU b g) = LinearMap.trace ℂ U (subLin ρ hU g) :=
  (LinearMap.trace_eq_matrix_trace ℂ b (subLin ρ hU g)).symm

lemma exists_min_invariant_subrep {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {W : Submodule ℂ (ι → ℂ)}
    (hWne : W ≠ ⊥) (hWinv : IsInvariantSubspace ρ W) :
    ∃ (d : ℕ) (U : Submodule ℂ (ι → ℂ)) (b : Module.Basis (Fin d) ℂ U)
      (hUinv : IsInvariantSubspace ρ U),
      U ≤ W ∧ U ≠ ⊥ ∧ IsMatRep (subRep ρ hUinv b) ∧ IsIrreducibleRep (subRep ρ hUinv b) := by
  let P : ℕ → Prop := fun d =>
    ∃ U : Submodule ℂ (ι → ℂ), U ≤ W ∧ U ≠ ⊥ ∧ IsInvariantSubspace ρ U ∧ Module.finrank ℂ U = d
  have hex : ∃ d, P d := ⟨Module.finrank ℂ W, W, le_rfl, hWne, hWinv, rfl⟩
  let d := Nat.find hex
  obtain ⟨U, hUW, hUne, hUinv, hUdim⟩ := Nat.find_spec hex
  have : FiniteDimensional ℂ (ι → ℂ) := inferInstance
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
  have hd_pos : 0 < d := by
    change 0 < Nat.find hex
    rw [← hUdim]
    exact Module.finrank_pos
  let b : Module.Basis (Fin d) ℂ U := Module.finBasisOfFinrankEq ℂ U hUdim
  let ρ_U := subRep ρ hUinv b
  have hρU_mat : IsMatRep ρ_U := subRep_isMatRep hρ hUinv b
  have hρU_irr : IsIrreducibleRep ρ_U := by
    refine ⟨⟨⟨0, hd_pos⟩⟩, fun V hV => ?_⟩
    let U' : Submodule ℂ U := V.map b.equivFun.symm.toLinearMap
    let U'' : Submodule ℂ (ι → ℂ) := U'.map U.subtype
    have hU''_le : U'' ≤ U := Submodule.map_subtype_le U U'
    have hU''_inv : IsInvariantSubspace ρ U'' := by
      intro x u hu
      rcases hu with ⟨u', ⟨v, hv, rfl⟩, rfl⟩
      have hLU : subLin ρ hUinv x (b.equivFun.symm v) = b.equivFun.symm (ρ_U x *ᵥ v) := by
        rw [← Matrix.toLin_toMatrix b b (subLin ρ hUinv x)]
        change Matrix.toLin b b (ρ_U x) (b.equivFun.symm v) = b.equivFun.symm (ρ_U x *ᵥ v)
        rw [Matrix.toLin_apply]
        have hrepr : (b.repr (b.equivFun.symm v) : Fin d → ℂ) = v := b.equivFun.apply_symm_apply v
        rw [hrepr, b.equivFun_symm_apply]
      refine ⟨subLin ρ hUinv x (b.equivFun.symm v), ⟨ρ_U x *ᵥ v, hV x v hv, hLU.symm⟩, rfl⟩
    by_cases hbot : U'' = ⊥
    · left
      have hU'_bot : U' = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        have : (x : ι → ℂ) ∈ U'' := ⟨x, hx, rfl⟩
        rw [hbot] at this
        exact Subtype.ext this
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hmem : b.equivFun.symm v ∈ U' := ⟨v, hv, rfl⟩
      rw [hU'_bot, Submodule.mem_bot] at hmem
      have hv0 := congrArg b.equivFun hmem
      rw [b.equivFun.apply_symm_apply, map_zero] at hv0
      exact hv0
    · right
      have hle_d : d ≤ Module.finrank ℂ U'' := Nat.find_min' hex
        ⟨U'', hU''_le.trans hUW, hbot, hU''_inv, rfl⟩
      have hge_d : Module.finrank ℂ U'' ≤ d := by
        change Module.finrank ℂ U'' ≤ Nat.find hex
        rw [← hUdim]
        exact Submodule.finrank_mono hU''_le
      have hU''_eq : U'' = U := Submodule.eq_of_le_of_finrank_eq hU''_le (by omega)
      have hU'_top : U' = ⊤ := by
        rw [eq_top_iff]
        intro u _
        have hu : (u : ι → ℂ) ∈ U'' := hU''_eq.symm ▸ u.2
        rcases hu with ⟨w, hw, hwu⟩
        have : w = u := Subtype.ext hwu
        subst this
        exact hw
      rw [eq_top_iff]
      intro v _
      have hv : b.equivFun.symm v ∈ U' := hU'_top.symm ▸ Submodule.mem_top
      rcases hv with ⟨w, hw, hvw⟩
      have hv0 := congrArg b.equivFun hvw
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hv0
      rw [← hv0]
      exact hw
  exact ⟨d, U, b, hUinv, hUW, hUne, hρU_mat, hρU_irr⟩

lemma kronecker_one_one {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂] :
    Matrix.kronecker (1 : Matrix ι₁ ι₁ ℂ) (1 : Matrix ι₂ ι₂ ℂ) = 1 := by
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  by_cases h1 : a₁ = b₁ <;> by_cases h2 : a₂ = b₂ <;> simp [Matrix.one_apply, Prod.ext_iff, h1, h2]

lemma kronecker_conjTranspose {ι₁ ι₂ : Type} (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) :
    (Matrix.kronecker A B)ᴴ = Matrix.kronecker Aᴴ Bᴴ := by
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  simp [Matrix.conjTranspose_apply]

lemma isMatRep_kronecker {G ι₁ ι₂ : Type} [Monoid G] [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h₁ : IsMatRep R₁) (h₂ : IsMatRep R₂) :
    IsMatRep (fun g => Matrix.kronecker (R₁ g) (R₂ g)) := by
  constructor
  · simp [h₁.1, h₂.1]
  · intro g h
    simp [h₁.2, h₂.2, Matrix.mul_kronecker_mul]

lemma isUnitaryRep_kronecker {G ι₁ ι₂ : Type} [Monoid G] [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h₁ : IsUnitaryRep R₁) (h₂ : IsUnitaryRep R₂) :
    IsUnitaryRep (fun g => Matrix.kronecker (R₁ g) (R₂ g)) := by
  refine ⟨isMatRep_kronecker h₁.1 h₂.1, fun g => ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  dsimp only
  calc Matrix.kronecker (R₁ g) (R₂ g) * (Matrix.kronecker (R₁ g) (R₂ g))ᴴ
      = Matrix.kronecker (R₁ g) (R₂ g) * Matrix.kronecker (R₁ g)ᴴ (R₂ g)ᴴ := by
          rw [kronecker_conjTranspose]
    _ = Matrix.kronecker (R₁ g * (R₁ g)ᴴ) (R₂ g * (R₂ g)ᴴ) :=
          (Matrix.mul_kronecker_mul (R₁ g) (R₁ g)ᴴ (R₂ g) (R₂ g)ᴴ).symm
    _ = 1 := by
          rw [isUnitaryRep_mul_conjTranspose h₁ g, isUnitaryRep_mul_conjTranspose h₂ g,
            kronecker_one_one]

lemma trace_kronecker {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) :
    Matrix.trace (Matrix.kronecker A B) = Matrix.trace A * Matrix.trace B := by
  change ∑ p : ι₁ × ι₂, Matrix.kronecker A B p p = (∑ i, A i i) * (∑ j, B j j)
  rw [Fintype.sum_prod_type]
  have hent : ∀ i j, Matrix.kronecker A B (i, j) (i, j) = A i i * B j j := fun _ _ => rfl
  simp_rw [hent, ← Finset.mul_sum, ← Finset.sum_mul]

/-! ### Section 2: Character inner product, Schur orthogonality, Burnside dimension sum -/

def charInner {G ι₁ ι₂ : Type} [Group G] [Fintype G] [Fintype ι₁] [Fintype ι₂]
    (R₂ : G → Matrix ι₂ ι₂ ℂ) (R₁ : G → Matrix ι₁ ι₁ ℂ) : ℂ :=
  ((Fintype.card G : ℂ))⁻¹ * ∑ g : G, Matrix.trace (R₂ g) * Matrix.trace (R₁ g⁻¹)

def homSpace {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (R₁ : G → Matrix ι₁ ι₁ ℂ) (R₂ : G → Matrix ι₂ ι₂ ℂ) : Submodule ℂ (Matrix ι₂ ι₁ ℂ) where
  carrier := {A | ∀ g : G, R₂ g * A = A * R₁ g}
  zero_mem' := fun g => by simp
  add_mem' := fun {A B} hA hB g => by rw [Matrix.mul_add, Matrix.add_mul, hA g, hB g]
  smul_mem' := fun c {A} hA g => by simp [Matrix.mul_smul, Matrix.smul_mul, hA g]

def avgOp {G ι₁ ι₂ : Type} [Group G] [Fintype G] [Fintype ι₁] [Fintype ι₂]
    (R₂ : G → Matrix ι₂ ι₂ ℂ) (R₁ : G → Matrix ι₁ ι₁ ℂ) :
    Matrix ι₂ ι₁ ℂ →ₗ[ℂ] Matrix ι₂ ι₁ ℂ where
  toFun M := ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, R₂ g * M * R₁ g⁻¹
  map_add' M₁ M₂ := by simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c M := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
    exact smul_comm _ _ _

lemma avgOp_intertwines {G ι₁ ι₂ : Type} [Group G] [Fintype G] [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h₁ : IsMatRep R₁) (h₂ : IsMatRep R₂) (M : Matrix ι₂ ι₁ ℂ) (h : G) :
    R₂ h * avgOp R₂ R₁ M = avgOp R₂ R₁ M * R₁ h := by
  have hstep : R₂ h * avgOp R₂ R₁ M * R₁ h⁻¹ = avgOp R₂ R₁ M := by
    simp only [avgOp, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp [h₂.2, h₁.2, mul_inv_rev, Matrix.mul_assoc]
  calc R₂ h * avgOp R₂ R₁ M
      = (R₂ h * avgOp R₂ R₁ M) * (R₁ h⁻¹ * R₁ h) := by rw [isMatRep_inv_mul h₁ h, Matrix.mul_one]
    _ = (R₂ h * avgOp R₂ R₁ M * R₁ h⁻¹) * R₁ h := by simp only [Matrix.mul_assoc]
    _ = avgOp R₂ R₁ M * R₁ h := by rw [hstep]

lemma avgOp_of_mem_homSpace {G ι₁ ι₂ : Type} [Group G] [Fintype G] [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h₁ : IsMatRep R₁) {M : Matrix ι₂ ι₁ ℂ} (hM : M ∈ homSpace R₁ R₂) :
    avgOp R₂ R₁ M = M := by
  have : Nonempty G := ⟨1⟩
  have hcard_ne : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [avgOp, LinearMap.coe_mk, AddHom.coe_mk]
  have hterm : ∀ g : G, R₂ g * M * R₁ g⁻¹ = M := fun g => by
    rw [hM g, Matrix.mul_assoc, isMatRep_mul_inv h₁ g, Matrix.mul_one]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard_ne, one_smul]

lemma avgOp_comp_avgOp {G ι₁ ι₂ : Type} [Group G] [Fintype G] [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h₁ : IsMatRep R₁) (h₂ : IsMatRep R₂) (M : Matrix ι₂ ι₁ ℂ) :
    avgOp R₂ R₁ (avgOp R₂ R₁ M) = avgOp R₂ R₁ M :=
  avgOp_of_mem_homSpace h₁ (avgOp_intertwines h₁ h₂ M)

lemma range_avgOp_eq_homSpace {G ι₁ ι₂ : Type} [Group G] [Fintype G] [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h₁ : IsMatRep R₁) (h₂ : IsMatRep R₂) :
    LinearMap.range (avgOp R₂ R₁) = homSpace R₁ R₂ := by
  ext A
  constructor
  · rintro ⟨M, rfl⟩
    exact avgOp_intertwines h₁ h₂ M
  · intro hA
    exact ⟨A, avgOp_of_mem_homSpace h₁ hA⟩

lemma trace_avgOp {G ι₁ ι₂ : Type} [Group G] [Fintype G] [Fintype ι₁] [Fintype ι₂]
    (R₂ : G → Matrix ι₂ ι₂ ℂ) (R₁ : G → Matrix ι₁ ι₁ ℂ) :
    LinearMap.trace ℂ (Matrix ι₂ ι₁ ℂ) (avgOp R₂ R₁) = charInner R₂ R₁ := by
  let e : Matrix ι₂ ι₁ ℂ ≃ₗ[ℂ] (ι₂ × ι₁ → ℂ) :=
    { toFun := fun M p => M p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => Matrix.of fun i j => f (i, j)
      left_inv := fun M => by ext i j; rfl
      right_inv := fun f => by ext ⟨i, j⟩; rfl }
  let b : Module.Basis (ι₂ × ι₁) ℂ (Matrix ι₂ ι₁ ℂ) := (Pi.basisFun ℂ (ι₂ × ι₁)).map e.symm
  rw [LinearMap.trace_eq_matrix_trace ℂ b (avgOp R₂ R₁)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  have hrepr : ∀ M (p : ι₂ × ι₁), b.repr M p = M p.1 p.2 := fun M p => by
    dsimp [b]
    rw [Module.Basis.map_repr]
    rfl
  have hb : ∀ (i : ι₂) (j : ι₁) (a : ι₂) (c : ι₁),
      b (i, j) a c = if a = i ∧ c = j then 1 else 0 := fun i j a c => by
    dsimp [b, e]
    simp [Pi.basisFun_apply, Pi.single_apply, Prod.ext_iff]
  simp_rw [hrepr, Fintype.sum_prod_type]
  have hentry : ∀ g i j, (R₂ g * b (i, j) * R₁ g⁻¹) i j = R₂ g i i * R₁ g⁻¹ j j := by
    intro g i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, hb]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [hk]
      · intro hi; exact (hi (Finset.mem_univ i)).elim
    · intro l _ hl
      have hz : ∑ k : ι₂, R₂ g i k * (if k = i ∧ l = j then (1 : ℂ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [hl]
      rw [hz, zero_mul]
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  calc ∑ i : ι₂, ∑ j : ι₁, (avgOp R₂ R₁ (b (i, j))) i j
      = ∑ i : ι₂, ∑ j : ι₁, ((Fintype.card G : ℂ))⁻¹ *
          ∑ g : G, (R₂ g * b (i, j) * R₁ g⁻¹) i j := by
          simp only [avgOp, LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply, smul_eq_mul,
            Matrix.sum_apply]
    _ = ∑ i : ι₂, ∑ j : ι₁, ((Fintype.card G : ℂ))⁻¹ *
          ∑ g : G, R₂ g i i * R₁ g⁻¹ j j := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          congr 1
          exact Finset.sum_congr rfl fun g _ => hentry g i j
    _ = ((Fintype.card G : ℂ))⁻¹ *
          ∑ g : G, (∑ i : ι₂, R₂ g i i) * (∑ j : ι₁, R₁ g⁻¹ j j) := by
          simp_rw [← Finset.mul_sum]
          congr 1
          have hswap1 : ∀ i : ι₂, ∑ j : ι₁, ∑ g : G, R₂ g i i * R₁ g⁻¹ j j =
              ∑ g : G, ∑ j : ι₁, R₂ g i i * R₁ g⁻¹ j j := fun _ => Finset.sum_comm
          simp_rw [hswap1]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
    _ = charInner R₂ R₁ := rfl

lemma trace_idem_eq_finrank_range {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hT : ∀ v, T (T v) = T v) :
    LinearMap.trace ℂ V T = (Module.finrank ℂ (LinearMap.range T) : ℂ) := by
  let R := LinearMap.range T
  let K := LinearMap.ker T
  let e : (R × K) ≃ₗ[ℂ] V :=
    { toFun := fun rk => rk.1.1 + rk.2.1
      map_add' := fun a b => by simp only [Prod.fst_add, Submodule.coe_add, Prod.snd_add]; abel
      map_smul' := fun c a => by simp only [Prod.smul_fst, SetLike.val_smul, Prod.smul_snd,
        RingHom.id_apply, smul_add]
      invFun := fun v => ⟨⟨T v, LinearMap.mem_range_self T v⟩,
        ⟨v - T v, by rw [LinearMap.mem_ker, map_sub, hT v, sub_self]⟩⟩
      left_inv := fun ⟨⟨r, hr⟩, ⟨k, hk⟩⟩ => by
        rcases hr with ⟨w, rfl⟩
        change T k = 0 at hk
        have hTrk : T (T w + k) = T w := by rw [map_add, hT w, hk, add_zero]
        ext <;> simp [hTrk]
      right_inv := fun v => add_sub_cancel _ _ }
  let d₁ := Module.finrank ℂ R
  let d₂ := Module.finrank ℂ K
  let bR : Module.Basis (Fin d₁) ℂ R := Module.finBasisOfFinrankEq ℂ R rfl
  let bK : Module.Basis (Fin d₂) ℂ K := Module.finBasisOfFinrankEq ℂ K rfl
  let bRK : Module.Basis (Fin d₁ ⊕ Fin d₂) ℂ (R × K) := bR.prod bK
  let b : Module.Basis (Fin d₁ ⊕ Fin d₂) ℂ V := bRK.map e
  rw [LinearMap.trace_eq_matrix_trace ℂ b T]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, LinearMap.toMatrix_apply]
  have hinl : ∀ i : Fin d₁, b.repr (T (b (Sum.inl i))) (Sum.inl i) = 1 := fun i => by
    have hbi : b (Sum.inl i) = (bR i : V) := by simp [b, bRK, e]
    have hTbi : T (bR i : V) = (bR i : V) := by
      rcases (bR i).2 with ⟨w, hw⟩
      rw [← hw, hT w]
    rw [hbi, hTbi, ← hbi, b.repr_self, Finsupp.single_eq_same]
  have hinr : ∀ j : Fin d₂, b.repr (T (b (Sum.inr j))) (Sum.inr j) = 0 := fun j => by
    have hbj : b (Sum.inr j) = (bK j : V) := by simp [b, bRK, e]
    have hTbj : T (bK j : V) = 0 := (bK j).2
    rw [hbj, hTbj, map_zero, Finsupp.zero_apply]
  simp_rw [hinl, hinr]
  simp [d₁, R]

lemma charInner_eq_finrank_homSpace {G ι₁ ι₂ : Type} [Group G] [Fintype G]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h₁ : IsMatRep R₁) (h₂ : IsMatRep R₂) :
    charInner R₂ R₁ = (Module.finrank ℂ (homSpace R₁ R₂) : ℂ) := by
  rw [← trace_avgOp, trace_idem_eq_finrank_range _ (avgOp_comp_avgOp h₁ h₂),
    range_avgOp_eq_homSpace h₁ h₂]

lemma charInner_eq_zero_of_not_repEquiv {G ι₁ ι₂ : Type} [Group G] [Fintype G]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (hm₁ : IsMatRep R₁) (hm₂ : IsMatRep R₂)
    (hi₁ : IsIrreducibleRep R₁) (hi₂ : IsIrreducibleRep R₂)
    (hne : ¬ RepEquiv R₁ R₂) :
    charInner R₂ R₁ = 0 := by
  rw [charInner_eq_finrank_homSpace hm₁ hm₂]
  have hbot : homSpace R₁ R₂ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro A hA
    exact schur_zero_of_not_repEquiv hi₁ hi₂ hne (fun g => (hA g).symm)
  rw [hbot, finrank_bot, Nat.cast_zero]

lemma charInner_self_eq_one {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hm : IsMatRep R) (hi : IsIrreducibleRep R) :
    charInner R R = 1 := by
  rw [charInner_eq_finrank_homSpace hm hm]
  have : Nonempty ι := hi.1
  have h1ne : (1 : Matrix ι ι ℂ) ≠ 0 := by
    intro h0
    have := congr_fun (congr_fun h0 (Classical.arbitrary ι)) (Classical.arbitrary ι)
    simp at this
  have hspan : homSpace R R = Submodule.span ℂ {(1 : Matrix ι ι ℂ)} := by
    apply le_antisymm
    · intro A hA
      obtain ⟨c, rfl⟩ := schur_eq_smul_one hi hA
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      intro g
      simp
  rw [hspan, finrank_span_singleton h1ne, Nat.cast_one]

lemma isIrreducibleRep_of_charInner_self_eq_one {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hm : IsMatRep R) (hne : Nonempty ι)
    (hc : charInner R R = 1) :
    IsIrreducibleRep R := by
  refine ⟨hne, fun W hW => ?_⟩
  rw [charInner_eq_finrank_homSpace hm hm] at hc
  have hfin : Module.finrank ℂ (homSpace R R) = 1 := by exact_mod_cast hc
  have h1mem : (1 : Matrix ι ι ℂ) ∈ homSpace R R := fun g => by simp
  have h1ne : (1 : Matrix ι ι ℂ) ≠ 0 := by
    intro h0
    have := congr_fun (congr_fun h0 (Classical.arbitrary ι)) (Classical.arbitrary ι)
    simp at this
  have hspan : Submodule.span ℂ {(1 : Matrix ι ι ℂ)} = homSpace R R := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact h1mem
    · rw [finrank_span_singleton h1ne, hfin]
  obtain ⟨P, hPP, hPcomm, hPrange, hPfix⟩ := exists_invariant_proj hm hW
  have hPmem : P ∈ homSpace R R := fun g => (hPcomm g).symm
  rw [← hspan, Submodule.mem_span_singleton] at hPmem
  obtain ⟨c, rfl⟩ := hPmem
  have hcc : c ^ 2 = c := by
    have hsub : (c * c - c) • (1 : Matrix ι ι ℂ) = 0 := by
      have : (c • (1 : Matrix ι ι ℂ)) * (c • (1 : Matrix ι ι ℂ)) - c • (1 : Matrix ι ι ℂ) = 0 := by
        rw [hPP, sub_self]
      simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sub_smul] using this
    rcases smul_eq_zero.mp hsub with h | h
    · linear_combination h
    · exact (h1ne h).elim
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by linear_combination hcc
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hc01 with rfl | rfl
  · left
    rw [Submodule.eq_bot_iff]
    intro v hv
    have := hPfix v hv
    simpa using this.symm
  · right
    rw [eq_top_iff]
    intro v _
    have := hPrange v
    simpa using this

lemma repEquiv_iff_charInner_ne_zero {G ι₁ ι₂ : Type} [Group G] [Fintype G]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (hm₁ : IsMatRep R₁) (hm₂ : IsMatRep R₂)
    (hi₁ : IsIrreducibleRep R₁) (hi₂ : IsIrreducibleRep R₂) :
    RepEquiv R₁ R₂ ↔ charInner R₂ R₁ ≠ 0 := by
  constructor
  · intro h
    have htr : charInner R₂ R₁ = charInner R₁ R₁ := by
      simp only [charInner]
      congr 1
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [repEquiv_trace_eq (repEquiv_symm h) g]
    rw [htr, charInner_self_eq_one hm₁ hi₁]
    exact one_ne_zero
  · intro hne
    by_contra hnot
    exact hne (charInner_eq_zero_of_not_repEquiv hm₁ hm₂ hi₁ hi₂ hnot)

lemma schur_entry_ortho_ne {G ι₁ ι₂ : Type} [Group G] [Fintype G]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (hm₁ : IsMatRep R₁) (hm₂ : IsMatRep R₂)
    (hi₁ : IsIrreducibleRep R₁) (hi₂ : IsIrreducibleRep R₂)
    (hne : ¬ RepEquiv R₁ R₂) (i : ι₂) (j : ι₂) (k : ι₁) (l : ι₁) :
    ((Fintype.card G : ℂ))⁻¹ * ∑ g : G, R₂ g i j * R₁ g⁻¹ k l = 0 := by
  let M : Matrix ι₂ ι₁ ℂ := Matrix.of fun a b => if a = j ∧ b = k then 1 else 0
  have hzero : avgOp R₂ R₁ M = 0 :=
    schur_zero_of_not_repEquiv hi₁ hi₂ hne (fun g => (avgOp_intertwines hm₁ hm₂ M g).symm)
  have h0il := congr_fun (congr_fun hzero i) l
  have hentry : ∀ g : G, (R₂ g * M * R₁ g⁻¹) i l = R₂ g i j * R₁ g⁻¹ k l := fun g => by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single j]
      · simp [M]
      · intro a _ ha; simp [M, ha]
      · intro hj; exact (hj (Finset.mem_univ j)).elim
    · intro b _ hb
      have hz : ∑ a : ι₂, R₂ g i a * M a b = 0 := Finset.sum_eq_zero fun a _ => by simp [M, hb]
      rw [hz, zero_mul]
    · intro hk; exact (hk (Finset.mem_univ k)).elim
  simp only [avgOp, LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply, smul_eq_mul,
    Matrix.sum_apply, Matrix.zero_apply] at h0il
  simp_rw [hentry] at h0il
  exact h0il

lemma schur_entry_ortho_eq {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hm : IsMatRep R) (hi : IsIrreducibleRep R)
    (i j k l : ι) :
    ((Fintype.card G : ℂ))⁻¹ * ∑ g : G, R g i j * R g⁻¹ k l =
      if j = k ∧ i = l then ((Fintype.card ι : ℂ))⁻¹ else 0 := by
  let M : Matrix ι ι ℂ := Matrix.of fun a b => if a = j ∧ b = k then 1 else 0
  obtain ⟨c, hc⟩ := schur_eq_smul_one hi (avgOp_intertwines hm hm M)
  have hG_ne : (Fintype.card G : ℂ) ≠ 0 := by
    have : Nonempty G := ⟨1⟩
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : Nonempty ι := hi.1
  have hI_ne : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have htr : Matrix.trace (avgOp R R M) = Matrix.trace M := by
    simp only [avgOp, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_smul, Matrix.trace_sum,
      smul_eq_mul]
    have ht : ∀ g : G, Matrix.trace (R g * M * R g⁻¹) = Matrix.trace M := fun g => by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, isMatRep_inv_mul hm g, Matrix.one_mul]
    simp_rw [ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hG_ne, one_mul]
  have htrM : Matrix.trace M = if j = k then 1 else 0 := by
    simp only [Matrix.trace, Matrix.diag, M, Matrix.of_apply]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, Finset.sum_eq_single j]
      · simp
      · intro a _ ha; simp [ha]
      · intro hj; exact (hj (Finset.mem_univ j)).elim
    · rw [if_neg hjk]
      refine Finset.sum_eq_zero fun a _ => ?_
      split_ifs with h
      · exact (hjk (h.1.symm.trans h.2)).elim
      · rfl
  have htrc : Matrix.trace (c • (1 : Matrix ι ι ℂ)) = c * (Fintype.card ι : ℂ) := by
    simp [Matrix.trace, mul_comm]
  have hc_val : c = ((Fintype.card ι : ℂ))⁻¹ * (if j = k then 1 else 0) := by
    have heq := congrArg Matrix.trace hc
    rw [htr, htrM, htrc] at heq
    calc c = (c * (Fintype.card ι : ℂ)) * ((Fintype.card ι : ℂ))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI_ne, mul_one]
      _ = (if j = k then (1 : ℂ) else 0) * ((Fintype.card ι : ℂ))⁻¹ := by rw [← heq]
      _ = ((Fintype.card ι : ℂ))⁻¹ * (if j = k then 1 else 0) := mul_comm _ _
  have hcil := congr_fun (congr_fun hc i) l
  have hentry : ∀ g : G, (R g * M * R g⁻¹) i l = R g i j * R g⁻¹ k l := fun g => by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single j]
      · simp [M]
      · intro a _ ha; simp [M, ha]
      · intro hj; exact (hj (Finset.mem_univ j)).elim
    · intro b _ hb
      have hz : ∑ a : ι, R g i a * M a b = 0 := Finset.sum_eq_zero fun a _ => by simp [M, hb]
      rw [hz, zero_mul]
    · intro hk; exact (hk (Finset.mem_univ k)).elim
  simp only [avgOp, LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply, smul_eq_mul,
    Matrix.sum_apply, Matrix.one_apply] at hcil
  simp_rw [hentry] at hcil
  rw [hcil, hc_val]
  by_cases hjk : j = k <;> by_cases hil : i = l <;> simp [hjk, hil]

lemma bessel_card_le {G : Type} [Group G] [Fintype G]
    {Γ : Type} [Fintype Γ] (B : Γ → Type) [∀ k, Fintype (B k)] [∀ k, DecidableEq (B k)]
    (R : ∀ k, G → Matrix (B k) (B k) ℂ)
    (hm : ∀ k, IsMatRep (R k)) (hi : ∀ k, IsIrreducibleRep (R k))
    (hdiff : ∀ k₁ k₂, k₁ ≠ k₂ → ¬ RepEquiv (R k₁) (R k₂)) :
    ∑ k : Γ, Fintype.card (B k) ^ 2 ≤ Fintype.card G := by
  let v : (Σ k : Γ, B k × B k) → (G → ℂ) := fun p g => R p.1 g p.2.1 p.2.2
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc p₀
    rcases p₀ with ⟨k₀, i₀, j₀⟩
    have hsum : ∑ g : G, (∑ p : Σ k : Γ, B k × B k, c p * v p g) * R k₀ g⁻¹ j₀ i₀ = 0 := by
      refine Finset.sum_eq_zero fun g _ => ?_
      have hg : (∑ p : Σ k : Γ, B k × B k, c p • v p g) = 0 := by
        simpa using congr_fun hc g
      rw [show (∑ p : Σ k : Γ, B k × B k, c p * v p g) = 0 from by simpa [smul_eq_mul] using hg,
        zero_mul]
    rw [Finset.sum_congr rfl fun g _ => Finset.sum_mul _ _ _] at hsum
    rw [Finset.sum_comm] at hsum
    have hterm : ∀ p : Σ k : Γ, B k × B k,
        (∑ g : G, c p * v p g * R k₀ g⁻¹ j₀ i₀) =
          if p = ⟨k₀, i₀, j₀⟩ then c ⟨k₀, i₀, j₀⟩ *
            ((Fintype.card G : ℂ) * ((Fintype.card (B k₀) : ℂ))⁻¹) else 0 := by
      rintro ⟨k, i, j⟩
      have hG_ne : (Fintype.card G : ℂ) ≠ 0 := by
        have : Nonempty G := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hpull : (∑ g : G, c ⟨k, i, j⟩ * v ⟨k, i, j⟩ g * R k₀ g⁻¹ j₀ i₀) =
          c ⟨k, i, j⟩ * ((Fintype.card G : ℂ) *
            (((Fintype.card G : ℂ))⁻¹ * ∑ g : G, R k g i j * R k₀ g⁻¹ j₀ i₀)) := by
        simp_rw [mul_assoc, ← Finset.mul_sum, v, ← mul_assoc (Fintype.card G : ℂ),
          mul_inv_cancel₀ hG_ne, one_mul]
      rw [hpull]
      by_cases hk : k = k₀
      · subst hk
        rw [schur_entry_ortho_eq (hm k) (hi k) i j j₀ i₀]
        by_cases hij : j = j₀ ∧ i = i₀
        · have heq : (⟨k, i, j⟩ : Σ k : Γ, B k × B k) = ⟨k, i₀, j₀⟩ := by
            obtain ⟨rfl, rfl⟩ := hij; rfl
          simp [heq, hij, mul_assoc]
        · have hne : (⟨k, i, j⟩ : Σ k : Γ, B k × B k) ≠ ⟨k, i₀, j₀⟩ := by
            intro h
            apply hij
            have h' := Sigma.ext_iff.mp h
            have h'' : (i, j) = (i₀, j₀) := eq_of_heq h'.2
            exact ⟨(Prod.ext_iff.mp h'').2, (Prod.ext_iff.mp h'').1⟩
          simp [hne, hij]
      · rw [schur_entry_ortho_ne (hm k₀) (hm k) (hi k₀) (hi k)
            (fun h => hdiff k k₀ hk (repEquiv_symm h)) i j j₀ i₀]
        have hne : (⟨k, i, j⟩ : Σ k : Γ, B k × B k) ≠ ⟨k₀, i₀, j₀⟩ := fun h =>
          hk (congrArg Sigma.fst h)
        simp [hne]
    simp_rw [hterm] at hsum
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at hsum
    have : Nonempty G := ⟨1⟩
    have : Nonempty (B k₀) := (hi k₀).1
    have hG_ne : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hB_ne : (Fintype.card (B k₀) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hmul_ne : (Fintype.card G : ℂ) * ((Fintype.card (B k₀) : ℂ))⁻¹ ≠ 0 :=
      mul_ne_zero hG_ne (inv_ne_zero hB_ne)
    exact (mul_eq_zero.mp hsum).resolve_right hmul_ne
  have hle := hli.fintype_card_le_finrank
  rw [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] at hle
  simpa [Fintype.card_sigma, Fintype.card_prod, pow_two] using hle

def regRep (G : Type) [Group G] [Fintype G] [DecidableEq G] : G → Matrix G G ℂ :=
  fun g => Matrix.of fun x y => if x = g * y then 1 else 0

lemma regRep_isMatRep (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    IsMatRep (regRep G) := by
  constructor
  · ext x y; simp [regRep, Matrix.one_apply]
  · intro g h
    ext x y
    rw [Matrix.mul_apply]
    simp only [regRep, Matrix.of_apply]
    rw [Finset.sum_eq_single (h * y)]
    · simp [mul_assoc]
    · intro z _ hz
      simp [hz]
    · intro hz; exact (hz (Finset.mem_univ _)).elim

lemma regRep_trace (G : Type) [Group G] [Fintype G] [DecidableEq G] (g : G) :
    Matrix.trace (regRep G g) = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  simp only [Matrix.trace, Matrix.diag, regRep, Matrix.of_apply]
  by_cases hg : g = 1
  · subst hg; simp
  · rw [if_neg hg]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hne : x ≠ g * x := fun h => hg (mul_right_cancel (h.symm.trans (one_mul x).symm))
    simp [hne]

lemma subLin_trace_add {G ι : Type} [Fintype ι] {ρ : G → Matrix ι ι ℂ}
    {W U W' : Submodule ℂ (ι → ℂ)}
    (hW : IsInvariantSubspace ρ W) (hU : IsInvariantSubspace ρ U) (hW' : IsInvariantSubspace ρ W')
    (hUW : U ≤ W) (hW'W : W' ≤ W) (hdisj : U ⊓ W' = ⊥) (hsup : U ⊔ W' = W) (g : G) :
    LinearMap.trace ℂ W (subLin ρ hW g) =
      LinearMap.trace ℂ U (subLin ρ hU g) + LinearMap.trace ℂ W' (subLin ρ hW' g) := by
  let f : (U × W') →ₗ[ℂ] W :=
    { toFun := fun p => ⟨p.1.1 + p.2.1, W.add_mem (hUW p.1.2) (hW'W p.2.2)⟩
      map_add' := fun a b => by ext i; simp; ring
      map_smul' := fun c a => by ext i; simp }
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have heq : a.1.1 + a.2.1 = b.1.1 + b.2.1 := congrArg Subtype.val hab
      have hdiff : a.1.1 - b.1.1 = b.2.1 - a.2.1 := by
        ext i; have := congr_fun heq i; simp only [Pi.add_apply, Pi.sub_apply] at *; linear_combination this
      have hmemU : a.1.1 - b.1.1 ∈ U := U.sub_mem a.1.2 b.1.2
      have hmemW' : a.1.1 - b.1.1 ∈ W' := hdiff ▸ W'.sub_mem b.2.2 a.2.2
      have hbot : a.1.1 - b.1.1 ∈ U ⊓ W' := ⟨hmemU, hmemW'⟩
      rw [hdisj, Submodule.mem_bot, sub_eq_zero] at hbot
      have hbot2 : b.2.1 - a.2.1 = 0 := by rw [← hdiff, hbot, sub_self]
      rw [sub_eq_zero] at hbot2
      ext <;> simp [hbot, hbot2]
    · intro w
      have hw : w.1 ∈ U ⊔ W' := hsup ▸ w.2
      obtain ⟨u, hu, w', hw', huw⟩ := Submodule.mem_sup.mp hw
      refine ⟨(⟨u, hu⟩, ⟨w', hw'⟩), Subtype.ext huw⟩
  let e : (U × W') ≃ₗ[ℂ] W := LinearEquiv.ofBijective f hbij
  let d₁ := Module.finrank ℂ U
  let d₂ := Module.finrank ℂ W'
  let bU : Module.Basis (Fin d₁) ℂ U := Module.finBasisOfFinrankEq ℂ U rfl
  let bW' : Module.Basis (Fin d₂) ℂ W' := Module.finBasisOfFinrankEq ℂ W' rfl
  let bUW' : Module.Basis (Fin d₁ ⊕ Fin d₂) ℂ (U × W') := bU.prod bW'
  let b : Module.Basis (Fin d₁ ⊕ Fin d₂) ℂ W := bUW'.map e
  rw [LinearMap.trace_eq_matrix_trace ℂ b (subLin ρ hW g),
    LinearMap.trace_eq_matrix_trace ℂ bU (subLin ρ hU g),
    LinearMap.trace_eq_matrix_trace ℂ bW' (subLin ρ hW' g)]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, LinearMap.toMatrix_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hb_eq : b (Sum.inl i) = e (bU i, 0) := by simp [b, bUW']
    have hact : subLin ρ hW g (e (bU i, 0)) = e (subLin ρ hU g (bU i), 0) := by
      ext x; simp [e, f, subLin]
    rw [hb_eq, hact]
    dsimp [b]
    rw [Module.Basis.map_repr, LinearEquiv.trans_apply]
    simp [bUW']
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hb_eq : b (Sum.inr j) = e (0, bW' j) := by simp [b, bUW']
    have hact : subLin ρ hW g (e (0, bW' j)) = e (0, subLin ρ hW' g (bW' j)) := by
      ext x; simp [e, f, subLin]
    rw [hb_eq, hact]
    dsimp [b]
    rw [Module.Basis.map_repr, LinearEquiv.trans_apply]
    simp [bUW']

lemma sum_card_sq_eq_card {G Λ : Type} [Group G] [Fintype G] [Fintype Λ]
    {B : Λ → Type} [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
    {R : ∀ l, G → Matrix (B l) (B l) ℂ} (hR : IsIrrepSystem R) :
    ∑ l : Λ, Fintype.card (B l) ^ 2 = Fintype.card G := by
  have hsub : ∀ (d : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
      (ρ : G → Matrix ι ι ℂ) (hρ : IsMatRep ρ) (W : Submodule ℂ (ι → ℂ))
      (hW : IsInvariantSubspace ρ W) (hdim : Module.finrank ℂ W = d),
      ((Module.finrank ℂ W : ℕ) : ℂ) =
        ∑ l : Λ, ((Fintype.card G : ℂ)⁻¹ *
          ∑ g : G, LinearMap.trace ℂ W (subLin ρ hW g) * Matrix.trace (R l g⁻¹)) *
          (Fintype.card (B l) : ℂ) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro ι _ _ ρ hρ W hW hdim
      by_cases hbot : W = ⊥
      · subst hbot
        have htr0 : ∀ g : G, LinearMap.trace ℂ (⊥ : Submodule ℂ (ι → ℂ)) (subLin ρ hW g) = 0 := by
          intro g
          have : subLin ρ hW g = 0 :=
            LinearMap.ext fun x => by
              have hx0 : x = 0 := Subtype.ext ((Submodule.mem_bot ℂ).mp x.2)
              rw [hx0, map_zero, LinearMap.zero_apply]
          rw [this, map_zero]
        simp [htr0]
      · obtain ⟨k, U, b, hUinv, hUW, hUne, hρU_mat, hρU_irr⟩ :=
          exists_min_invariant_subrep hρ hbot hW
        obtain ⟨l₀, hl₀⟩ := @hR.2.2.2 (Fin k) _ _ (subRep ρ hUinv b) hρU_mat hρU_irr
        let W' := W ⊓ repOrtho ρ U
        have hW'inv : IsInvariantSubspace ρ W' := fun g v ⟨hvW, hvO⟩ =>
          ⟨hW g v hvW, repOrtho_invariant hρ hUinv g v hvO⟩
        have hcomplU := repOrtho_isCompl hρ U
        have hdisj : U ⊓ W' = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro v ⟨hvU, _, hvO⟩
          have hbot' : U ⊓ repOrtho ρ U = ⊥ := hcomplU.disjoint.eq_bot
          rw [Submodule.eq_bot_iff] at hbot'
          exact (Submodule.mem_bot ℂ).mpr (hbot' v ⟨hvU, hvO⟩)
        have hsup : U ⊔ W' = W := by
          apply le_antisymm
          · exact sup_le hUW inf_le_left
          · intro w hwW
            have hmem : w ∈ U ⊔ repOrtho ρ U := hcomplU.codisjoint.eq_top ▸ Submodule.mem_top
            obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hmem
            have hvW : v ∈ W := by
              have := W.sub_mem hwW (hUW hu)
              simpa using this
            exact Submodule.add_mem_sup hu ⟨hvW, hv⟩
        have hfin_sum := Submodule.finrank_sup_add_finrank_inf_eq U W'
        rw [hsup, hdisj, finrank_bot, add_zero] at hfin_sum
        have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
        have hU_pos : 0 < Module.finrank ℂ U := Module.finrank_pos
        have hW'_lt : Module.finrank ℂ W' < d := by omega
        have ihW' := ih (Module.finrank ℂ W') hW'_lt ρ hρ W' hW'inv rfl
        have hk_eq : Module.finrank ℂ U = Fintype.card (B l₀) := by
          rw [Module.finrank_eq_card_basis b]
          exact (repEquiv_card_eq hl₀).symm
        have hU_tr : ∀ g : G, LinearMap.trace ℂ U (subLin ρ hUinv g) = Matrix.trace (R l₀ g) :=
          fun g => by rw [← subRep_trace_eq hUinv b g, ← repEquiv_trace_eq hl₀ g]
        have hU_sum : ((Module.finrank ℂ U : ℕ) : ℂ) =
            ∑ l : Λ, ((Fintype.card G : ℂ)⁻¹ *
              ∑ g : G, LinearMap.trace ℂ U (subLin ρ hUinv g) * Matrix.trace (R l g⁻¹)) *
              (Fintype.card (B l) : ℂ) := by
          simp_rw [hU_tr]
          change ((Module.finrank ℂ U : ℕ) : ℂ) =
            ∑ l : Λ, charInner (R l₀) (R l) * (Fintype.card (B l) : ℂ)
          rw [Finset.sum_eq_single l₀]
          · rw [charInner_self_eq_one (hR.1 l₀).1 (hR.2.1 l₀), one_mul, hk_eq]
          · intro l _ hl
            rw [charInner_eq_zero_of_not_repEquiv (hR.1 l).1 (hR.1 l₀).1 (hR.2.1 l) (hR.2.1 l₀)
              (hR.2.2.1 l l₀ hl), zero_mul]
          · intro hl₀mem; exact (hl₀mem (Finset.mem_univ l₀)).elim
        calc ((Module.finrank ℂ W : ℕ) : ℂ)
            = ((Module.finrank ℂ U : ℕ) : ℂ) + ((Module.finrank ℂ W' : ℕ) : ℂ) := by
              congr 1; exact_mod_cast hfin_sum
          _ = ∑ l : Λ, ((Fintype.card G : ℂ)⁻¹ *
                ∑ g : G, LinearMap.trace ℂ U (subLin ρ hUinv g) * Matrix.trace (R l g⁻¹)) *
                (Fintype.card (B l) : ℂ) +
              ∑ l : Λ, ((Fintype.card G : ℂ)⁻¹ *
                ∑ g : G, LinearMap.trace ℂ W' (subLin ρ hW'inv g) * Matrix.trace (R l g⁻¹)) *
                (Fintype.card (B l) : ℂ) := by rw [hU_sum, ihW']
          _ = ∑ l : Λ, ((Fintype.card G : ℂ)⁻¹ *
                ∑ g : G, LinearMap.trace ℂ W (subLin ρ hW g) * Matrix.trace (R l g⁻¹)) *
                (Fintype.card (B l) : ℂ) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun l _ => ?_
              simp_rw [subLin_trace_add hW hUinv hW'inv hUW inf_le_left hdisj hsup,
                add_mul, Finset.sum_add_distrib, mul_add]
              ring
  have htop_inv : IsInvariantSubspace (regRep G) (⊤ : Submodule ℂ (G → ℂ)) :=
    fun _ _ _ => Submodule.mem_top
  have htop := hsub (Module.finrank ℂ (⊤ : Submodule ℂ (G → ℂ)))
    (regRep G) (regRep_isMatRep G) ⊤ htop_inv rfl
  have hfin_top : Module.finrank ℂ (⊤ : Submodule ℂ (G → ℂ)) = Fintype.card G := by
    rw [finrank_top, Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one]
  have htr_top : ∀ g : G,
      LinearMap.trace ℂ (⊤ : Submodule ℂ (G → ℂ)) (subLin (regRep G) htop_inv g) =
        Matrix.trace (regRep G g) := fun g => by
    let e : (⊤ : Submodule ℂ (G → ℂ)) ≃ₗ[ℂ] (G → ℂ) := Submodule.topEquiv
    let b : Module.Basis G ℂ (⊤ : Submodule ℂ (G → ℂ)) := (Pi.basisFun ℂ G).map e.symm
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp [b, e]
    rw [Module.Basis.map_repr]
    simp [subLin]
  rw [hfin_top] at htop
  have hG_ne : (Fintype.card G : ℂ) ≠ 0 := by
    have : Nonempty G := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hrhs : ∀ l : Λ,
      ((Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, LinearMap.trace ℂ (⊤ : Submodule ℂ (G → ℂ)) (subLin (regRep G) htop_inv g) *
          Matrix.trace (R l g⁻¹)) = (Fintype.card (B l) : ℂ) := fun l => by
    simp_rw [htr_top, regRep_trace]
    rw [Finset.sum_eq_single (1 : G)]
    · simp only [↓reduceIte, inv_one, (hR.1 l).1.1, Matrix.trace, Matrix.diag, Matrix.one_apply]
      simp [← mul_assoc, hG_ne]
    · intro g _ hg; simp [hg]
    · intro h1; exact (h1 (Finset.mem_univ 1)).elim
  simp_rw [hrhs] at htop
  have hnat : ((Fintype.card G : ℕ) : ℂ) = ((∑ l : Λ, Fintype.card (B l) ^ 2 : ℕ) : ℂ) := by
    simpa [sq] using htop
  exact (Nat.cast_injective hnat).symm

lemma exhaustive_of_sum_sq_eq_card {G Λ : Type} [Group G] [Fintype G] [Fintype Λ]
    {B : Λ → Type} [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
    (R : ∀ l, G → Matrix (B l) (B l) ℂ)
    (hm : ∀ l, IsMatRep (R l)) (hi : ∀ l, IsIrreducibleRep (R l))
    (hdiff : ∀ l₁ l₂, l₁ ≠ l₂ → ¬ RepEquiv (R l₁) (R l₂))
    (hsum : ∑ l : Λ, Fintype.card (B l) ^ 2 = Fintype.card G)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : G → Matrix ι ι ℂ) (hρm : IsMatRep ρ) (hρi : IsIrreducibleRep ρ) :
    ∃ l : Λ, RepEquiv (R l) ρ := by
  by_contra hnone
  push Not at hnone
  let B' : Option Λ → Type
    | none => ι
    | some l => B l
  let : ∀ k : Option Λ, Fintype (B' k) := fun k => match k with
    | none => inferInstance
    | some l => inferInstance
  let : ∀ k : Option Λ, DecidableEq (B' k) := fun k => match k with
    | none => inferInstance
    | some l => inferInstance
  let R' : ∀ k : Option Λ, G → Matrix (B' k) (B' k) ℂ
    | none => ρ
    | some l => R l
  have hm' : ∀ k, IsMatRep (R' k)
    | none => hρm
    | some l => hm l
  have hi' : ∀ k, IsIrreducibleRep (R' k)
    | none => hρi
    | some l => hi l
  have hdiff' : ∀ k₁ k₂, k₁ ≠ k₂ → ¬ RepEquiv (R' k₁) (R' k₂)
    | none, none, h => (h rfl).elim
    | none, some l, _ => fun h => hnone l (repEquiv_symm h)
    | some l, none, _ => hnone l
    | some l₁, some l₂, h => hdiff l₁ l₂ (fun he => h (congrArg some he))
  have hle := bessel_card_le B' R' hm' hi' hdiff'
  have hsplit : ∑ k : Option Λ, Fintype.card (B' k) ^ 2 =
      Fintype.card ι ^ 2 + ∑ l : Λ, Fintype.card (B l) ^ 2 :=
    Fintype.sum_option _
  rw [hsplit, hsum] at hle
  have : Nonempty ι := hρi.1
  have hpos : 0 < Fintype.card ι ^ 2 := pow_pos Fintype.card_pos 2
  omega

/-! ### Section 3: Tensor products of irrep systems and isomorphism transport -/

lemma tensorFamily_one {I : Type} [Fintype I] {ι : I → Type} [∀ r, DecidableEq (ι r)]
    [instD : DecidableEq (∀ r, ι r)] :
    tensorFamily (fun r => (1 : Matrix (ι r) (ι r) ℂ)) = 1 := by
  obtain rfl : instD = Classical.decEq _ := Subsingleton.elim _ _
  ext i j
  simp only [tensorFamily, Matrix.of_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij]
    obtain ⟨r, hr⟩ : ∃ r, i r ≠ j r := by
      by_contra h; push Not at h; exact hij (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])

lemma tensorFamily_mul {I : Type} [Fintype I] {ι : I → Type} [∀ r, Fintype (ι r)]
    [instF : Fintype (∀ r, ι r)] (A B : ∀ r, Matrix (ι r) (ι r) ℂ) :
    tensorFamily A * tensorFamily B = tensorFamily (fun r => A r * B r) := by
  obtain rfl : instF = @Pi.instFintype I ι (Classical.decEq I) _ _ := Subsingleton.elim _ _
  ext i j
  simp only [Matrix.mul_apply, tensorFamily, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun r x => A r (i r) x * B r x (j r)).symm

lemma tensorFamily_conjTranspose {I : Type} [Fintype I] {ι : I → Type}
    (A : ∀ r, Matrix (ι r) (ι r) ℂ) :
    (tensorFamily A)ᴴ = tensorFamily (fun r => (A r)ᴴ) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, tensorFamily, Matrix.of_apply,
    show ∀ (s : Finset I) (f : I → ℂ), star (∏ r ∈ s, f r) = ∏ r ∈ s, star (f r) from
      fun s f => map_prod (starRingEnd ℂ) f s]

lemma tensorFamily_trace {I : Type} [Fintype I] {ι : I → Type} [∀ r, Fintype (ι r)]
    [instF : Fintype (∀ r, ι r)] (A : ∀ r, Matrix (ι r) (ι r) ℂ) :
    Matrix.trace (tensorFamily A) = ∏ r, Matrix.trace (A r) := by
  obtain rfl : instF = @Pi.instFintype I ι (Classical.decEq I) _ _ := Subsingleton.elim _ _
  simp only [Matrix.trace, Matrix.diag, tensorFamily, Matrix.of_apply]
  exact (Fintype.prod_sum fun r x => A r x x).symm

def prodRep {I : Type} [Fintype I] {G : I → Type} {Λ : I → Type} {B : ∀ r, Λ r → Type}
    (R : ∀ r (l : Λ r), G r → Matrix (B r l) (B r l) ℂ)
    (l : ∀ r, Λ r) (g : ∀ r, G r) : Matrix (∀ r, B r (l r)) (∀ r, B r (l r)) ℂ :=
  tensorFamily fun r => R r (l r) (g r)

lemma isUnitaryRep_prodRep {I : Type} [Fintype I] [DecidableEq I] {G : I → Type} [∀ r, Monoid (G r)]
    {Λ : I → Type} {B : ∀ r, Λ r → Type} [∀ r l, Fintype (B r l)] [∀ r l, DecidableEq (B r l)]
    (R : ∀ r (l : Λ r), G r → Matrix (B r l) (B r l) ℂ)
    (l : ∀ r, Λ r) (hl : ∀ r, IsUnitaryRep (R r (l r))) :
    IsUnitaryRep (prodRep R l) := by
  refine ⟨⟨?_, ?_⟩, fun g => ?_⟩
  · simp only [prodRep, Pi.one_apply, fun r => (hl r).1.1, tensorFamily_one]
  · intro g h
    simp only [prodRep, Pi.mul_apply, fun r => (hl r).1.2 (g r) (h r), tensorFamily_mul]
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, prodRep,
      tensorFamily_conjTranspose, tensorFamily_mul]
    simp only [fun r => isUnitaryRep_mul_conjTranspose (hl r) (g r), tensorFamily_one]

lemma charInner_prodRep {I : Type} [Fintype I] [DecidableEq I] {G : I → Type} [∀ r, Group (G r)]
    [∀ r, Fintype (G r)] {Λ : I → Type} {B : ∀ r, Λ r → Type} [∀ r l, Fintype (B r l)]
    (R : ∀ r (l : Λ r), G r → Matrix (B r l) (B r l) ℂ)
    (l l' : ∀ r, Λ r) :
    charInner (prodRep R l) (prodRep R l') = ∏ r : I, charInner (R r (l r)) (R r (l' r)) := by
  simp only [charInner, prodRep, tensorFamily_trace, Pi.inv_apply]
  rw [Fintype.card_pi, Nat.cast_prod, ← Finset.prod_inv_distrib, Finset.prod_mul_distrib]
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun r x =>
    Matrix.trace (R r (l r) x) * Matrix.trace (R r (l' r) x⁻¹)).symm

lemma isIrrepSystem_prodRep {I : Type} [Fintype I] [DecidableEq I] {G : I → Type} [∀ r, Group (G r)]
    [∀ r, Fintype (G r)] {Λ : I → Type} [∀ r, Fintype (Λ r)] {B : ∀ r, Λ r → Type}
    [∀ r l, Fintype (B r l)] [∀ r l, DecidableEq (B r l)]
    (R : ∀ r (l : Λ r), G r → Matrix (B r l) (B r l) ℂ)
    (hR : ∀ r, IsIrrepSystem (R r)) :
    IsIrrepSystem (prodRep R) := by
  have hu : ∀ l, IsUnitaryRep (prodRep R l) := fun l =>
    isUnitaryRep_prodRep R l fun r => (hR r).1 (l r)
  have hi : ∀ l, IsIrreducibleRep (prodRep R l) := fun l => by
    refine isIrreducibleRep_of_charInner_self_eq_one (hu l).1
      ⟨fun r => Classical.choice ((hR r).2.1 (l r)).1⟩ ?_
    rw [charInner_prodRep]
    exact Finset.prod_eq_one fun r _ =>
      charInner_self_eq_one ((hR r).1 (l r)).1 ((hR r).2.1 (l r))
  have hdiff : ∀ l l', l ≠ l' → ¬ RepEquiv (prodRep R l) (prodRep R l') := by
    intro l l' hne
    rw [repEquiv_iff_charInner_ne_zero (hu l).1 (hu l').1 (hi l) (hi l')]
    push Not
    rw [charInner_prodRep]
    obtain ⟨r₀, hr₀⟩ : ∃ r₀, l' r₀ ≠ l r₀ := by
      by_contra h; push Not at h; exact hne (funext fun r => (h r).symm)
    exact Finset.prod_eq_zero (Finset.mem_univ r₀)
      (charInner_eq_zero_of_not_repEquiv ((hR r₀).1 (l r₀)).1 ((hR r₀).1 (l' r₀)).1
        ((hR r₀).2.1 (l r₀)) ((hR r₀).2.1 (l' r₀)) ((hR r₀).2.2.1 _ _ hr₀.symm))
  have hsum : ∑ l : (∀ r, Λ r), Fintype.card (∀ r, B r (l r)) ^ 2 =
      Fintype.card (∀ r, G r) := by
    simp_rw [Fintype.card_pi, sq, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum fun r lr => Fintype.card (B r lr) * Fintype.card (B r lr)]
    congr 1
    ext r
    simpa [sq] using sum_card_sq_eq_card (hR r)
  refine ⟨hu, hi, hdiff, fun {ι} _ _ ρ hρm hρi =>
    exhaustive_of_sum_sq_eq_card (prodRep R) (fun l => (hu l).1) hi hdiff hsum ρ hρm hρi⟩

lemma isIrrepSystem_comp_mulEquiv {G H Λ : Type} [Group G] [Group H]
    (e : G ≃* H) {B : Λ → Type} [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
    {R : ∀ l, H → Matrix (B l) (B l) ℂ} (hR : IsIrrepSystem R) :
    IsIrrepSystem (fun l g => R l (e g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l
    refine ⟨⟨?_, ?_⟩, fun g => (hR.1 l).2 (e g)⟩
    · simp [(hR.1 l).1.1]
    · intro g₁ g₂; simp [(hR.1 l).1.2]
  · intro l
    refine ⟨((hR.2.1) l).1, fun W hW => ((hR.2.1) l).2 W fun h v hv => ?_⟩
    simpa using hW (e.symm h) v hv
  · intro l₁ l₂ hne ⟨A, B', hAB, hBA, hi⟩
    refine hR.2.2.1 l₁ l₂ hne ⟨A, B', hAB, hBA, fun h _ => ?_⟩
    simpa using hi (e.symm h) (Set.mem_univ _)
  · intro ι _ _ ρ hρm hρi
    let ρ' : H → Matrix ι ι ℂ := fun h => ρ (e.symm h)
    have hρ'm : IsMatRep ρ' := ⟨by simp [ρ', hρm.1], fun x y => by simp [ρ', hρm.2]⟩
    have hρ'i : IsIrreducibleRep ρ' := ⟨hρi.1, fun W hW => hρi.2 W fun g v hv => by
      simpa [ρ'] using hW (e g) v hv⟩
    obtain ⟨l, A, B', hAB, hBA, hi⟩ := @hR.2.2.2 ι _ _ ρ' hρ'm hρ'i
    exact ⟨l, A, B', hAB, hBA, fun g _ => by simpa [ρ'] using hi (e g) (Set.mem_univ _)⟩

lemma isIrrepSystem_congr {G Λ : Type} [Monoid G] {B : Λ → Type}
    {instF₁ instF₂ : ∀ l, Fintype (B l)} {instD₁ instD₂ : ∀ l, DecidableEq (B l)}
    {R₁ R₂ : ∀ l, G → Matrix (B l) (B l) ℂ} (hR : ∀ l g, R₁ l g = R₂ l g)
    (h : @IsIrrepSystem G Λ _ B instF₁ instD₁ R₁) :
    @IsIrrepSystem G Λ _ B instF₂ instD₂ R₂ := by
  obtain rfl : instF₁ = instF₂ := funext fun l => Subsingleton.elim _ _
  obtain rfl : instD₁ = instD₂ := funext fun l => Subsingleton.elim _ _
  obtain rfl : R₁ = R₂ := funext fun l => funext fun g => hR l g
  exact h

lemma isIrrepSystem_charInner {G Λ : Type} [Group G] [Fintype G]
    {B : Λ → Type} [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
    {R : ∀ l, G → Matrix (B l) (B l) ℂ} (hR : IsIrrepSystem R) (l l' : Λ) :
    charInner (R l) (R l') = if l = l' then 1 else 0 := by
  by_cases h : l = l'
  · subst h; rw [if_pos rfl]; exact charInner_self_eq_one (hR.1 l).1 (hR.2.1 l)
  · rw [if_neg h]; exact charInner_eq_zero_of_not_repEquiv (hR.1 l').1 (hR.1 l).1
      (hR.2.1 l') (hR.2.1 l) (hR.2.2.1 l' l (Ne.symm h))

/-! ### Section 4: Wreath product structure, `baseRep`, `inertiaW`, `extRep`, `blockPerm`, `littleRep` -/

lemma mem_baseGroup_iff {F : Type} [Group F] {n : ℕ} {x : WP F n} :
    x ∈ baseGroup F n ↔ x.right = 1 := by
  change x ∈ WreathProduct.inl.range ↔ x.right = 1
  rw [WreathProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, WreathProduct.rightHom_apply]

def baseGroupEquiv (F : Type) [Group F] (n : ℕ) : (Fin n → F) ≃* baseGroup F n where
  toFun f := ⟨WreathProduct.inl f, f, rfl⟩
  invFun x := (x : WP F n).left
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    refine WreathProduct.ext rfl ?_
    exact (mem_baseGroup_iff.mp x.2).symm
  map_mul' f₁ f₂ := Subtype.ext (WreathProduct.inl.map_mul f₁ f₂)

lemma isIrrepSystem_baseRep {F : Type} [Group F] [Fintype F] {n : ℕ}
    {ΛF : Type} [Fintype ΛF] {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]
    {RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ} (hRF : IsIrrepSystem RF) :
    IsIrrepSystem (baseRep (F := F) (n := n) RF) := by
  have hprod := isIrrepSystem_prodRep (I := Fin n) (G := fun _ => F) (Λ := fun _ => ΛF)
    (B := fun _ => BF) (fun _ => RF) (fun _ => hRF)
  have hprod' : IsIrrepSystem (prodRep (fun _ : Fin n => RF)) :=
    isIrrepSystem_congr (fun _ _ => rfl) hprod
  have hcomp := isIrrepSystem_comp_mulEquiv (baseGroupEquiv F n).symm hprod'
  exact isIrrepSystem_congr (fun _ _ => rfl) hcomp

def permMat {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (e : ι₁ ≃ ι₂) : Matrix ι₂ ι₁ ℂ :=
  Matrix.of fun j i => if j = e i then 1 else 0

lemma permMat_mul_conjTranspose {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] (e : ι₁ ≃ ι₂) :
    permMat e * (permMat e)ᴴ = 1 := by
  ext j₁ j₂
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm j₂)]
  · simp [permMat, Matrix.one_apply, eq_comm]
  · intro i _ hi
    have hne : j₂ ≠ e i := fun h => hi (by rw [h, e.symm_apply_apply])
    simp [permMat, hne]
  · intro h; exact (h (Finset.mem_univ _)).elim

lemma permMat_conjTranspose_mul {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] (e : ι₁ ≃ ι₂) :
    (permMat e)ᴴ * permMat e = 1 := by
  ext i₁ i₂
  rw [Matrix.mul_apply, Finset.sum_eq_single (e i₂)]
  · simp [permMat, Matrix.one_apply, eq_comm]
  · intro j _ hj
    simp [permMat, hj]
  · intro h; exact (h (Finset.mem_univ _)).elim

lemma permMat_conj_apply {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] (e : ι₁ ≃ ι₂) (A : Matrix ι₁ ι₁ ℂ) (j₁ j₂ : ι₂) :
    (permMat e * A * (permMat e)ᴴ) j₁ j₂ = A (e.symm j₁) (e.symm j₂) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm j₂)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm j₁)]
    · simp [permMat]
    · intro i _ hi
      have hne : j₁ ≠ e i := fun h => hi (by rw [h, e.symm_apply_apply])
      simp [permMat, hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro i _ hi
    have hne : j₂ ≠ e i := fun h => hi (by rw [h, e.symm_apply_apply])
    simp [permMat, hne]
  · intro h; exact (h (Finset.mem_univ _)).elim

lemma permMat_trans {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]
    (e₁ : ι₁ ≃ ι₂) (e₂ : ι₂ ≃ ι₃) :
    permMat (e₁.trans e₂) = permMat e₂ * permMat e₁ := by
  ext k i
  rw [Matrix.mul_apply, Finset.sum_eq_single (e₁ i)]
  · simp [permMat]; rfl
  · intro j _ hj
    simp [permMat, hj]
  · intro h; exact (h (Finset.mem_univ _)).elim

lemma permMat_refl {ι : Type} [Fintype ι] [DecidableEq ι] :
    permMat (Equiv.refl ι) = 1 := by
  ext i j
  simp [permMat, Matrix.one_apply]; rfl

lemma cast_BF_heq {α : Type} (B : α → Type) {a b : α} (h : a = b) (x : B a) :
    HEq (cast (congrArg B h) x) x := by
  subst h; rfl

lemma cast_BF_eq_heq {α : Type} (B : α → Type) {a b : α} {h : a = b} (x : B a) (y : B b)
    (hxy : HEq x y) : cast (congrArg B h) x = y := by
  subst h; exact eq_of_heq hxy

lemma eq_of_cast_heq {α : Type} (B : α → Type) {a b c : α} {h₁ : a = b} {h₂ : b = c}
    (x : B a) (y : B c) (hxy : HEq x y) :
    cast (congrArg B h₂) (cast (congrArg B h₁) x) = y := by
  subst h₁; subst h₂; exact eq_of_heq hxy

lemma cast_eq_cast_cast {α : Type} (B : α → Type) {a₁ a₂ b c : α}
    {h₁ : a₁ = c} {h₂ : a₂ = b} {h₃ : b = c} (x : B a₁) (y : B a₂) (hxy : HEq x y) :
    cast (congrArg B h₁) x = cast (congrArg B h₃) (cast (congrArg B h₂) y) := by
  subst h₁; subst h₂; subst h₃; exact eq_of_heq hxy

lemma fun_heq {α : Type} {P : α → Type} (f : ∀ a, P a) {a b : α} (h : a = b) :
    HEq (f a) (f b) := by subst h; rfl

lemma cast_fun_eq {α γ : Type} (B : α → Type) (f : γ → α) (v : ∀ c, B (f c))
    {c₁ c₂ : γ} (h : c₁ = c₂) (hf : f c₁ = f c₂) :
    cast (congrArg B hf) (v c₁) = v c₂ := by subst h; rfl

lemma cast_cast_fun_eq {α γ : Type} (B : α → Type) (f : γ → α) (v : ∀ c, B (f c))
    {c₁ c₂ : γ} (h : c₁ = c₂) {mid : α} (h₁ : f c₁ = mid) (h₂ : mid = f c₂) :
    cast (congrArg B h₂) (cast (congrArg B h₁) (v c₁)) = v c₂ := by
  subst h; exact @eq_of_cast_heq _ B _ _ _ h₁ h₂ (v c₁) (v c₁) HEq.rfl

lemma cast_eq_cast_cast_fun {α γ : Type} (B : α → Type) (f : γ → α) (v : ∀ c, B (f c))
    {c₁ c₂ : γ} (h : c₁ = c₂) {dst mid : α}
    (h₁ : f c₁ = dst) (h₂ : f c₂ = mid) (h₃ : mid = dst) :
    cast (congrArg B h₁) (v c₁) = cast (congrArg B h₃) (cast (congrArg B h₂) (v c₂)) := by
  subst h; exact @cast_eq_cast_cast _ B _ _ _ _ h₁ h₂ h₃ (v c₁) (v c₁) HEq.rfl

lemma transport_baseRep_repEquiv {F : Type} [Group F] {n : ℕ}
    {ΛF : Type} {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]
    (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (hRF : IsIrrepSystem RF)
    (g : WP F n) (l : Fin n → ΛF) :
    RepEquiv (baseRep (F := F) RF (fun s => l (g.right⁻¹ s)))
      (transport (baseGroup F n) (baseRep RF l) g) := by
  let π : Equiv.Perm (Fin n) := g.right
  let e : (∀ r, BF (l r)) ≃ (∀ s, BF (l (π⁻¹ s))) :=
    { toFun := fun v s => v (π⁻¹ s)
      invFun := fun w r => cast (congrArg BF (congrArg l (π.left_inv r))) (w (π r))
      left_inv := fun v => by
        ext r
        exact cast_fun_eq BF l v (π.left_inv r) (congrArg l (π.left_inv r))
      right_inv := fun w => by
        ext s
        exact cast_fun_eq BF (fun t => l (π⁻¹ t)) w (π.right_inv s)
          (congrArg l (π.left_inv (π⁻¹ s))) }
  let P : Matrix (∀ s, BF (l (π⁻¹ s))) (∀ r, BF (l r)) ℂ := permMat e
  let D : Matrix (∀ r, BF (l r)) (∀ r, BF (l r)) ℂ :=
    tensorFamily fun r => RF (l r) (g.left (π r))
  have hD_inv : (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) * D = 1 := by
    dsimp only [D]
    rw [tensorFamily_mul]
    simp only [fun r => isMatRep_inv_mul (hRF.1 (l r)).1 (g.left (π r)), tensorFamily_one]
  have hD_inv' : D * (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) = 1 := by
    dsimp only [D]
    rw [tensorFamily_mul]
    simp only [fun r => isMatRep_mul_inv (hRF.1 (l r)).1 (g.left (π r)), tensorFamily_one]
  let A : Matrix (∀ r, BF (l r)) (∀ s, BF (l (π⁻¹ s))) ℂ :=
    (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) * Pᴴ
  let B : Matrix (∀ s, BF (l (π⁻¹ s))) (∀ r, BF (l r)) ℂ := P * D
  refine ⟨A, B, ?_, ?_, fun x _ => ?_⟩
  · calc A * B
        = (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) * (Pᴴ * P) * D := by
            simp only [A, B, Matrix.mul_assoc]
      _ = (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) * D := by
            rw [permMat_conjTranspose_mul e, Matrix.mul_one]
      _ = 1 := hD_inv
  · calc B * A
        = P * (D * (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹)) * Pᴴ := by
            simp only [A, B, Matrix.mul_assoc]
      _ = P * Pᴴ := by rw [hD_inv', Matrix.mul_one]
      _ = 1 := permMat_mul_conjTranspose e
  · have hleft : ∀ r : Fin n,
        (g⁻¹ * (x : WP F n) * g).left r =
          (g.left (π r))⁻¹ * (x : WP F n).left (π r) * g.left (π r) := fun r => by
      have hx : (x : WP F n).right = 1 := mem_baseGroup_iff.mp x.2
      simp only [WreathProduct.mul_left, WreathProduct.inv_left, WreathProduct.mul_right,
        WreathProduct.inv_right, Pi.mul_apply, Pi.inv_apply, hx, mul_one, inv_inv]
      rfl
    have htr_eq : transport (baseGroup F n) (baseRep RF l) g x =
        (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) *
          (tensorFamily fun r => RF (l r) ((x : WP F n).left (π r))) * D := by
      simp only [transport, baseRep, hleft]
      dsimp only [D]
      rw [tensorFamily_mul, tensorFamily_mul]
      congr 1; ext r
      rw [(hRF.1 (l r)).1.2, (hRF.1 (l r)).1.2]
    have hconj : P * (tensorFamily fun r => RF (l r) ((x : WP F n).left (π r))) * Pᴴ =
        baseRep (F := F) RF (fun s => l (π⁻¹ s)) x := by
      ext j₁ j₂
      rw [permMat_conj_apply e]
      simp only [tensorFamily, baseRep, Matrix.of_apply]
      refine Fintype.prod_equiv π _ _ fun r => ?_
      have h1 : e.symm j₁ r = cast (congrArg BF (congrArg l (π.left_inv r))) (j₁ (π r)) := rfl
      have h2 : e.symm j₂ r = cast (congrArg BF (congrArg l (π.left_inv r))) (j₂ (π r)) := rfl
      rw [h1, h2]
      have hcast : ∀ {a b : Fin n} (h : a = b) (v : F) (ja jb : BF (l b)),
          RF (l a) v (cast (congrArg BF (congrArg l h.symm)) ja)
            (cast (congrArg BF (congrArg l h.symm)) jb) = RF (l b) v ja jb := by
        intro a b h v ja jb; subst h; rfl
      exact hcast (π.left_inv r).symm ((x : WP F n).left (π r)) (j₁ (π r)) (j₂ (π r))
    calc A * baseRep (F := F) RF (fun s => l (π⁻¹ s)) x
        = (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) * Pᴴ *
            (P * (tensorFamily fun r => RF (l r) ((x : WP F n).left (π r))) * Pᴴ) := by
            rw [hconj]
      _ = (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) * (Pᴴ * P) *
            (tensorFamily fun r => RF (l r) ((x : WP F n).left (π r))) * Pᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) *
            (tensorFamily fun r => RF (l r) ((x : WP F n).left (π r))) * Pᴴ := by
            rw [permMat_conjTranspose_mul e, Matrix.mul_one]
      _ = (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹) *
            (tensorFamily fun r => RF (l r) ((x : WP F n).left (π r))) *
            (D * (tensorFamily fun r => RF (l r) (g.left (π r))⁻¹)) * Pᴴ := by
            rw [hD_inv', Matrix.mul_one]
      _ = transport (baseGroup F n) (baseRep RF l) g x * A := by
            rw [htr_eq]
            simp only [A, Matrix.mul_assoc]

lemma baseRep_congr {F : Type} [Group F] {n : ℕ} {ΛF : Type}
    {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]
    (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) {l₁ l₂ : Fin n → ΛF} (h : l₁ = l₂) :
    RepEquiv (baseRep (F := F) RF l₁) (baseRep (F := F) RF l₂) := by
  subst h; exact repEquiv_refl _

lemma inertia_baseRep_eq_inertiaW {F : Type} [Group F] [Fintype F] {n : ℕ}
    {ΛF : Type} [Fintype ΛF] {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]
    (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (hRF : IsIrrepSystem RF) (σ : Fin n → ΛF) :
    inertia (baseGroup F n) (baseRep (F := F) RF) σ = inertiaW (F := F) σ := by
  ext g
  change RepEquiv (transport (baseGroup F n) (baseRep RF σ) g) (baseRep RF σ) ↔
    ∀ r, σ (g.right⁻¹ r) = σ r
  have heq := transport_baseRep_repEquiv RF hRF g σ
  have hirr := isIrrepSystem_baseRep (F := F) (n := n) hRF
  constructor
  · intro hg
    have hrep := repEquiv_trans heq hg
    have hl : (fun s => σ (g.right⁻¹ s)) = σ := by
      by_contra hne
      exact hirr.2.2.1 _ _ hne hrep
    exact congr_fun hl
  · intro hg
    have hl : (fun s => σ (g.right⁻¹ s)) = σ := funext hg
    exact repEquiv_symm (repEquiv_trans (baseRep_congr RF hl.symm) heq)

lemma antitone_orbit_unique {n : ℕ} {ΛF : Type} [LinearOrder ΛF]
    {σ₁ σ₂ : Fin n → ΛF} (h₁ : Antitone σ₁) (h₂ : Antitone σ₂)
    (π : Equiv.Perm (Fin n)) (hπ : σ₂ = fun r => σ₁ (π⁻¹ r)) : σ₁ = σ₂ := by
  have hcard : ∀ ρ : ΛF,
      Finset.card (Finset.univ.filter fun r => ρ < σ₁ r) =
      Finset.card (Finset.univ.filter fun r => ρ < σ₂ r) := fun ρ => by
    rw [hπ]
    refine Finset.card_bij (fun r _ => π r) ?_ ?_ ?_
    · intro r hr
      simpa using hr
    · intro a _ b _ hab
      exact π.injective hab
    · intro s hs
      refine ⟨π⁻¹ s, ?_, by simp⟩
      simpa using hs
  have hlt : ∀ (σ : Fin n → ΛF), Antitone σ → ∀ (ρ : ΛF) (i : Fin n),
      ρ < σ i ↔ i.val < Finset.card (Finset.univ.filter fun r => ρ < σ r) := by
    intro σ hσ ρ i
    let S : Finset (Fin n) := Finset.univ.filter fun r => ρ < σ r
    change ρ < σ i ↔ i.val < S.card
    have hdown : ∀ a b : Fin n, a ≤ b → b ∈ S → a ∈ S := fun a b hab hb => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact lt_of_lt_of_le hb (hσ hab)
    by_cases hi : ρ < σ i
    · have him : i ∈ S := by simpa [S] using hi
      have hsub : Finset.Iic i ⊆ S := fun a ha => hdown a i (Finset.mem_Iic.mp ha) him
      have hcard_le := Finset.card_le_card hsub
      rw [Fin.card_Iic] at hcard_le
      exact ⟨fun _ => by omega, fun _ => hi⟩
    · constructor
      · intro h; exact (hi h).elim
      · intro hlt_card
        exfalso
        have hsub : S ⊆ Finset.Iio i := fun a ha => by
          rw [Finset.mem_Iio]
          by_contra hge
          have hia : i ≤ a := not_lt.mp hge
          exact hi (lt_of_lt_of_le (by simpa [S] using ha) (hσ hia))
        have hcard_le := Finset.card_le_card hsub
        rw [Fin.card_Iio] at hcard_le
        omega
  ext i
  rcases lt_trichotomy (σ₁ i) (σ₂ i) with hlt1 | heq | hlt2
  · have h1 := (hlt σ₂ h₂ (σ₁ i) i).mp hlt1
    rw [← hcard (σ₁ i), ← hlt σ₁ h₁ (σ₁ i) i] at h1
    exact (lt_irrefl _ h1).elim
  · exact heq
  · have h2 := (hlt σ₁ h₁ (σ₂ i) i).mp hlt2
    rw [hcard (σ₂ i), ← hlt σ₂ h₂ (σ₂ i) i] at h2
    exact (lt_irrefl _ h2).elim

lemma exists_antitone_orbit {n : ℕ} {ΛF : Type} [LinearOrder ΛF] (l : Fin n → ΛF) :
    ∃ (σ : Fin n → ΛF) (_hσ : Antitone σ) (π : Equiv.Perm (Fin n)), l = fun r => σ (π⁻¹ r) := by
  let f : Fin n → OrderDual ΛF := fun r => OrderDual.toDual (l r)
  let τ : Equiv.Perm (Fin n) := Tuple.sort f
  let σ : Fin n → ΛF := fun r => l (τ r)
  have hσ : Antitone σ := fun a b hab => by
    have hm := Tuple.monotone_sort f hab
    exact OrderDual.ofDual_le_ofDual.mp hm
  refine ⟨σ, hσ, τ, ?_⟩
  ext r
  simp [σ]

def transportEquiv {F : Type} [Group F] {n : ℕ} {ΛF : Type} (BF : ΛF → Type)
    (σ : Fin n → ΛF) (x : inertiaW (F := F) σ) :
    (∀ r, BF (σ r)) ≃ (∀ r, BF (σ r)) where
  toFun i r := cast (congrArg BF (inertiaW_inv_apply x r)) (i ((x : WP F n).right⁻¹ r))
  invFun j s := cast (congrArg BF (inertiaW_apply x s)) (j ((x : WP F n).right s))
  left_inv i := by
    ext r
    exact cast_cast_fun_eq BF σ i ((x : WP F n).right.left_inv r)
      (inertiaW_inv_apply x ((x : WP F n).right r)) (inertiaW_apply x r)
  right_inv j := by
    ext s
    exact cast_cast_fun_eq BF σ j ((x : WP F n).right.right_inv s)
      (inertiaW_apply x ((x : WP F n).right⁻¹ s)) (inertiaW_inv_apply x s)

lemma transportU_eq_permMat {F : Type} [Group F] {n : ℕ} {ΛF : Type}
    (BF : ΛF → Type) [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]
    (σ : Fin n → ΛF) (x : inertiaW (F := F) σ) :
    transportU (BF := BF) σ x = permMat (transportEquiv BF σ x) := by
  ext j i
  simp only [transportU, permMat, Matrix.of_apply, transportEquiv, Equiv.coe_fn_mk, funext_iff]

lemma transportEquiv_one {F : Type} [Group F] {n : ℕ} {ΛF : Type} (BF : ΛF → Type)
    (σ : Fin n → ΛF) :
    transportEquiv (F := F) BF σ 1 = Equiv.refl _ := by
  ext i r
  dsimp [transportEquiv]
  have h1 : (((1 : inertiaW (F := F) σ) : WP F n).right)⁻¹ r = r := by
    rw [OneMemClass.coe_one, WreathProduct.one_right, inv_one]
    rfl
  exact cast_fun_eq BF σ i h1 (inertiaW_inv_apply 1 r)

lemma transportEquiv_mul {F : Type} [Group F] {n : ℕ} {ΛF : Type} (BF : ΛF → Type)
    (σ : Fin n → ΛF) (x y : inertiaW (F := F) σ) :
    transportEquiv BF σ (x * y) = (transportEquiv BF σ y).trans (transportEquiv BF σ x) := by
  ext i r
  dsimp [transportEquiv]
  have hm : (((x * y : inertiaW (F := F) σ) : WP F n).right)⁻¹ r =
      (y : WP F n).right⁻¹ ((x : WP F n).right⁻¹ r) := by
    rw [Subgroup.coe_mul, WreathProduct.mul_right, mul_inv_rev]
    rfl
  exact cast_eq_cast_cast_fun BF σ i hm (inertiaW_inv_apply (x * y) r)
    (inertiaW_inv_apply y ((x : WP F n).right⁻¹ r)) (inertiaW_inv_apply x r)

lemma isUnitaryRep_transportU {F : Type} [Group F] {n : ℕ} {ΛF : Type}
    (BF : ΛF → Type) [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]
    (σ : Fin n → ΛF) :
    IsUnitaryRep (transportU (F := F) (BF := BF) σ) := by
  refine ⟨⟨?_, ?_⟩, fun x => ?_⟩
  · rw [transportU_eq_permMat, transportEquiv_one, permMat_refl]
  · intro x y; simp only [transportU_eq_permMat]; rw [transportEquiv_mul, permMat_trans]
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, transportU_eq_permMat,
      permMat_mul_conjTranspose]

lemma transportU_conj_tensorFamily {F : Type} [Group F] {n : ℕ} {ΛF : Type}
    {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]
    (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (σ : Fin n → ΛF)
    (x : inertiaW (F := F) σ) (f : Fin n → F) :
    transportU (BF := BF) σ x * (tensorFamily fun r => RF (σ r) (f r)) *
        (transportU (BF := BF) σ x)ᴴ =
      tensorFamily fun r => RF (σ r) (f ((x : WP F n).right⁻¹ r)) := by
  rw [transportU_eq_permMat]
  ext j k
  rw [permMat_conj_apply]
  simp only [tensorFamily, Matrix.of_apply]
  refine Fintype.prod_equiv (x : WP F n).right
    (fun r => RF (σ r) (f r) ((transportEquiv BF σ x).symm j r) ((transportEquiv BF σ x).symm k r))
    (fun s => RF (σ s) (f ((x : WP F n).right⁻¹ s)) (j s) (k s)) fun r => ?_
  let e := transportEquiv BF σ x
  have hinv_r : (x : WP F n).right⁻¹ ((x : WP F n).right r) = r := by simp
  have hcast_eq : ∀ {a b : ΛF} (h : a = b) {v₁ v₂ : F} (hv : v₁ = v₂)
      (ja : BF a) (jb : BF b) (ka : BF a) (kb : BF b),
      HEq ja jb → HEq ka kb → RF a v₁ ja ka = RF b v₂ jb kb := by
    intro a b h v₁ v₂ hv ja jb ka kb hj hk
    subst h; subst hv
    rw [eq_of_heq hj, eq_of_heq hk]
  refine hcast_eq (inertiaW_apply x r).symm (congrArg f hinv_r.symm) _ _ _ _ ?_ ?_
  · have h1 := congr_fun (e.apply_symm_apply j) ((x : WP F n).right r)
    dsimp [e, transportEquiv] at h1
    have h2 : HEq ((e.symm j) r) ((e.symm j) ((x : WP F n).right⁻¹ ((x : WP F n).right r))) :=
      fun_heq (e.symm j) hinv_r.symm
    exact h2.trans
      ((cast_BF_heq BF (inertiaW_inv_apply x ((x : WP F n).right r)) _).symm.trans (heq_of_eq h1))
  · have h1 := congr_fun (e.apply_symm_apply k) ((x : WP F n).right r)
    dsimp [e, transportEquiv] at h1
    have h2 : HEq ((e.symm k) r) ((e.symm k) ((x : WP F n).right⁻¹ ((x : WP F n).right r))) :=
      fun_heq (e.symm k) hinv_r.symm
    exact h2.trans
      ((cast_BF_heq BF (inertiaW_inv_apply x ((x : WP F n).right r)) _).symm.trans (heq_of_eq h1))

lemma isUnitaryRep_extRep {F : Type} [Group F] {n : ℕ} {ΛF : Type}
    {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]
    (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (hRF : IsIrrepSystem RF) (σ : Fin n → ΛF) :
    IsUnitaryRep (extRep (F := F) RF σ) := by
  have hU := isUnitaryRep_transportU (F := F) BF σ
  have hD : ∀ x : inertiaW (F := F) σ,
      (tensorFamily fun r => RF (σ r) ((x : WP F n).left r)) ∈ Matrix.unitaryGroup _ ℂ := by
    intro x
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, tensorFamily_conjTranspose,
      tensorFamily_mul]
    simp only [fun r => isUnitaryRep_mul_conjTranspose (hRF.1 (σ r)) ((x : WP F n).left r),
      tensorFamily_one]
  refine ⟨⟨?_, ?_⟩, fun x => ?_⟩
  · simp only [extRep, OneMemClass.coe_one, WreathProduct.one_left, Pi.one_apply,
      fun r => (hRF.1 (σ r)).1.1, tensorFamily_one, hU.1.1, Matrix.mul_one]
  · intro x y
    simp only [extRep]
    have hconj : transportU (BF := BF) σ x *
        (tensorFamily fun r => RF (σ r) ((y : WP F n).left r)) =
        (tensorFamily fun r => RF (σ r) ((y : WP F n).left ((x : WP F n).right⁻¹ r))) *
          transportU (BF := BF) σ x := by
      calc transportU (BF := BF) σ x * (tensorFamily fun r => RF (σ r) ((y : WP F n).left r))
          = (transportU (BF := BF) σ x * (tensorFamily fun r => RF (σ r) ((y : WP F n).left r)) *
              (transportU (BF := BF) σ x)ᴴ) * transportU (BF := BF) σ x := by
              rw [Matrix.mul_assoc _ _ (transportU (BF := BF) σ x),
                isUnitaryRep_conjTranspose_mul hU x, Matrix.mul_one]
        _ = (tensorFamily fun r => RF (σ r) ((y : WP F n).left ((x : WP F n).right⁻¹ r))) *
              transportU (BF := BF) σ x := by
              rw [transportU_conj_tensorFamily]
    calc (tensorFamily fun r => RF (σ r) ((x * y : inertiaW (F := F) σ).1.left r)) *
            transportU (BF := BF) σ (x * y)
        = (tensorFamily fun r => RF (σ r) ((x : WP F n).left r) *
            RF (σ r) ((y : WP F n).left ((x : WP F n).right⁻¹ r))) *
            (transportU (BF := BF) σ x * transportU (BF := BF) σ y) := by
            congr 1
            · ext j k; simp [tensorFamily, WreathProduct.mul_left, (hRF.1 (σ _)).1.2]
            · exact hU.1.2 x y
      _ = ((tensorFamily fun r => RF (σ r) ((x : WP F n).left r)) *
            (tensorFamily fun r => RF (σ r) ((y : WP F n).left ((x : WP F n).right⁻¹ r)))) *
            (transportU (BF := BF) σ x * transportU (BF := BF) σ y) := by
            rw [tensorFamily_mul]
      _ = (tensorFamily fun r => RF (σ r) ((x : WP F n).left r)) *
            ((tensorFamily fun r => RF (σ r) ((y : WP F n).left ((x : WP F n).right⁻¹ r))) *
              transportU (BF := BF) σ x) * transportU (BF := BF) σ y := by
            simp only [Matrix.mul_assoc]
      _ = ((tensorFamily fun r => RF (σ r) ((x : WP F n).left r)) * transportU (BF := BF) σ x) *
            ((tensorFamily fun r => RF (σ r) ((y : WP F n).left r)) * transportU (BF := BF) σ y) := by
            rw [← hconj]
            simp only [Matrix.mul_assoc]
  · exact (Matrix.unitaryGroup _ ℂ).mul_mem (hD x) (hU.2 x)

lemma extRep_mem_baseGroup {F : Type} [Group F] {n : ℕ} {ΛF : Type}
    {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]
    (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (σ : Fin n → ΛF)
    {x : WP F n} (hx : x ∈ baseGroup F n) (hxI : x ∈ inertiaW (F := F) σ) :
    extRep (F := F) RF σ ⟨x, hxI⟩ = baseRep (F := F) RF σ ⟨x, hx⟩ := by
  have hr : x.right = 1 := mem_baseGroup_iff.mp hx
  have hid : transportEquiv BF σ ⟨x, hxI⟩ = Equiv.refl _ := by
    ext i r
    dsimp [transportEquiv]
    have h1 : (x.right)⁻¹ r = r := by rw [hr, inv_one]; rfl
    exact cast_fun_eq BF σ i h1 (inertiaW_inv_apply ⟨x, hxI⟩ r)
  have hU1 : transportU (BF := BF) σ ⟨x, hxI⟩ = 1 := by
    rw [transportU_eq_permMat, hid, permMat_refl]
  simp [extRep, baseRep, hU1]

lemma baseGroup_le_inertiaW {F : Type} [Group F] {n : ℕ} {ΛF : Type} (σ : Fin n → ΛF) :
    baseGroup F n ≤ inertiaW (F := F) σ := by
  intro x hx r
  rw [mem_baseGroup_iff.mp hx, inv_one, Equiv.Perm.one_apply]

def blockHom {F : Type} [Group F] {n : ℕ} {ΛF : Type} [LinearOrder ΛF] (σ : Fin n → ΛF) :
    inertiaW (F := F) σ →* (∀ ρ, Equiv.Perm (Fin (Fintype.card (block σ ρ)))) where
  toFun x ρ := blockPerm σ ρ x
  map_one' := by
    ext ρ i
    simp [blockPerm]
  map_mul' x y := by
    ext ρ i
    simp [blockPerm]

lemma blockHom_ker {F : Type} [Group F] {n : ℕ} {ΛF : Type} [LinearOrder ΛF] (σ : Fin n → ΛF) :
    (blockHom (F := F) σ).ker = (baseGroup F n).subgroupOf (inertiaW (F := F) σ) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_baseGroup_iff]
  constructor
  · intro hx
    ext r
    have hxρ := congr_fun hx (σ r)
    let e := (Fintype.orderIsoFinOfCardEq (block σ (σ r)) rfl).toEquiv
    have h1 := congr_arg (fun p : Equiv.Perm _ => e (p (e.symm ⟨r, rfl⟩))) hxρ
    have h1' : e ((blockPerm σ (σ r) x) (e.symm ⟨r, rfl⟩)) = e (e.symm ⟨r, rfl⟩) := h1
    dsimp [blockPerm] at h1'
    have hsub : ((e.trans ((x : WP F n).right.subtypePerm
        (fun r' => by rw [inertiaW_apply x r']))).trans e.symm) (e.symm ⟨r, rfl⟩) =
        e.symm ⟨(x : WP F n).right (e (e.symm ⟨r, rfl⟩)).1,
          (inertiaW_apply x (e (e.symm ⟨r, rfl⟩)).1).trans (e (e.symm ⟨r, rfl⟩)).2⟩ := rfl
    have he_eq : (⟨(x : WP F n).right (e (e.symm ⟨r, rfl⟩)).1,
        (inertiaW_apply x (e (e.symm ⟨r, rfl⟩)).1).trans (e (e.symm ⟨r, rfl⟩)).2⟩ :
        block σ (σ r)) =
        ⟨(x : WP F n).right r, (inertiaW_apply x r).trans rfl⟩ := by
      apply Subtype.ext
      change (x : WP F n).right (e (e.symm ⟨r, rfl⟩)).1 = (x : WP F n).right r
      rw [congrArg Subtype.val (e.apply_symm_apply ⟨r, rfl⟩)]
    change e (e.symm ⟨(x : WP F n).right (e (e.symm ⟨r, rfl⟩)).1,
        (inertiaW_apply x (e (e.symm ⟨r, rfl⟩)).1).trans (e (e.symm ⟨r, rfl⟩)).2⟩) =
      e (e.symm ⟨r, rfl⟩) at h1'
    rw [he_eq, e.apply_symm_apply, e.apply_symm_apply] at h1'
    exact congrArg Fin.val (congrArg Subtype.val h1')
  · intro hx
    ext ρ i
    simp [blockHom, blockPerm, hx]

lemma blockHom_surjective {F : Type} [Group F] {n : ℕ} {ΛF : Type} [LinearOrder ΛF]
    (σ : Fin n → ΛF) :
    Function.Surjective (blockHom (F := F) σ) := by
  intro q
  let e : ∀ ρ, Fin (Fintype.card (block σ ρ)) ≃ block σ ρ := fun ρ =>
    (Fintype.orderIsoFinOfCardEq (block σ ρ) rfl).toEquiv
  let p : ∀ ρ, Equiv.Perm (block σ ρ) := fun ρ => ((e ρ).symm.trans (q ρ)).trans (e ρ)
  let π : Equiv.Perm (Fin n) :=
    { toFun := fun r => (p (σ r) ⟨r, rfl⟩).1
      invFun := fun r => ((p (σ r))⁻¹ ⟨r, rfl⟩).1
      left_inv := fun r => by
        dsimp only
        have hσ : σ ((p (σ r) ⟨r, rfl⟩).1) = σ r := (p (σ r) ⟨r, rfl⟩).2
        have hcast : ∀ {ρ₁ ρ₂ : ΛF} (h : ρ₁ = ρ₂) (a : Fin n) (ha : σ a = ρ₁) (hb : σ a = ρ₂),
            ((p ρ₂)⁻¹ ⟨a, hb⟩).1 = ((p ρ₁)⁻¹ ⟨a, ha⟩).1 := fun h a ha hb => by subst h; rfl
        rw [hcast hσ.symm _ hσ rfl]
        simp
      right_inv := fun r => by
        dsimp only
        have hσ : σ (((p (σ r))⁻¹ ⟨r, rfl⟩).1) = σ r := ((p (σ r))⁻¹ ⟨r, rfl⟩).2
        have hcast : ∀ {ρ₁ ρ₂ : ΛF} (h : ρ₁ = ρ₂) (a : Fin n) (ha : σ a = ρ₁) (hb : σ a = ρ₂),
            (p ρ₂ ⟨a, hb⟩).1 = (p ρ₁ ⟨a, ha⟩).1 := fun h a ha hb => by subst h; rfl
        rw [hcast hσ.symm _ hσ rfl]
        simp }
  have hx : WreathProduct.inr π ∈ inertiaW (F := F) σ := fun r => by
    change σ (π.symm r) = σ r
    exact ((p (σ r))⁻¹ ⟨r, rfl⟩).2
  refine ⟨⟨WreathProduct.inr π, hx⟩, ?_⟩
  ext ρ i
  have hpi : ∀ r : block σ ρ, π r.1 = (p ρ r).1 := fun ⟨r, hr⟩ => by
    change (p (σ r) ⟨r, rfl⟩).1 = (p ρ ⟨r, hr⟩).1
    subst hr; rfl
  have h1 : (blockHom (F := F) σ ⟨WreathProduct.inr π, hx⟩ ρ) i =
      (e ρ).symm ⟨π ((e ρ i).1), (inertiaW_apply ⟨WreathProduct.inr π, hx⟩ (e ρ i).1).trans (e ρ i).2⟩ :=
    rfl
  rw [h1]
  have h2 : (⟨π ((e ρ i).1), (inertiaW_apply ⟨WreathProduct.inr π, hx⟩ (e ρ i).1).trans (e ρ i).2⟩ :
      block σ ρ) = p ρ (e ρ i) := Subtype.ext (hpi (e ρ i))
  rw [h2]
  simp [p]

lemma littleRep_eq_prodRep {F : Type} [Group F] {n : ℕ}
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF]
    {BS : ∀ m, Nat.Partition m → Type} [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (σ : Fin n → ΛF) (ν : ∀ ρ, Nat.Partition (Fintype.card (block σ ρ)))
    (x : inertiaW (F := F) σ) :
    littleRep RS σ ν x =
      prodRep (fun ρ => RS (Fintype.card (block σ ρ))) ν (blockHom (F := F) σ x) := rfl

lemma isUnitaryRep_congr {G ι : Type} [Monoid G]
    {instF₁ instF₂ : Fintype ι} {instD₁ instD₂ : DecidableEq ι}
    {R : G → Matrix ι ι ℂ}
    (h : @IsUnitaryRep G ι _ instF₁ instD₁ R) :
    @IsUnitaryRep G ι _ instF₂ instD₂ R := by
  obtain rfl : instF₁ = instF₂ := Subsingleton.elim _ _
  obtain rfl : instD₁ = instD₂ := Subsingleton.elim _ _
  exact h

lemma isUnitaryRep_littleRep {F : Type} [Group F] {n : ℕ}
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF]
    {BS : ∀ m, Nat.Partition m → Type} [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (hRS : ∀ m, IsIrrepSystem (RS m))
    (σ : Fin n → ΛF) (ν : ∀ ρ, Nat.Partition (Fintype.card (block σ ρ))) :
    IsUnitaryRep (littleRep (F := F) RS σ ν) := by
  have hu0 := isUnitaryRep_prodRep (fun ρ => RS (Fintype.card (block σ ρ))) ν
    fun ρ => (hRS _).1 (ν ρ)
  have hu : IsUnitaryRep (prodRep (fun ρ => RS (Fintype.card (block σ ρ))) ν) :=
    isUnitaryRep_congr hu0
  refine ⟨⟨?_, ?_⟩, fun x => ?_⟩
  · simp [littleRep_eq_prodRep, hu.1.1]
  · intro x y
    simp only [littleRep_eq_prodRep, map_mul]
    exact hu.1.2 _ _
  · simp only [littleRep_eq_prodRep]
    exact hu.2 _

lemma littleRep_mul_baseGroup {F : Type} [Group F] {n : ℕ}
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF]
    {BS : ∀ m, Nat.Partition m → Type} [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (σ : Fin n → ΛF) (ν : ∀ ρ, Nat.Partition (Fintype.card (block σ ρ)))
    (k : inertiaW (F := F) σ) {m : WP F n} (hm : m ∈ baseGroup F n) :
    littleRep RS σ ν (k * ⟨m, baseGroup_le_inertiaW σ hm⟩) = littleRep RS σ ν k := by
  have hker : (⟨m, baseGroup_le_inertiaW σ hm⟩ : inertiaW (F := F) σ) ∈ (blockHom (F := F) σ).ker := by
    rw [blockHom_ker, Subgroup.mem_subgroupOf]
    exact hm
  rw [littleRep_eq_prodRep, littleRep_eq_prodRep, map_mul, (MonoidHom.mem_ker.mp hker), mul_one]

lemma charInner_littleRep {F : Type} [Group F] [Fintype F] {n : ℕ}
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF]
    {BS : ∀ m, Nat.Partition m → Type} [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (hRS : ∀ m, IsIrrepSystem (RS m))
    (σ : Fin n → ΛF) (ν ν' : ∀ ρ, Nat.Partition (Fintype.card (block σ ρ))) :
    charInner (littleRep (F := F) RS σ ν) (littleRep (F := F) RS σ ν') =
      if ν = ν' then 1 else 0 := by
  let φ := blockHom (F := F) σ
  let H := ∀ ρ, Equiv.Perm (Fin (Fintype.card (block σ ρ)))
  let Pν := prodRep (fun ρ => RS (Fintype.card (block σ ρ))) ν
  let Pν' := prodRep (fun ρ => RS (Fintype.card (block σ ρ))) ν'
  have hfib : ∀ q : H,
      ∑ k ∈ Finset.univ.filter (fun k : inertiaW (F := F) σ => φ k = q),
        Matrix.trace (Pν (φ k)) * Matrix.trace (Pν' (φ k⁻¹)) =
      (Fintype.card φ.ker : ℂ) * (Matrix.trace (Pν q) * Matrix.trace (Pν' q⁻¹)) := fun q => by
    obtain ⟨k₀, rfl⟩ := blockHom_surjective (F := F) σ q
    have hcard : (Finset.univ.filter (fun k : inertiaW (F := F) σ => φ k = φ k₀)).card =
        Fintype.card φ.ker := by
      refine Finset.card_bij (fun k hk => ⟨k * k₀⁻¹, by
          rw [MonoidHom.mem_ker, map_mul, map_inv]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hk, mul_inv_cancel]⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ hab
        have h1 : a * k₀⁻¹ = b * k₀⁻¹ := congrArg Subtype.val hab
        exact mul_right_cancel h1
      · rintro ⟨u, hu⟩ _
        refine ⟨u * k₀, ?_, by apply Subtype.ext; simp [mul_assoc]⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, MonoidHom.mem_ker.mp hu,
          one_mul]
    have hconst : ∀ k ∈ Finset.univ.filter (fun k : inertiaW (F := F) σ => φ k = φ k₀),
        Matrix.trace (Pν (φ k)) * Matrix.trace (Pν' (φ k⁻¹)) =
          Matrix.trace (Pν (φ k₀)) * Matrix.trace (Pν' (φ k₀)⁻¹) := fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [hk, map_inv, hk]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul]
  have hcard_mul : Fintype.card (inertiaW (F := F) σ) = Fintype.card φ.ker * Fintype.card H := by
    have he := QuotientGroup.quotientKerEquivOfSurjective φ (blockHom_surjective (F := F) σ)
    rw [← Fintype.card_congr he.toEquiv]
    have hl := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hl
    rw [hl, mul_comm]
  simp only [charInner, littleRep_eq_prodRep]
  change ((Fintype.card (inertiaW (F := F) σ) : ℂ))⁻¹ *
      ∑ k : inertiaW (F := F) σ, Matrix.trace (Pν (φ k)) * Matrix.trace (Pν' (φ k⁻¹)) = _
  rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (fun _ _ => Finset.mem_univ _)]
  simp_rw [hfib, ← Finset.mul_sum, hcard_mul, Nat.cast_mul, mul_inv]
  have hker_ne : (Fintype.card φ.ker : ℂ) ≠ 0 := by
    have : Nonempty φ.ker := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc ((Fintype.card φ.ker : ℂ)⁻¹ * (Fintype.card H : ℂ)⁻¹) *
        ((Fintype.card φ.ker : ℂ) * ∑ q : H, Matrix.trace (Pν q) * Matrix.trace (Pν' q⁻¹))
      = (Fintype.card H : ℂ)⁻¹ * ((Fintype.card φ.ker : ℂ)⁻¹ * (Fintype.card φ.ker : ℂ)) *
          ∑ q : H, Matrix.trace (Pν q) * Matrix.trace (Pν' q⁻¹) := by ring
    _ = charInner Pν Pν' := by rw [inv_mul_cancel₀ hker_ne, mul_one]; rfl
    _ = if ν = ν' then 1 else 0 := by
        have hsys0 := isIrrepSystem_prodRep (fun ρ => RS (Fintype.card (block σ ρ)))
          (fun ρ => hRS _)
        have hsys : IsIrrepSystem (prodRep (fun ρ => RS (Fintype.card (block σ ρ)))) :=
          isIrrepSystem_congr (fun _ _ => rfl) hsys0
        have hch := isIrrepSystem_charInner hsys ν ν'
        by_cases hν : ν = ν'
        · rw [if_pos hν] at hch ⊢; exact hch
        · rw [if_neg hν] at hch ⊢; exact hch

/-! ### Section 5: Induced representations, Mackey character inner product, and dimension sum -/

lemma indRep_cond_existsUnique {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    (hT : Subgroup.IsComplement T (K : Set G)) (g : G) (t : T) :
    ∃! s : T, ((s : G)⁻¹ * g * (t : G)) ∈ K := by
  obtain ⟨⟨s, k⟩, hmul, huniq⟩ := hT.existsUnique (g * (t : G))
  refine ⟨s, ?_, ?_⟩
  · have hsk : (s : G) * (k : G) = g * (t : G) := hmul
    have heq : (s : G)⁻¹ * g * (t : G) = (k : G) := by
      rw [mul_assoc, ← hsk, inv_mul_cancel_left]
    dsimp only
    rw [heq]
    exact k.2
  · intro s' hs'
    have hmul' : (s' : G) * (⟨(s' : G)⁻¹ * g * (t : G), hs'⟩ : (K : Set G)).1 = g * (t : G) := by
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    exact congrArg Prod.fst (huniq ⟨s', ⟨_, hs'⟩⟩ hmul')

lemma isUnitaryRep_indRep {G : Type} [Group G] (K : Subgroup G) (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (K : Set G))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : K → Matrix ι ι ℂ} (hR : IsUnitaryRep R) :
    IsUnitaryRep (indRep K T R) := by
  have hm : IsMatRep (indRep K T R) := by
    constructor
    · ext ⟨s, j⟩ ⟨t, i⟩
      simp only [indRep, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff]
      by_cases hst : s = t
      · subst hst
        have h1 : ((s : G)⁻¹ * 1 * (s : G)) ∈ K := by simp [K.one_mem]
        rw [dif_pos h1]
        have hk1 : (⟨(s : G)⁻¹ * 1 * (s : G), h1⟩ : K) = 1 := by ext; simp
        rw [hk1, hR.1.1, Matrix.one_apply]
        simp
      · have hnot : ¬ ((s : G)⁻¹ * 1 * (t : G)) ∈ K := by
          intro hmem
          obtain ⟨u, _, huniq⟩ := indRep_cond_existsUnique K T hT 1 t
          have ht1 : ((t : G)⁻¹ * 1 * (t : G)) ∈ K := by simp [K.one_mem]
          exact hst ((huniq s hmem).trans (huniq t ht1).symm)
        rw [dif_neg hnot]
        simp [hst]
    · intro g₁ g₂
      ext ⟨s, j⟩ ⟨t, i⟩
      simp only [indRep, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type]
      obtain ⟨u₀, hu₀, hu₀_uniq⟩ := indRep_cond_existsUnique K T hT g₂ t
      rw [Finset.sum_eq_single u₀]
      · have hiff : ((s : G)⁻¹ * (g₁ * g₂) * (t : G)) ∈ K ↔ ((s : G)⁻¹ * g₁ * (u₀ : G)) ∈ K := by
          have hmul : (s : G)⁻¹ * (g₁ * g₂) * (t : G) =
              ((s : G)⁻¹ * g₁ * (u₀ : G)) * ((u₀ : G)⁻¹ * g₂ * (t : G)) := by group
          rw [hmul]
          exact K.mul_mem_cancel_right hu₀
        by_cases h1 : ((s : G)⁻¹ * g₁ * (u₀ : G)) ∈ K
        · have h12 : ((s : G)⁻¹ * (g₁ * g₂) * (t : G)) ∈ K := hiff.mpr h1
          simp only [dif_pos h12, dif_pos h1, dif_pos hu₀]
          have hmulK : (⟨(s : G)⁻¹ * (g₁ * g₂) * (t : G), h12⟩ : K) =
              ⟨(s : G)⁻¹ * g₁ * (u₀ : G), h1⟩ * ⟨(u₀ : G)⁻¹ * g₂ * (t : G), hu₀⟩ := by
            apply Subtype.ext
            change (s : G)⁻¹ * (g₁ * g₂) * (t : G) =
              ((s : G)⁻¹ * g₁ * (u₀ : G)) * ((u₀ : G)⁻¹ * g₂ * (t : G))
            group
          rw [hmulK, hR.1.2, Matrix.mul_apply]
        · have h12 : ¬ ((s : G)⁻¹ * (g₁ * g₂) * (t : G)) ∈ K := fun h => h1 (hiff.mp h)
          simp only [dif_neg h12, dif_neg h1]
          simp
      · intro u _ hu
        have hnot : ¬ ((u : G)⁻¹ * g₂ * (t : G)) ∈ K := fun h => hu (hu₀_uniq u h)
        simp only [dif_neg hnot]
        simp
      · intro hu₀mem; exact (hu₀mem (Finset.mem_univ u₀)).elim
  refine ⟨hm, fun g => ?_⟩
  have hconj : (indRep K T R g)ᴴ = indRep K T R g⁻¹ := by
    ext ⟨s, j⟩ ⟨t, i⟩
    simp only [Matrix.conjTranspose_apply, indRep, Matrix.of_apply]
    have hiff : ((t : G)⁻¹ * g * (s : G)) ∈ K ↔ ((s : G)⁻¹ * g⁻¹ * (t : G)) ∈ K := by
      have hinv : ((t : G)⁻¹ * g * (s : G))⁻¹ = (s : G)⁻¹ * g⁻¹ * (t : G) := by group
      rw [← hinv, K.inv_mem_iff]
    by_cases h : ((s : G)⁻¹ * g⁻¹ * (t : G)) ∈ K
    · have h' : ((t : G)⁻¹ * g * (s : G)) ∈ K := hiff.mpr h
      rw [dif_pos h', dif_pos h]
      have hk : (⟨(t : G)⁻¹ * g * (s : G), h'⟩ : K)⁻¹ = ⟨(s : G)⁻¹ * g⁻¹ * (t : G), h⟩ := by
        apply Subtype.ext
        change ((t : G)⁻¹ * g * (s : G))⁻¹ = (s : G)⁻¹ * g⁻¹ * (t : G)
        group
      change ((R ⟨_, h'⟩)ᴴ) j i = R ⟨_, h⟩ j i
      rw [← isUnitaryRep_inv_eq_conjTranspose hR, hk]
    · have h' : ¬ ((t : G)⁻¹ * g * (s : G)) ∈ K := fun hh => h (hiff.mp hh)
      rw [dif_neg h', dif_neg h, star_zero]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hconj]
  exact isMatRep_mul_inv hm g

def complementEquiv {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    (hT : Subgroup.IsComplement T (K : Set G)) : T × K ≃ G :=
  Equiv.ofBijective (fun p => (p.1 : G) * (p.2 : G))
    ⟨fun a b hab => by
      obtain ⟨⟨p₀, _⟩, _, huniq⟩ := hT.existsUnique ((a.1 : G) * (a.2 : G))
      have ha := huniq ⟨a.1, ⟨a.2.1, a.2.2⟩⟩ rfl
      have hb := huniq ⟨b.1, ⟨b.2.1, b.2.2⟩⟩ hab.symm
      have heq := ha.trans hb.symm
      ext
      · exact congrArg (fun q => (q.1 : G)) heq
      · exact congrArg (fun q => (q.2 : G)) heq,
     fun g => by
      obtain ⟨⟨t, k⟩, hmul, _⟩ := hT.existsUnique g
      exact ⟨(t, ⟨k.1, k.2⟩), hmul⟩⟩

lemma card_mul_trace_indRep {G : Type} [Group G] [Fintype G]
    (K : Subgroup G) (T : Set G) (hT : Subgroup.IsComplement T (K : Set G))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : K → Matrix ι ι ℂ) (hR : IsMatRep R) (g : G) :
    (Fintype.card K : ℂ) * Matrix.trace (indRep K T R g) =
      ∑ x : G, if hx : x⁻¹ * g * x ∈ K then Matrix.trace (R ⟨x⁻¹ * g * x, hx⟩) else 0 := by
  have htr : Matrix.trace (indRep K T R g) =
      ∑ t : T, if ht : ((t : G)⁻¹ * g * (t : G)) ∈ K then
        Matrix.trace (R ⟨(t : G)⁻¹ * g * (t : G), ht⟩) else 0 := by
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, indRep, Matrix.of_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with ht
    · rfl
    · simp
  have hsum_k : (Fintype.card K : ℂ) *
      (∑ t : T, if ht : ((t : G)⁻¹ * g * (t : G)) ∈ K then
        Matrix.trace (R ⟨(t : G)⁻¹ * g * (t : G), ht⟩) else 0) =
      ∑ p : T × K, if ht : ((p.1 : G)⁻¹ * g * (p.1 : G)) ∈ K then
        Matrix.trace (R ⟨(p.1 : G)⁻¹ * g * (p.1 : G), ht⟩) else 0 := by
    have htr_const : ∀ b : ℂ, (Fintype.card K : ℂ) * b = ∑ _y : K, b := fun b => by
      symm; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    convert htr_const _
  rw [htr, hsum_k]
  let e := complementEquiv K T hT
  symm
  refine Fintype.sum_equiv e.symm _ _ fun x => ?_
  have hx_eq : ((e.symm x).1 : G) * ((e.symm x).2 : G) = x := e.apply_symm_apply x
  let t := (e.symm x).1
  let k := (e.symm x).2
  change (if hx : x⁻¹ * g * x ∈ K then Matrix.trace (R ⟨x⁻¹ * g * x, hx⟩) else 0) =
    if ht : ((t : G)⁻¹ * g * (t : G)) ∈ K then Matrix.trace (R ⟨(t : G)⁻¹ * g * (t : G), ht⟩) else 0
  have hiff : x⁻¹ * g * x ∈ K ↔ ((t : G)⁻¹ * g * (t : G)) ∈ K := by
    have hconj : x⁻¹ * g * x = (k : G)⁻¹ * ((t : G)⁻¹ * g * (t : G)) * (k : G) := by
      conv_lhs => rw [← hx_eq]
      dsimp only [t, k]; group
    rw [hconj, mul_assoc, Subgroup.mul_mem_cancel_left _ (K.inv_mem k.2),
      Subgroup.mul_mem_cancel_right _ k.2]
  by_cases hx : x⁻¹ * g * x ∈ K
  · have ht : ((t : G)⁻¹ * g * (t : G)) ∈ K := hiff.mp hx
    rw [dif_pos hx, dif_pos ht]
    have hconjK : (⟨x⁻¹ * g * x, hx⟩ : K) = k⁻¹ * ⟨(t : G)⁻¹ * g * (t : G), ht⟩ * k := by
      apply Subtype.ext
      change x⁻¹ * g * x = (k : G)⁻¹ * ((t : G)⁻¹ * g * (t : G)) * (k : G)
      conv_lhs => rw [← hx_eq]
      dsimp only [t, k]; group
    rw [hconjK, hR.2, hR.2, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      isMatRep_mul_inv hR k, Matrix.one_mul]
  · have ht : ¬ ((t : G)⁻¹ * g * (t : G)) ∈ K := fun h => hx (hiff.mpr h)
    rw [dif_neg hx, dif_neg ht]

lemma card_mul_charInner_indRep {G : Type} [Group G] [Fintype G]
    (K₁ K₂ : Subgroup G) (T₁ T₂ : Set G)
    (hT₁ : Subgroup.IsComplement T₁ (K₁ : Set G)) (hT₂ : Subgroup.IsComplement T₂ (K₂ : Set G))
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (R₁ : K₁ → Matrix ι₁ ι₁ ℂ) (R₂ : K₂ → Matrix ι₂ ι₂ ℂ)
    (hR₁ : IsMatRep R₁) (hR₂ : IsMatRep R₂) :
    (Fintype.card K₁ : ℂ) * (Fintype.card K₂ : ℂ) *
        charInner (indRep K₁ T₁ R₁) (indRep K₂ T₂ R₂) =
      ∑ z : G, ∑ k₁ : K₁,
        if hz : z⁻¹ * (k₁ : G) * z ∈ K₂ then
          Matrix.trace (R₁ k₁) * Matrix.trace (R₂ (⟨z⁻¹ * (k₁ : G) * z, hz⟩)⁻¹)
        else 0 := by
  have hG_ne : (Fintype.card G : ℂ) ≠ 0 := by
    have : Nonempty G := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [charInner]
  calc (Fintype.card K₁ : ℂ) * (Fintype.card K₂ : ℂ) *
        (((Fintype.card G : ℂ))⁻¹ * ∑ g : G,
          Matrix.trace (indRep K₁ T₁ R₁ g) * Matrix.trace (indRep K₂ T₂ R₂ g⁻¹))
      = ((Fintype.card G : ℂ))⁻¹ * ∑ g : G,
          ((Fintype.card K₁ : ℂ) * Matrix.trace (indRep K₁ T₁ R₁ g)) *
          ((Fintype.card K₂ : ℂ) * Matrix.trace (indRep K₂ T₂ R₂ g⁻¹)) := by
          rw [Finset.mul_sum]; rw [Finset.mul_sum]; ring_nf
          simp_rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => by ring
    _ = ((Fintype.card G : ℂ))⁻¹ * ∑ g : G,
          (∑ x : G, if hx : x⁻¹ * g * x ∈ K₁ then Matrix.trace (R₁ ⟨x⁻¹ * g * x, hx⟩) else 0) *
          (∑ y : G, if hy : y⁻¹ * g⁻¹ * y ∈ K₂ then Matrix.trace (R₂ ⟨y⁻¹ * g⁻¹ * y, hy⟩) else 0) := by
          congr 1
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [card_mul_trace_indRep K₁ T₁ hT₁ R₁ hR₁ g,
            card_mul_trace_indRep K₂ T₂ hT₂ R₂ hR₂ g⁻¹]
    _ = ((Fintype.card G : ℂ))⁻¹ * ∑ x : G, ∑ y : G, ∑ g : G,
          (if hx : x⁻¹ * g * x ∈ K₁ then Matrix.trace (R₁ ⟨x⁻¹ * g * x, hx⟩) else 0) *
          (if hy : y⁻¹ * g⁻¹ * y ∈ K₂ then Matrix.trace (R₂ ⟨y⁻¹ * g⁻¹ * y, hy⟩) else 0) := by
          congr 1
          simp_rw [Finset.sum_mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ((Fintype.card G : ℂ))⁻¹ * ∑ x : G, ∑ y : G, ∑ k₁ : K₁,
          if hz : (x⁻¹ * y)⁻¹ * (k₁ : G) * (x⁻¹ * y) ∈ K₂ then
            Matrix.trace (R₁ k₁) *
              Matrix.trace (R₂ (⟨(x⁻¹ * y)⁻¹ * (k₁ : G) * (x⁻¹ * y), hz⟩)⁻¹)
          else 0 := by
          congr 1
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          let c : G ≃ G := (MulAut.conj x⁻¹).toEquiv
          have hc : ∑ g : G,
              (if hx : x⁻¹ * g * x ∈ K₁ then Matrix.trace (R₁ ⟨x⁻¹ * g * x, hx⟩) else 0) *
              (if hy : y⁻¹ * g⁻¹ * y ∈ K₂ then Matrix.trace (R₂ ⟨y⁻¹ * g⁻¹ * y, hy⟩) else 0) =
              ∑ k : G,
                (if hk : k ∈ K₁ then Matrix.trace (R₁ ⟨k, hk⟩) else 0) *
                (if hy : (x⁻¹ * y)⁻¹ * k⁻¹ * (x⁻¹ * y) ∈ K₂ then
                  Matrix.trace (R₂ ⟨(x⁻¹ * y)⁻¹ * k⁻¹ * (x⁻¹ * y), hy⟩) else 0) := by
            refine Fintype.sum_equiv c _ _ fun g => ?_
            have hcg : c g = x⁻¹ * g * x := by simp [c, MulAut.conj_apply]
            have hconj2 : y⁻¹ * g⁻¹ * y = (x⁻¹ * y)⁻¹ * (c g)⁻¹ * (x⁻¹ * y) := by
              rw [hcg]; group
            rw [← hcg, ← hconj2]
          rw [hc, ← Finset.sum_filter_of_ne (p := fun k : G => k ∈ K₁) (fun k _ hk => by
              by_contra hmem; apply hk; rw [dif_neg hmem, zero_mul])]
          refine Finset.sum_bij (fun k hk => (⟨k, (Finset.mem_filter.mp hk).2⟩ : K₁))
            (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ hab => congrArg Subtype.val hab)
            (fun k₁ _ => ⟨k₁.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k₁.2⟩, rfl⟩)
            fun k hk => ?_
          have hkK : k ∈ K₁ := (Finset.mem_filter.mp hk).2
          rw [dif_pos hkK]
          change Matrix.trace (R₁ ⟨k, hkK⟩) *
              (if hy : (x⁻¹ * y)⁻¹ * k⁻¹ * (x⁻¹ * y) ∈ K₂ then
                Matrix.trace (R₂ ⟨(x⁻¹ * y)⁻¹ * k⁻¹ * (x⁻¹ * y), hy⟩) else 0) =
              if hz : (x⁻¹ * y)⁻¹ * k * (x⁻¹ * y) ∈ K₂ then
                Matrix.trace (R₁ ⟨k, hkK⟩) * Matrix.trace (R₂ (⟨(x⁻¹ * y)⁻¹ * k * (x⁻¹ * y), hz⟩)⁻¹)
              else 0
          have hiff2 : (x⁻¹ * y)⁻¹ * k⁻¹ * (x⁻¹ * y) ∈ K₂ ↔
              (x⁻¹ * y)⁻¹ * k * (x⁻¹ * y) ∈ K₂ := by
            have hinv : ((x⁻¹ * y)⁻¹ * k * (x⁻¹ * y))⁻¹ =
                (x⁻¹ * y)⁻¹ * k⁻¹ * (x⁻¹ * y) := by group
            rw [← hinv, K₂.inv_mem_iff]
          by_cases hz : (x⁻¹ * y)⁻¹ * k * (x⁻¹ * y) ∈ K₂
          · have hy : (x⁻¹ * y)⁻¹ * k⁻¹ * (x⁻¹ * y) ∈ K₂ := hiff2.mpr hz
            rw [dif_pos hy, dif_pos hz]
            congr 2
            exact congrArg R₂ (Subtype.ext (by
              change (x⁻¹ * y)⁻¹ * k⁻¹ * (x⁻¹ * y) = ↑((⟨(x⁻¹ * y)⁻¹ * k * (x⁻¹ * y), hz⟩ : K₂)⁻¹)
              simp only [Subgroup.coe_inv]
              group))
          · have hy : ¬ (x⁻¹ * y)⁻¹ * k⁻¹ * (x⁻¹ * y) ∈ K₂ := fun h => hz (hiff2.mp h)
            rw [dif_neg hy, dif_neg hz, mul_zero]
    _ = ∑ z : G, ∑ k₁ : K₁,
          if hz : z⁻¹ * (k₁ : G) * z ∈ K₂ then
            Matrix.trace (R₁ k₁) * Matrix.trace (R₂ (⟨z⁻¹ * (k₁ : G) * z, hz⟩)⁻¹)
          else 0 := by
          have hxy : ∀ x : G, (∑ y : G, ∑ k₁ : K₁,
              if hz : (x⁻¹ * y)⁻¹ * (k₁ : G) * (x⁻¹ * y) ∈ K₂ then
                Matrix.trace (R₁ k₁) *
                  Matrix.trace (R₂ (⟨(x⁻¹ * y)⁻¹ * (k₁ : G) * (x⁻¹ * y), hz⟩)⁻¹)
              else 0) =
              ∑ z : G, ∑ k₁ : K₁,
                if hz : z⁻¹ * (k₁ : G) * z ∈ K₂ then
                  Matrix.trace (R₁ k₁) * Matrix.trace (R₂ (⟨z⁻¹ * (k₁ : G) * z, hz⟩)⁻¹)
                else 0 := fun x =>
            Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ fun y => rfl
          simp_rw [hxy, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
            ← smul_eq_mul, smul_smul, inv_mul_cancel₀ hG_ne, one_smul]

lemma sum_trace_mul_eq {G ι₁ ι₂ : Type} [Group G] [Fintype G]
    [Fintype ι₁] [Fintype ι₂]
    (R₁ : G → Matrix ι₁ ι₁ ℂ) (R₂ : G → Matrix ι₂ ι₂ ℂ)
    (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) :
    ∑ g : G, Matrix.trace (A * R₁ g) * Matrix.trace (B * R₂ g⁻¹) =
      ∑ a : ι₁, ∑ b : ι₁, ∑ c : ι₂, ∑ d : ι₂,
        (A a b * B c d) * ∑ g : G, R₁ g b a * R₂ g⁻¹ d c := by
  have hexp : ∀ g : G, Matrix.trace (A * R₁ g) * Matrix.trace (B * R₂ g⁻¹) =
      ∑ a : ι₁, ∑ b : ι₁, ∑ c : ι₂, ∑ d : ι₂,
        (A a b * B c d) * (R₁ g b a * R₂ g⁻¹ d c) := fun g => by
    calc Matrix.trace (A * R₁ g) * Matrix.trace (B * R₂ g⁻¹)
        = (∑ a : ι₁, ∑ b : ι₁, A a b * R₁ g b a) *
          (∑ c : ι₂, ∑ d : ι₂, B c d * R₂ g⁻¹ d c) := by
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      _ = ∑ a : ι₁, ∑ b : ι₁, ∑ c : ι₂, ∑ d : ι₂,
            (A a b * B c d) * (R₁ g b a * R₂ g⁻¹ d c) := by
          simp_rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => by ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum]

lemma sum_trace_mul_eq_zero_of_not_repEquiv {G ι₁ ι₂ : Type} [Group G] [Fintype G]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (hm₁ : IsMatRep R₁) (hm₂ : IsMatRep R₂)
    (hi₁ : IsIrreducibleRep R₁) (hi₂ : IsIrreducibleRep R₂)
    (hne : ¬ RepEquiv R₁ R₂) (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) :
    ∑ g : G, Matrix.trace (A * R₁ g) * Matrix.trace (B * R₂ g⁻¹) = 0 := by
  have hG_ne : (Fintype.card G : ℂ) ≠ 0 := by
    have : Nonempty G := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_trace_mul_eq]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  have h0 := schur_entry_ortho_ne hm₂ hm₁ hi₂ hi₁ (fun h => hne (repEquiv_symm h)) b a d c
  have hsum0 : ∑ g : G, R₁ g b a * R₂ g⁻¹ d c = 0 := (mul_eq_zero.mp h0).resolve_left (inv_ne_zero hG_ne)
  rw [hsum0, mul_zero]

lemma avg_trace_mul_eq_trace_mul {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hm : IsMatRep R) (hi : IsIrreducibleRep R)
    (A B : Matrix ι ι ℂ) :
    ((Fintype.card G : ℂ))⁻¹ * ∑ g : G, Matrix.trace (A * R g) * Matrix.trace (B * R g⁻¹) =
      ((Fintype.card ι : ℂ))⁻¹ * Matrix.trace (A * B) := by
  rw [sum_trace_mul_eq]
  have htr : Matrix.trace (A * B) = ∑ a : ι, ∑ b : ι, A a b * B b a := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [htr, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hassoc : ∀ (a b c d : ι),
      ((Fintype.card G : ℂ))⁻¹ * ((A a b * B c d) * ∑ g : G, R g b a * R g⁻¹ d c) =
      (A a b * B c d) * (((Fintype.card G : ℂ))⁻¹ * ∑ g : G, R g b a * R g⁻¹ d c) := fun _ _ _ _ => by ring
  rw [Finset.mul_sum, Finset.sum_eq_single b]
  · rw [Finset.mul_sum, Finset.sum_eq_single a]
    · rw [hassoc a b b a, schur_entry_ortho_eq hm hi b a a b, if_pos ⟨rfl, rfl⟩]
      ring
    · intro d _ hda
      rw [hassoc a b b d, schur_entry_ortho_eq hm hi b a d b, if_neg (fun h => hda h.1.symm), mul_zero]
    · intro ha; exact (ha (Finset.mem_univ a)).elim
  · intro c _ hcb
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [hassoc a b c d, schur_entry_ortho_eq hm hi b a d c, if_neg (fun h => hcb h.2.symm), mul_zero]
  · intro hb; exact (hb (Finset.mem_univ b)).elim

lemma charInner_phi_aux {F : Type} [Group F] [Fintype F] {n : ℕ}
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF] {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)]
    [∀ ρ, DecidableEq (BF ρ)] (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (hRF : IsIrrepSystem RF)
    {BS : ∀ m, Nat.Partition m → Type} [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (hRS : ∀ m, IsIrrepSystem (RS m))
    (T : (Fin n → ΛF) → Set (WP F n))
    (σ₁ σ₂ : Fin n → ΛF) (hσ₁ : Antitone σ₁) (hσ₂ : Antitone σ₂)
    (hT₁ : Subgroup.IsComplement (T σ₁) (inertiaW (F := F) σ₁ : Set (WP F n)))
    (hT₂ : Subgroup.IsComplement (T σ₂) (inertiaW (F := F) σ₂ : Set (WP F n)))
    (ν₁ : ∀ ρ, Nat.Partition (Fintype.card (block σ₁ ρ)))
    (ν₂ : ∀ ρ, Nat.Partition (Fintype.card (block σ₂ ρ)))
    (z : WP F n) (hz_not : ¬ (σ₁ = σ₂ ∧ z ∈ inertiaW (F := F) σ₁)) :
    (∑ k₁ : inertiaW (F := F) σ₁,
      if hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ then
        Matrix.trace (Matrix.kronecker (extRep RF σ₁ k₁) (littleRep RS σ₁ ν₁ k₁)) *
        Matrix.trace (Matrix.kronecker (extRep RF σ₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)
          (littleRep RS σ₂ ν₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹))
      else 0) = 0 := by
  have hnot_eqv : ¬ RepEquiv (baseRep (F := F) RF σ₁)
      (transport (baseGroup F n) (baseRep RF σ₂) z) := by
    intro hrep
    have heq := transport_baseRep_repEquiv RF hRF z σ₂
    have hrep' := repEquiv_trans hrep (repEquiv_symm heq)
    have hirr := isIrrepSystem_baseRep (F := F) (n := n) hRF
    have hl : σ₁ = fun s => σ₂ (z.right⁻¹ s) := by
      by_contra hne
      exact hirr.2.2.1 _ _ hne hrep'
    have hσeq : σ₁ = σ₂ := (antitone_orbit_unique hσ₂ hσ₁ z.right hl).symm
    subst hσeq
    have hzmem : z ∈ inertiaW (F := F) σ₁ := fun r => (congr_fun hl r).symm
    exact hz_not ⟨rfl, hzmem⟩
  have hbase_ne : (Fintype.card (baseGroup F n) : ℂ) ≠ 0 := by
    have : Nonempty (baseGroup F n) := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  suffices hmul : (Fintype.card (baseGroup F n) : ℂ) *
      (∑ k₁ : inertiaW (F := F) σ₁,
        if hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ then
          Matrix.trace (Matrix.kronecker (extRep RF σ₁ k₁) (littleRep RS σ₁ ν₁ k₁)) *
          Matrix.trace (Matrix.kronecker (extRep RF σ₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)
            (littleRep RS σ₂ ν₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹))
        else 0) = 0 by
    exact (mul_eq_zero.mp hmul).resolve_left hbase_ne
  have hshift : ∀ m : baseGroup F n,
      (∑ k₁ : inertiaW (F := F) σ₁,
        if hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ then
          Matrix.trace (Matrix.kronecker (extRep RF σ₁ k₁) (littleRep RS σ₁ ν₁ k₁)) *
          Matrix.trace (Matrix.kronecker (extRep RF σ₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)
            (littleRep RS σ₂ ν₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹))
        else 0) =
      ∑ k₁ : inertiaW (F := F) σ₁,
        if hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ then
          (Matrix.trace (littleRep RS σ₁ ν₁ k₁) *
            Matrix.trace (littleRep RS σ₂ ν₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)) *
          (Matrix.trace (extRep RF σ₁ k₁ * baseRep RF σ₁ m) *
            Matrix.trace (extRep RF σ₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹ *
              transport (baseGroup F n) (baseRep RF σ₂) z m⁻¹))
        else 0 := fun m => by
    let mI : inertiaW (F := F) σ₁ := ⟨m.1, baseGroup_le_inertiaW σ₁ m.2⟩
    symm
    refine Fintype.sum_equiv (Equiv.mulRight mI) _ _ fun k₁ => ?_
    have hmul_app : (Equiv.mulRight mI) k₁ = k₁ * mI := rfl
    simp only [hmul_app]
    have hm_norm : z⁻¹ * (m : WP F n) * z ∈ baseGroup F n :=
      conj_inv_mem (baseGroup F n) z m
    have hm_I2 : z⁻¹ * (m : WP F n) * z ∈ inertiaW (F := F) σ₂ :=
      baseGroup_le_inertiaW σ₂ hm_norm
    have hiff : z⁻¹ * ((k₁ * mI : inertiaW (F := F) σ₁) : WP F n) * z ∈ inertiaW (F := F) σ₂ ↔
        z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ := by
      have hmul : z⁻¹ * ((k₁ * mI : inertiaW (F := F) σ₁) : WP F n) * z =
          (z⁻¹ * (k₁ : WP F n) * z) * (z⁻¹ * (m : WP F n) * z) := by
        change z⁻¹ * ((k₁ : WP F n) * (m : WP F n)) * z = _; group
      rw [hmul]
      exact (inertiaW (F := F) σ₂).mul_mem_cancel_right hm_I2
    by_cases hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂
    · have hz' := hiff.mpr hz
      rw [dif_pos hz, dif_pos hz']
      have he1 := isUnitaryRep_extRep (F := F) RF hRF σ₁
      have he2 := isUnitaryRep_extRep (F := F) RF hRF σ₂
      have hm1 : extRep RF σ₁ (k₁ * mI) = extRep RF σ₁ k₁ * baseRep RF σ₁ m := by
        rw [he1.1.2, extRep_mem_baseGroup RF σ₁ m.2 mI.2]
      have hl1 : littleRep RS σ₁ ν₁ (k₁ * mI) = littleRep RS σ₁ ν₁ k₁ :=
        littleRep_mul_baseGroup RS σ₁ ν₁ k₁ m.2
      let k₂ : inertiaW (F := F) σ₂ := ⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩
      let m₂ : inertiaW (F := F) σ₂ := ⟨z⁻¹ * (m : WP F n) * z, hm_I2⟩
      have hk2_eq : (⟨z⁻¹ * ((k₁ * mI : inertiaW (F := F) σ₁) : WP F n) * z, hz'⟩ :
          inertiaW (F := F) σ₂) = k₂ * m₂ := by
        apply Subtype.ext
        change z⁻¹ * ((k₁ : WP F n) * (m : WP F n)) * z =
          (z⁻¹ * (k₁ : WP F n) * z) * (z⁻¹ * (m : WP F n) * z)
        group
      have hm_norm_inv : ((m₂⁻¹ : inertiaW (F := F) σ₂) : WP F n) ∈ baseGroup F n := by
        change (z⁻¹ * (m : WP F n) * z)⁻¹ ∈ baseGroup F n
        exact (baseGroup F n).inv_mem hm_norm
      have hm2_inv : extRep RF σ₂ m₂⁻¹ = transport (baseGroup F n) (baseRep RF σ₂) z m⁻¹ := by
        trans baseRep RF σ₂ ⟨(m₂⁻¹ : WP F n), hm_norm_inv⟩
        · exact extRep_mem_baseGroup RF σ₂ hm_norm_inv m₂⁻¹.2
        · simp only [transport]
          congr 1
          apply Subtype.ext
          change (z⁻¹ * (m : WP F n) * z)⁻¹ = z⁻¹ * (m : WP F n)⁻¹ * z
          group
      have hk2_inv : extRep RF σ₂ (⟨z⁻¹ * ((k₁ * mI : inertiaW (F := F) σ₁) : WP F n) * z, hz'⟩)⁻¹ =
          extRep RF σ₂ m₂⁻¹ * extRep RF σ₂ k₂⁻¹ := by
        rw [hk2_eq, mul_inv_rev, he2.1.2]
      have hl2 : littleRep RS σ₂ ν₂
          (⟨z⁻¹ * ((k₁ * mI : inertiaW (F := F) σ₁) : WP F n) * z, hz'⟩)⁻¹ =
          littleRep RS σ₂ ν₂ k₂⁻¹ := by
        rw [hk2_eq, mul_inv_rev, littleRep_eq_prodRep, littleRep_eq_prodRep, map_mul]
        have hker : m₂⁻¹ ∈ (blockHom (F := F) σ₂).ker := by
          rw [blockHom_ker, Subgroup.mem_subgroupOf]
          exact hm_norm_inv
        rw [MonoidHom.mem_ker.mp hker, one_mul]
      rw [hm1, hl1, hk2_inv, hl2, trace_kronecker, trace_kronecker, hm2_inv,
        Matrix.trace_mul_comm (transport (baseGroup F n) (baseRep RF σ₂) z m⁻¹) (extRep RF σ₂ k₂⁻¹)]
      ring
    · rw [dif_neg hz, dif_neg (fun h => hz (hiff.mp h))]
  have hirr := isIrrepSystem_baseRep (F := F) (n := n) hRF
  have hm₁ : IsMatRep (baseRep (F := F) RF σ₁) := (hirr.1 σ₁).1
  have hi₁ : IsIrreducibleRep (baseRep (F := F) RF σ₁) := hirr.2.1 σ₁
  have hmT : IsMatRep (transport (baseGroup F n) (baseRep RF σ₂) z) := by
    refine ⟨?_, fun x y => ?_⟩
    · simp only [transport]
      convert (hirr.1 σ₂).1.1
      simp
    · simp only [transport]
      rw [← (hirr.1 σ₂).1.2]
      congr 1
      apply Subtype.ext
      change z⁻¹ * ((x : WP F n) * (y : WP F n)) * z =
        (z⁻¹ * (x : WP F n) * z) * (z⁻¹ * (y : WP F n) * z)
      group
  have hiT : IsIrreducibleRep (transport (baseGroup F n) (baseRep RF σ₂) z) := by
    refine ⟨(hirr.2.1 σ₂).1, fun W hW => (hirr.2.1 σ₂).2 W fun y v hv => ?_⟩
    have hy : z * (y : WP F n) * z⁻¹ ∈ baseGroup F n := by
      rw [mem_baseGroup_iff]
      simp only [WreathProduct.mul_right, WreathProduct.inv_right, mem_baseGroup_iff.mp y.2,
        mul_one, mul_inv_cancel]
    have hW' := hW ⟨z * (y : WP F n) * z⁻¹, hy⟩ v hv
    have heq : transport (baseGroup F n) (baseRep RF σ₂) z ⟨z * (y : WP F n) * z⁻¹, hy⟩ =
        baseRep RF σ₂ y := by
      simp only [transport]
      congr 1
      apply Subtype.ext
      change z⁻¹ * (z * (y : WP F n) * z⁻¹) * z = (y : WP F n)
      group
    rwa [heq] at hW'
  calc (Fintype.card (baseGroup F n) : ℂ) *
        (∑ k₁ : inertiaW (F := F) σ₁,
          if hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ then
            Matrix.trace (Matrix.kronecker (extRep RF σ₁ k₁) (littleRep RS σ₁ ν₁ k₁)) *
            Matrix.trace (Matrix.kronecker (extRep RF σ₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)
              (littleRep RS σ₂ ν₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹))
          else 0)
      = ∑ _m : baseGroup F n, ∑ k₁ : inertiaW (F := F) σ₁,
          if hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ then
            Matrix.trace (Matrix.kronecker (extRep RF σ₁ k₁) (littleRep RS σ₁ ν₁ k₁)) *
            Matrix.trace (Matrix.kronecker (extRep RF σ₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)
              (littleRep RS σ₂ ν₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹))
          else 0 := by
            symm
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ m : baseGroup F n, ∑ k₁ : inertiaW (F := F) σ₁,
          if hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ then
            (Matrix.trace (littleRep RS σ₁ ν₁ k₁) *
              Matrix.trace (littleRep RS σ₂ ν₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)) *
            (Matrix.trace (extRep RF σ₁ k₁ * baseRep RF σ₁ m) *
              Matrix.trace (extRep RF σ₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹ *
                transport (baseGroup F n) (baseRep RF σ₂) z m⁻¹))
          else 0 := Finset.sum_congr rfl fun m _ => hshift m
    _ = ∑ k₁ : inertiaW (F := F) σ₁, ∑ m : baseGroup F n,
          if hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ then
            (Matrix.trace (littleRep RS σ₁ ν₁ k₁) *
              Matrix.trace (littleRep RS σ₂ ν₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)) *
            (Matrix.trace (extRep RF σ₁ k₁ * baseRep RF σ₁ m) *
              Matrix.trace (extRep RF σ₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹ *
                transport (baseGroup F n) (baseRep RF σ₂) z m⁻¹))
          else 0 := Finset.sum_comm
    _ = 0 := by
          refine Finset.sum_eq_zero fun k₁ _ => ?_
          by_cases hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂
          · simp only [dif_pos hz, ← Finset.mul_sum]
            have h0 := sum_trace_mul_eq_zero_of_not_repEquiv hm₁ hmT hi₁ hiT hnot_eqv
              (extRep RF σ₁ k₁) (extRep RF σ₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)
            rw [h0, mul_zero]
          · simp [dif_neg hz]

lemma charInner_phi_ne {F : Type} [Group F] [Fintype F] {n : ℕ}
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF] {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)]
    [∀ ρ, DecidableEq (BF ρ)] (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (hRF : IsIrrepSystem RF)
    {BS : ∀ m, Nat.Partition m → Type} [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (hRS : ∀ m, IsIrrepSystem (RS m))
    (T : (Fin n → ΛF) → Set (WP F n))
    (σ₁ σ₂ : Fin n → ΛF) (hσ₁ : Antitone σ₁) (hσ₂ : Antitone σ₂) (hne : σ₁ ≠ σ₂)
    (hT₁ : Subgroup.IsComplement (T σ₁) (inertiaW (F := F) σ₁ : Set (WP F n)))
    (hT₂ : Subgroup.IsComplement (T σ₂) (inertiaW (F := F) σ₂ : Set (WP F n)))
    (ν₁ : ∀ ρ, Nat.Partition (Fintype.card (block σ₁ ρ)))
    (ν₂ : ∀ ρ, Nat.Partition (Fintype.card (block σ₂ ρ))) :
    charInner
      (indRep (inertiaW (F := F) σ₁) (T σ₁)
        (fun x => Matrix.kronecker (extRep RF σ₁ x) (littleRep RS σ₁ ν₁ x)))
      (indRep (inertiaW (F := F) σ₂) (T σ₂)
        (fun x => Matrix.kronecker (extRep RF σ₂ x) (littleRep RS σ₂ ν₂ x))) = 0 := by
  let R₁ := fun x : inertiaW (F := F) σ₁ => Matrix.kronecker (extRep RF σ₁ x) (littleRep RS σ₁ ν₁ x)
  let R₂ := fun x : inertiaW (F := F) σ₂ => Matrix.kronecker (extRep RF σ₂ x) (littleRep RS σ₂ ν₂ x)
  have hR₁ : IsMatRep R₁ := isMatRep_kronecker
    (isUnitaryRep_extRep (F := F) RF hRF σ₁).1 (isUnitaryRep_littleRep (F := F) RS hRS σ₁ ν₁).1
  have hR₂ : IsMatRep R₂ := isMatRep_kronecker
    (isUnitaryRep_extRep (F := F) RF hRF σ₂).1 (isUnitaryRep_littleRep (F := F) RS hRS σ₂ ν₂).1
  have hmul := card_mul_charInner_indRep (inertiaW (F := F) σ₁) (inertiaW (F := F) σ₂)
    (T σ₁) (T σ₂) hT₁ hT₂ R₁ R₂ hR₁ hR₂
  have hzero : (∑ z : WP F n, ∑ k₁ : inertiaW (F := F) σ₁,
      if hz : z⁻¹ * (k₁ : WP F n) * z ∈ inertiaW (F := F) σ₂ then
        Matrix.trace (R₁ k₁) * Matrix.trace (R₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹)
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun z _ => ?_
    exact charInner_phi_aux RF hRF RS hRS T σ₁ σ₂ hσ₁ hσ₂ hT₁ hT₂ ν₁ ν₂ z (fun h => hne h.1)
  rw [hzero] at hmul
  have hc1 : (Fintype.card (inertiaW (F := F) σ₁) : ℂ) ≠ 0 := by
    have : Nonempty (inertiaW (F := F) σ₁) := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc2 : (Fintype.card (inertiaW (F := F) σ₂) : ℂ) ≠ 0 := by
    have : Nonempty (inertiaW (F := F) σ₂) := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hc1 hc2)

lemma charInner_phi_eq {F : Type} [Group F] [Fintype F] {n : ℕ}
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF] {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)]
    [∀ ρ, DecidableEq (BF ρ)] (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (hRF : IsIrrepSystem RF)
    {BS : ∀ m, Nat.Partition m → Type} [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (hRS : ∀ m, IsIrrepSystem (RS m))
    (T : (Fin n → ΛF) → Set (WP F n))
    (σ : Fin n → ΛF) (hσ : Antitone σ)
    (hT : Subgroup.IsComplement (T σ) (inertiaW (F := F) σ : Set (WP F n)))
    (ν₁ ν₂ : ∀ ρ, Nat.Partition (Fintype.card (block σ ρ))) :
    charInner
      (indRep (inertiaW (F := F) σ) (T σ)
        (fun x => Matrix.kronecker (extRep RF σ x) (littleRep RS σ ν₁ x)))
      (indRep (inertiaW (F := F) σ) (T σ)
        (fun x => Matrix.kronecker (extRep RF σ x) (littleRep RS σ ν₂ x))) =
      if ν₁ = ν₂ then 1 else 0 := by
  let K := inertiaW (F := F) σ
  let R₁ := fun x : K => Matrix.kronecker (extRep RF σ x) (littleRep RS σ ν₁ x)
  let R₂ := fun x : K => Matrix.kronecker (extRep RF σ x) (littleRep RS σ ν₂ x)
  have he : IsUnitaryRep (extRep (F := F) RF σ) := isUnitaryRep_extRep (F := F) RF hRF σ
  have hl1 : IsUnitaryRep (littleRep (F := F) RS σ ν₁) := isUnitaryRep_littleRep (F := F) RS hRS σ ν₁
  have hl2 : IsUnitaryRep (littleRep (F := F) RS σ ν₂) := isUnitaryRep_littleRep (F := F) RS hRS σ ν₂
  have hR₁ : IsMatRep R₁ := isMatRep_kronecker he.1 hl1.1
  have hR₂ : IsMatRep R₂ := isMatRep_kronecker he.1 hl2.1
  have hmul := card_mul_charInner_indRep K K (T σ) (T σ) hT hT R₁ R₂ hR₁ hR₂
  let S : ℂ := ∑ k₁ : K, Matrix.trace (R₁ k₁) * Matrix.trace (R₂ k₁⁻¹)
  have hz_eval : ∀ z : WP F n,
      (∑ k₁ : K, if hz : z⁻¹ * (k₁ : WP F n) * z ∈ K then
        Matrix.trace (R₁ k₁) * Matrix.trace (R₂ (⟨z⁻¹ * (k₁ : WP F n) * z, hz⟩)⁻¹) else 0) =
      if z ∈ K then S else 0 := fun z => by
    by_cases hzK : z ∈ K
    · rw [if_pos hzK]
      refine Finset.sum_congr rfl fun k₁ _ => ?_
      let zK : K := ⟨z, hzK⟩
      have hmem : z⁻¹ * (k₁ : WP F n) * z ∈ K := (zK⁻¹ * k₁ * zK).2
      rw [dif_pos hmem]
      have hconj : (⟨z⁻¹ * (k₁ : WP F n) * z, hmem⟩ : K)⁻¹ = zK⁻¹ * k₁⁻¹ * zK := by
        apply Subtype.ext
        change (z⁻¹ * (k₁ : WP F n) * z)⁻¹ = z⁻¹ * (k₁ : WP F n)⁻¹ * z
        group
      rw [hconj, hR₂.2, hR₂.2, Matrix.trace_mul_comm (R₂ zK⁻¹ * R₂ k₁⁻¹) (R₂ zK),
        ← Matrix.mul_assoc (R₂ zK) (R₂ zK⁻¹) (R₂ k₁⁻¹), isMatRep_mul_inv hR₂ zK, Matrix.one_mul]
    · rw [if_neg hzK]
      exact charInner_phi_aux RF hRF RS hRS T σ σ hσ hσ hT hT ν₁ ν₂ z (fun h => hzK h.2)
  have hsum_z : (∑ z : WP F n, if z ∈ K then S else 0) = (Fintype.card K : ℂ) * S := by
    rw [(Finset.sum_filter (p := fun z : WP F n => z ∈ K) (f := fun _ : WP F n => S)
      (s := Finset.univ)).symm, Finset.sum_const, nsmul_eq_mul]
    congr 1
    exact congrArg Nat.cast (Fintype.card_subtype (fun z : WP F n => z ∈ K)).symm
  have hS_mul : (Fintype.card (baseGroup F n) : ℂ) * S =
      (Fintype.card (baseGroup F n) : ℂ) * ((Fintype.card K : ℂ) * (if ν₁ = ν₂ then 1 else 0)) := by
    have hshift : ∀ m : baseGroup F n, S =
        ∑ k₁ : K,
          (Matrix.trace (littleRep RS σ ν₁ k₁) * Matrix.trace (littleRep RS σ ν₂ k₁⁻¹)) *
          (Matrix.trace (extRep RF σ k₁ * baseRep RF σ m) *
            Matrix.trace (extRep RF σ k₁⁻¹ * baseRep RF σ m⁻¹)) := fun m => by
      let mI : K := ⟨m.1, baseGroup_le_inertiaW σ m.2⟩
      symm
      refine Fintype.sum_equiv (Equiv.mulRight mI) _ _ fun k₁ => ?_
      have hmul_app : (Equiv.mulRight mI) k₁ = k₁ * mI := rfl
      simp only [hmul_app]
      have hm1 : extRep RF σ (k₁ * mI) = extRep RF σ k₁ * baseRep RF σ m := by
        rw [he.1.2, extRep_mem_baseGroup RF σ m.2 mI.2]
      have hl1' : littleRep RS σ ν₁ (k₁ * mI) = littleRep RS σ ν₁ k₁ :=
        littleRep_mul_baseGroup RS σ ν₁ k₁ m.2
      have hm2 : extRep RF σ (k₁ * mI)⁻¹ = baseRep RF σ m⁻¹ * extRep RF σ k₁⁻¹ := by
        rw [mul_inv_rev, he.1.2]
        congr 1
        have hmI_inv : ((mI⁻¹ : K) : WP F n) ∈ baseGroup F n := (baseGroup F n).inv_mem m.2
        trans baseRep RF σ ⟨(mI⁻¹ : WP F n), hmI_inv⟩
        · exact extRep_mem_baseGroup RF σ hmI_inv mI⁻¹.2
        · rfl
      have hl2' : littleRep RS σ ν₂ (k₁ * mI)⁻¹ = littleRep RS σ ν₂ k₁⁻¹ := by
        rw [mul_inv_rev, littleRep_eq_prodRep, littleRep_eq_prodRep, map_mul]
        have hker : mI⁻¹ ∈ (blockHom (F := F) σ).ker := by
          rw [blockHom_ker, Subgroup.mem_subgroupOf]
          exact (baseGroup F n).inv_mem m.2
        rw [MonoidHom.mem_ker.mp hker, one_mul]
      dsimp only [R₁, R₂]
      rw [hm1, hl1', hm2, hl2', trace_kronecker, trace_kronecker,
        Matrix.trace_mul_comm (baseRep RF σ m⁻¹) (extRep RF σ k₁⁻¹)]
      ring
    have hirr := isIrrepSystem_baseRep (F := F) (n := n) hRF
    have hm_base : IsMatRep (baseRep (F := F) RF σ) := (hirr.1 σ).1
    have hi_base : IsIrreducibleRep (baseRep (F := F) RF σ) := hirr.2.1 σ
    have hbase_ne : (Fintype.card (baseGroup F n) : ℂ) ≠ 0 := by
      have : Nonempty (baseGroup F n) := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hBF_ne : (Fintype.card (∀ r, BF (σ r)) : ℂ) ≠ 0 := by
      have : Nonempty (∀ r, BF (σ r)) := hi_base.1; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    calc (Fintype.card (baseGroup F n) : ℂ) * S
        = ∑ _m : baseGroup F n, S := by
          symm
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ m : baseGroup F n, ∑ k₁ : K,
            (Matrix.trace (littleRep RS σ ν₁ k₁) * Matrix.trace (littleRep RS σ ν₂ k₁⁻¹)) *
            (Matrix.trace (extRep RF σ k₁ * baseRep RF σ m) *
              Matrix.trace (extRep RF σ k₁⁻¹ * baseRep RF σ m⁻¹)) :=
            Finset.sum_congr rfl fun m _ => hshift m
      _ = ∑ k₁ : K, (Matrix.trace (littleRep RS σ ν₁ k₁) * Matrix.trace (littleRep RS σ ν₂ k₁⁻¹)) *
            ∑ m : baseGroup F n,
              Matrix.trace (extRep RF σ k₁ * baseRep RF σ m) *
              Matrix.trace (extRep RF σ k₁⁻¹ * baseRep RF σ m⁻¹) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k₁ _ => by rw [← Finset.mul_sum]
      _ = ∑ k₁ : K, (Matrix.trace (littleRep RS σ ν₁ k₁) * Matrix.trace (littleRep RS σ ν₂ k₁⁻¹)) *
            (Fintype.card (baseGroup F n) : ℂ) := by
            refine Finset.sum_congr rfl fun k₁ _ => ?_
            have havg := avg_trace_mul_eq_trace_mul hm_base hi_base
              (extRep RF σ k₁) (extRep RF σ k₁⁻¹)
            rw [isMatRep_mul_inv he.1 k₁, Matrix.trace_one, inv_mul_cancel₀ hBF_ne] at havg
            have hsum_m : ∑ m : baseGroup F n,
                Matrix.trace (extRep RF σ k₁ * baseRep RF σ m) *
                Matrix.trace (extRep RF σ k₁⁻¹ * baseRep RF σ m⁻¹) =
                (Fintype.card (baseGroup F n) : ℂ) := by
              have h1 := congrArg (fun z : ℂ => (Fintype.card (baseGroup F n) : ℂ) * z) havg
              rwa [← mul_assoc, mul_inv_cancel₀ hbase_ne, one_mul, mul_one] at h1
            rw [hsum_m]
      _ = (Fintype.card (baseGroup F n) : ℂ) *
            ∑ k₁ : K, Matrix.trace (littleRep RS σ ν₁ k₁) * Matrix.trace (littleRep RS σ ν₂ k₁⁻¹) := by
            rw [← Finset.sum_mul, mul_comm]
      _ = (Fintype.card (baseGroup F n) : ℂ) *
            ((Fintype.card K : ℂ) * charInner (littleRep (F := F) RS σ ν₁) (littleRep (F := F) RS σ ν₂)) := by
            have hK_ne : (Fintype.card K : ℂ) ≠ 0 := by
              have : Nonempty K := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
            congr 1
            simp only [charInner]
            rw [← mul_assoc, mul_inv_cancel₀ hK_ne, one_mul]
      _ = (Fintype.card (baseGroup F n) : ℂ) * ((Fintype.card K : ℂ) * (if ν₁ = ν₂ then 1 else 0)) := by
            rw [charInner_littleRep RS hRS σ ν₁ ν₂]
  have hbase_ne : (Fintype.card (baseGroup F n) : ℂ) ≠ 0 := by
    have : Nonempty (baseGroup F n) := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : S = (Fintype.card K : ℂ) * (if ν₁ = ν₂ then 1 else 0) :=
    mul_left_cancel₀ hbase_ne hS_mul
  simp_rw [hz_eval] at hmul
  rw [hsum_z, hS, ← mul_assoc] at hmul
  have hK_ne : (Fintype.card K : ℂ) ≠ 0 := by
    have : Nonempty K := ⟨1⟩; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact mul_left_cancel₀ (mul_ne_zero hK_ne hK_ne) hmul

lemma sum_card_sq_phi_eq_card {F : Type} [Group F] [Fintype F] (n : ℕ)
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF] (BF : ΛF → Type) [∀ ρ, Fintype (BF ρ)]
    [∀ ρ, DecidableEq (BF ρ)] (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (hRF : IsIrrepSystem RF)
    (BS : ∀ m, Nat.Partition m → Type) [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (hRS : ∀ m, IsIrrepSystem (RS m))
    (T : (Fin n → ΛF) → Set (WP F n))
    (hT : ∀ σ : Fin n → ΛF, Antitone σ →
      Subgroup.IsComplement (T σ) (inertiaW (F := F) σ : Set (WP F n))) :
    ∑ p : (Σ σ : {σ : Fin n → ΛF // Antitone σ},
        ∀ ρ, Nat.Partition (Fintype.card (block σ.1 ρ))),
      Fintype.card (T p.1.1 × ((∀ r, BF (p.1.1 r)) × (∀ ρ, BS _ (p.2 ρ)))) ^ 2 =
      Fintype.card (WP F n) := by
  let Orb (σ : Fin n → ΛF) : Finset (Fin n → ΛF) :=
    Finset.univ.image (fun π : Equiv.Perm (Fin n) => fun r => σ (π⁻¹ r))
  have hOrb_bij : ∀ (σ : Fin n → ΛF) (_hσ : Antitone σ),
      Fintype.card (T σ) = (Orb σ).card := fun σ hσ => by
    let f : T σ → Orb σ := fun t =>
      ⟨fun r => σ (t.1.right⁻¹ r), Finset.mem_image.mpr ⟨t.1.right, Finset.mem_univ _, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun t₁ t₂ h => ?_, fun ⟨l, hl⟩ => ?_⟩
      · have heq : (fun r => σ (t₁.1.right⁻¹ r)) = (fun r => σ (t₂.1.right⁻¹ r)) :=
          congrArg Subtype.val h
        have hk : (t₁ : WP F n)⁻¹ * (t₂ : WP F n) ∈ inertiaW (F := F) σ := fun r => by
          have hright : ((t₁ : WP F n)⁻¹ * (t₂ : WP F n)).right⁻¹ r =
              t₂.1.right⁻¹ (t₁.1.right r) := by
            simp [WreathProduct.mul_right, WreathProduct.inv_right]
          rw [hright]
          have h1 := congr_fun heq (t₁.1.right r)
          simpa using h1.symm
        obtain ⟨_, _, huniq⟩ := (hT σ hσ).existsUnique (t₂ : WP F n)
        have ha := huniq ⟨t₁, ⟨_, hk⟩⟩ (mul_inv_cancel_left (t₁ : WP F n) (t₂ : WP F n))
        have hb := huniq ⟨t₂, ⟨1, (inertiaW (F := F) σ).one_mem⟩⟩ (mul_one (t₂ : WP F n))
        exact congrArg Prod.fst (ha.trans hb.symm)
      · obtain ⟨π, _, rfl⟩ := Finset.mem_image.mp hl
        let g : WP F n := ⟨1, π⟩
        obtain ⟨⟨t, k⟩, hmul, _⟩ := (hT σ hσ).existsUnique g
        refine ⟨t, Subtype.ext (funext fun r => ?_)⟩
        have hπ : π = t.1.right * k.1.right := by
          have := congrArg WreathProduct.right hmul
          simpa [g, WreathProduct.mul_right] using this.symm
        have hkr := k.2 (t.1.right⁻¹ r)
        change σ (t.1.right⁻¹ r) = σ (π⁻¹ r)
        rw [hπ]
        simpa [mul_inv_rev] using hkr.symm
    simpa [Fintype.card_coe] using Fintype.card_of_bijective hf
  have hWP_card : Fintype.card (WP F n) =
      Fintype.card (Fin n → F) * Fintype.card (Equiv.Perm (Fin n)) := by
    let eWP : WP F n ≃ (Fin n → F) × Equiv.Perm (Fin n) :=
      { toFun := fun w => (w.left, w.right)
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    rw [Fintype.card_congr eWP, Fintype.card_prod]
  have hbase_card : Fintype.card (baseGroup F n) = Fintype.card (Fin n → F) :=
    (Fintype.card_congr (baseGroupEquiv F n).toEquiv).symm
  have hT_H : ∀ (σ : Fin n → ΛF) (hσ : Antitone σ),
      Fintype.card (T σ) * Fintype.card (∀ ρ, Equiv.Perm (Fin (Fintype.card (block σ ρ)))) =
        Fintype.card (Equiv.Perm (Fin n)) := fun σ hσ => by
    let φ := blockHom (F := F) σ
    have hcomp : Fintype.card (T σ) * Fintype.card (inertiaW (F := F) σ) = Fintype.card (WP F n) := by
      rw [← Fintype.card_prod]
      exact Fintype.card_congr (complementEquiv (inertiaW (F := F) σ) (T σ) (hT σ hσ))
    have hquot : Fintype.card (inertiaW (F := F) σ) =
        Fintype.card φ.ker * Fintype.card (∀ ρ, Equiv.Perm (Fin (Fintype.card (block σ ρ)))) := by
      have he := QuotientGroup.quotientKerEquivOfSurjective φ (blockHom_surjective (F := F) σ)
      rw [← Fintype.card_congr he.toEquiv]
      have hl := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hl
      rw [hl, mul_comm]
    have hker_card : Fintype.card φ.ker = Fintype.card (Fin n → F) := by
      let eK : φ.ker ≃ baseGroup F n :=
        { toFun := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.mp (blockHom_ker (F := F) σ ▸ x.2)⟩
          invFun := fun y => ⟨⟨y.1, baseGroup_le_inertiaW σ y.2⟩,
            by rw [blockHom_ker, Subgroup.mem_subgroupOf]; exact y.2⟩
          left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := fun y => by apply Subtype.ext; rfl }
      rw [Fintype.card_congr eK, hbase_card]
    have hpos : 0 < Fintype.card (Fin n → F) := by
      have : Nonempty (Fin n → F) := ⟨fun _ => 1⟩; exact Fintype.card_pos
    rw [hquot, hker_card, hWP_card] at hcomp
    have hcomp' : (Fintype.card (T σ) *
        Fintype.card (∀ ρ, Equiv.Perm (Fin (Fintype.card (block σ ρ))))) *
        Fintype.card (Fin n → F) =
        Fintype.card (Equiv.Perm (Fin n)) * Fintype.card (Fin n → F) := by
      linarith
    exact Nat.mul_right_cancel hpos hcomp'
  let sortOrb (l : Fin n → ΛF) : {σ : Fin n → ΛF // Antitone σ} :=
    ⟨Classical.choose (exists_antitone_orbit l),
      (Classical.choose_spec (exists_antitone_orbit l)).1⟩
  have hfib_iff : ∀ (l : Fin n → ΛF) (σ : {σ : Fin n → ΛF // Antitone σ}),
      l ∈ Orb σ.1 ↔ sortOrb l = σ := fun l σ => by
    simp only [Orb, Finset.mem_image, Finset.mem_univ, true_and]
    have hspec := Classical.choose_spec (exists_antitone_orbit l)
    obtain ⟨π₀, hl₀⟩ := hspec.2
    constructor
    · rintro ⟨π, hπ⟩
      apply Subtype.ext
      refine antitone_orbit_unique (sortOrb l).2 σ.2 (π⁻¹ * π₀) ?_
      ext r
      have h1 := congr_fun hl₀ (π r)
      have h2 := congr_fun hπ (π r)
      rw [show π⁻¹ (π r) = r from π.left_inv r] at h2
      simp only [sortOrb, mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply, inv_inv]
      exact h2.trans h1
    · intro h
      refine ⟨π₀, ?_⟩
      rw [← h]
      exact hl₀.symm
  have hfib_sum : (∑ σ : {σ : Fin n → ΛF // Antitone σ},
      ∑ l ∈ Orb σ.1, Fintype.card (∀ r, BF (l r)) ^ 2) =
      ∑ l : Fin n → ΛF, Fintype.card (∀ r, BF (l r)) ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n → ΛF)))
      (t := (Finset.univ : Finset {σ : Fin n → ΛF // Antitone σ}))
      (g := sortOrb) (fun _ _ => Finset.mem_univ _) (fun l => Fintype.card (∀ r, BF (l r)) ^ 2)]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfib_iff l σ
  have hOrb_sum : ∀ σ : {σ : Fin n → ΛF // Antitone σ},
      (Orb σ.1).card * Fintype.card (∀ r, BF (σ.1 r)) ^ 2 =
        ∑ l ∈ Orb σ.1, Fintype.card (∀ r, BF (l r)) ^ 2 := fun σ => by
    have hconst : ∀ l ∈ Orb σ.1,
        Fintype.card (∀ r, BF (l r)) ^ 2 = Fintype.card (∀ r, BF (σ.1 r)) ^ 2 := fun l hl => by
      obtain ⟨π, _, rfl⟩ := Finset.mem_image.mp hl
      have hc : Fintype.card (∀ r, BF (σ.1 (π⁻¹ r))) = Fintype.card (∀ s, BF (σ.1 s)) := by
        simp_rw [Fintype.card_pi]
        exact Fintype.prod_equiv π⁻¹ _ _ fun r => rfl
      rw [hc]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hsum_ν_all : ∀ σ : {σ : Fin n → ΛF // Antitone σ},
      (∑ ν : (∀ ρ, Nat.Partition (Fintype.card (block σ.1 ρ))),
        Fintype.card (∀ ρ, BS _ (ν ρ)) ^ 2) =
      Fintype.card (∀ ρ, Equiv.Perm (Fin (Fintype.card (block σ.1 ρ)))) := fun σ => by
    have hsys := isIrrepSystem_prodRep (fun ρ => RS (Fintype.card (block σ.1 ρ)))
      (fun ρ => hRS _)
    exact sum_card_sq_eq_card hsys
  have hsum_base : (∑ l : Fin n → ΛF, Fintype.card (∀ r, BF (l r)) ^ 2) =
      Fintype.card (Fin n → F) := by
    simp_rw [Fintype.card_pi, sq, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum fun (_ : Fin n) (ρ : ΛF) => Fintype.card (BF ρ) * Fintype.card (BF ρ)]
    refine Finset.prod_congr rfl fun _ _ => ?_
    simpa [sq] using sum_card_sq_eq_card hRF
  rw [Fintype.sum_sigma]
  calc ∑ σ : {σ : Fin n → ΛF // Antitone σ},
        ∑ ν : (∀ ρ, Nat.Partition (Fintype.card (block σ.1 ρ))),
          Fintype.card (T σ.1 × ((∀ r, BF (σ.1 r)) × (∀ ρ, BS _ (ν ρ)))) ^ 2
      = ∑ σ : {σ : Fin n → ΛF // Antitone σ},
          (Fintype.card (T σ.1) ^ 2 * Fintype.card (∀ r, BF (σ.1 r)) ^ 2) *
          ∑ ν : (∀ ρ, Nat.Partition (Fintype.card (block σ.1 ρ))),
            Fintype.card (∀ ρ, BS _ (ν ρ)) ^ 2 := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ν _ => ?_
          simp only [Fintype.card_prod]
          ring
    _ = ∑ σ : {σ : Fin n → ΛF // Antitone σ},
          (Fintype.card (T σ.1) ^ 2 * Fintype.card (∀ r, BF (σ.1 r)) ^ 2) *
          Fintype.card (∀ ρ, Equiv.Perm (Fin (Fintype.card (block σ.1 ρ)))) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [hsum_ν_all σ]
    _ = ∑ σ : {σ : Fin n → ΛF // Antitone σ},
          Fintype.card (Equiv.Perm (Fin n)) *
            ((Orb σ.1).card * Fintype.card (∀ r, BF (σ.1 r)) ^ 2) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [← hOrb_bij σ.1 σ.2]
          calc (Fintype.card (T σ.1) ^ 2 * Fintype.card (∀ r, BF (σ.1 r)) ^ 2) *
                Fintype.card (∀ ρ, Equiv.Perm (Fin (Fintype.card (block σ.1 ρ))))
              = (Fintype.card (T σ.1) *
                  Fintype.card (∀ ρ, Equiv.Perm (Fin (Fintype.card (block σ.1 ρ))))) *
                  (Fintype.card (T σ.1) * Fintype.card (∀ r, BF (σ.1 r)) ^ 2) := by ring
            _ = Fintype.card (Equiv.Perm (Fin n)) *
                  (Fintype.card (T σ.1) * Fintype.card (∀ r, BF (σ.1 r)) ^ 2) := by
                  rw [hT_H σ.1 σ.2]
    _ = Fintype.card (Equiv.Perm (Fin n)) *
          ∑ σ : {σ : Fin n → ΛF // Antitone σ},
            ∑ l ∈ Orb σ.1, Fintype.card (∀ r, BF (l r)) ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun σ _ => hOrb_sum σ
    _ = Fintype.card (Equiv.Perm (Fin n)) * ∑ l : Fin n → ΛF, Fintype.card (∀ r, BF (l r)) ^ 2 := by
          rw [hfib_sum]
    _ = Fintype.card (Equiv.Perm (Fin n)) * Fintype.card (Fin n → F) := by
          rw [hsum_base]
    _ = Fintype.card (WP F n) := by rw [hWP_card, mul_comm]

end GL2QFT.Supplement.Thm87Helpers

theorem solution (F : Type) [Group F] [Fintype F] (n : ℕ) (hn : 1 ≤ n)
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF] (BF : ΛF → Type) [∀ ρ, Fintype (BF ρ)]
    [∀ ρ, DecidableEq (BF ρ)] (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (hRF : IsIrrepSystem RF)
    (BS : ∀ m, Nat.Partition m → Type) [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (hRS : ∀ m, IsIrrepSystem (RS m))
    (T : (Fin n → ΛF) → Set (WP F n))
    (hT : ∀ σ : Fin n → ΛF, Antitone σ →
      Subgroup.IsComplement (T σ) (inertiaW (F := F) σ : Set (WP F n)) ∧ (1 : WP F n) ∈ T σ) :
    let Lab : Type :=
      Σ σ : {σ : Fin n → ΛF // Antitone σ}, ∀ ρ, Nat.Partition (Fintype.card (block σ.1 ρ))
    let Φ : ∀ p : Lab, WP F n →
        Matrix (T p.1.1 × ((∀ r, BF (p.1.1 r)) × (∀ ρ, BS _ (p.2 ρ))))
          (T p.1.1 × ((∀ r, BF (p.1.1 r)) × (∀ ρ, BS _ (p.2 ρ)))) ℂ :=
      fun p => indRep (inertiaW (F := F) p.1.1) (T p.1.1)
        (fun x => Matrix.kronecker (extRep RF p.1.1 x) (littleRep RS p.1.1 p.2 x))
    (∀ p : Lab, IsUnitaryRep (Φ p) ∧ IsIrreducibleRep (Φ p)) ∧
    (∀ p p' : Lab, RepEquiv (Φ p) (Φ p') → p = p') ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : WP F n → Matrix ι ι ℂ),
      IsMatRep ρ → IsIrreducibleRep ρ → ∃ p : Lab, RepEquiv (Φ p) ρ) := by
  classical
  dsimp only
  let Lab : Type :=
    Σ σ : {σ : Fin n → ΛF // Antitone σ}, ∀ ρ, Nat.Partition (Fintype.card (block σ.1 ρ))
  let Φ : ∀ p : Lab, WP F n →
      Matrix (T p.1.1 × ((∀ r, BF (p.1.1 r)) × (∀ ρ, BS _ (p.2 ρ))))
        (T p.1.1 × ((∀ r, BF (p.1.1 r)) × (∀ ρ, BS _ (p.2 ρ)))) ℂ :=
    fun p => indRep (inertiaW (F := F) p.1.1) (T p.1.1)
      (fun x => Matrix.kronecker (extRep RF p.1.1 x) (littleRep RS p.1.1 p.2 x))
  have hΦ_unit : ∀ p : Lab, IsUnitaryRep (Φ p) := fun ⟨⟨σ, hσ⟩, ν⟩ => by
    refine GL2QFT.Supplement.Thm87Helpers.isUnitaryRep_indRep
      (inertiaW (F := F) σ) (T σ) (hT σ hσ).1 ?_
    exact GL2QFT.Supplement.Thm87Helpers.isUnitaryRep_kronecker
      (GL2QFT.Supplement.Thm87Helpers.isUnitaryRep_extRep (F := F) RF hRF σ)
      (GL2QFT.Supplement.Thm87Helpers.isUnitaryRep_littleRep (F := F) RS hRS σ ν)
  have hΦ_irr : ∀ p : Lab, IsIrreducibleRep (Φ p) := fun ⟨⟨σ, hσ⟩, ν⟩ => by
    have hne : Nonempty (T σ × ((∀ r, BF (σ r)) × (∀ ρ, BS _ (ν ρ)))) :=
      ⟨⟨⟨1, (hT σ hσ).2⟩,
        ⟨fun r => Classical.choice (hRF.2.1 (σ r)).1,
         fun ρ => Classical.choice ((hRS _).2.1 (ν ρ)).1⟩⟩⟩
    refine GL2QFT.Supplement.Thm87Helpers.isIrreducibleRep_of_charInner_self_eq_one
      (hΦ_unit ⟨⟨σ, hσ⟩, ν⟩).1 hne ?_
    have hch := GL2QFT.Supplement.Thm87Helpers.charInner_phi_eq
      RF hRF RS hRS T σ hσ (hT σ hσ).1 ν ν
    rw [if_pos rfl] at hch
    dsimp only [Φ]
    convert hch
  have hΦ_diff : ∀ p p' : Lab, p ≠ p' → ¬ RepEquiv (Φ p) (Φ p') := by
    rintro ⟨⟨σ₁, hσ₁⟩, ν₁⟩ ⟨⟨σ₂, hσ₂⟩, ν₂⟩ hne heqv
    rw [GL2QFT.Supplement.Thm87Helpers.repEquiv_iff_charInner_ne_zero
      (hΦ_unit _).1 (hΦ_unit _).1 (hΦ_irr _) (hΦ_irr _)] at heqv
    by_cases hσ : σ₁ = σ₂
    · subst hσ
      have hν : ν₁ ≠ ν₂ := fun h => hne (by subst h; rfl)
      have hch := GL2QFT.Supplement.Thm87Helpers.charInner_phi_eq
        RF hRF RS hRS T σ₁ hσ₁ (hT σ₁ hσ₁).1 ν₂ ν₁
      rw [if_neg hν.symm] at hch
      dsimp only [Φ] at heqv
      exact heqv (by convert hch)
    · have hch := GL2QFT.Supplement.Thm87Helpers.charInner_phi_ne
        RF hRF RS hRS T σ₂ σ₁ hσ₂ hσ₁ (Ne.symm hσ) (hT σ₂ hσ₂).1 (hT σ₁ hσ₁).1 ν₂ ν₁
      dsimp only [Φ] at heqv
      exact heqv (by convert hch)
  refine ⟨fun p => ⟨hΦ_unit p, hΦ_irr p⟩, ?_, ?_⟩
  · intro p p' heqv
    by_contra hne
    exact hΦ_diff p p' hne heqv
  · intro ι _ _ ρ hρm hρi
    have hsum := GL2QFT.Supplement.Thm87Helpers.sum_card_sq_phi_eq_card
      (F := F) n BF RF hRF BS RS hRS T (fun σ hσ => (hT σ hσ).1)
    exact GL2QFT.Supplement.Thm87Helpers.exhaustive_of_sum_sq_eq_card
      Φ (fun p => (hΦ_unit p).1) hΦ_irr hΦ_diff (by convert hsum) ρ hρm hρi
