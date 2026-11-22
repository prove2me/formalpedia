-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_7_12
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:27:09.972381+00:00
-- url     : https://prove2.me/submissions/6902182a-b1a0-41a7-adee-2f7e847c83de

import Definitions.Def_GL2QFT_Supplement_RepTheory

noncomputable section

open Classical
open scoped Matrix ComplexConjugate Kronecker
open GL2QFT GL2QFT.Supplement

namespace GL2QFT.Supplement.Thm712Helpers

/-! ### Section 1: Matrix representation basics, Kronecker products, and Schur's lemma -/

private theorem isUnitaryRep_mul_conjTranspose {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g * (R g)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hR.2 g)

private theorem isUnitaryRep_conjTranspose_mul {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    (R g)ᴴ * R g = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hR.2 g)

private theorem isMatRep_mul_inv {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsMatRep R) (g : G) :
    R g * R g⁻¹ = 1 := by
  rw [← hR.2, mul_inv_cancel, hR.1]

private theorem isMatRep_inv_mul {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsMatRep R) (g : G) :
    R g⁻¹ * R g = 1 := by
  rw [← hR.2, inv_mul_cancel, hR.1]

private theorem isUnitaryRep_inv_eq_conjTranspose {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g⁻¹ = (R g)ᴴ := by
  have h1 : R g * R g⁻¹ = 1 := isMatRep_mul_inv hR.1 g
  have h2 : (R g)ᴴ * R g = 1 := isUnitaryRep_conjTranspose_mul hR g
  calc R g⁻¹ = 1 * R g⁻¹ := (Matrix.one_mul _).symm
    _ = ((R g)ᴴ * R g) * R g⁻¹ := by rw [h2]
    _ = (R g)ᴴ * (R g * R g⁻¹) := Matrix.mul_assoc _ _ _
    _ = (R g)ᴴ := by rw [h1, Matrix.mul_one]

private theorem isUnitaryRep_ne_zero {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g ≠ 0 := by
  intro h0
  have h1 := isUnitaryRep_mul_conjTranspose hR g
  rw [h0, Matrix.zero_mul] at h1
  have i₀ : ι := Classical.arbitrary ι
  have := congr_fun (congr_fun h1 i₀) i₀
  simp at this

private theorem repEquiv_refl {G ι : Type} [Fintype ι] [DecidableEq ι]
    (R : G → Matrix ι ι ℂ) : RepEquiv R R := by
  refine ⟨1, 1, Matrix.one_mul _, Matrix.one_mul _, fun g _ => ?_⟩
  rw [Matrix.one_mul, Matrix.mul_one]

private theorem repEquiv_symm {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
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

private theorem repEquiv_trans {G ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ} {R₃ : G → Matrix ι₃ ι₃ ℂ}
    (h12 : RepEquiv R₁ R₂) (h23 : RepEquiv R₂ R₃) : RepEquiv R₁ R₃ := by
  obtain ⟨A₁, B₁, hAB₁, hBA₁, hi₁⟩ := h12
  obtain ⟨A₂, B₂, hAB₂, hBA₂, hi₂⟩ := h23
  refine ⟨A₂ * A₁, B₁ * B₂, ?_, ?_, fun g hg => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₁, hAB₁, Matrix.one_mul, hAB₂]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc B₂, hBA₂, Matrix.one_mul, hBA₁]
  · rw [Matrix.mul_assoc, hi₁ g hg, ← Matrix.mul_assoc, hi₂ g hg, Matrix.mul_assoc]

private theorem repEquiv_ne_zero_left {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] [Nonempty ι₂]
    {A : Matrix ι₂ ι₁ ℂ} {B : Matrix ι₁ ι₂ ℂ} (hAB : A * B = 1) : A ≠ 0 := by
  intro h0
  rw [h0, Matrix.zero_mul] at hAB
  have i₀ : ι₂ := Classical.arbitrary ι₂
  have := congr_fun (congr_fun hAB i₀) i₀
  simp at this

private theorem isMatRep_kronecker {G ι₁ ι₂ : Type} [Monoid G] [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h₁ : IsMatRep R₁) (h₂ : IsMatRep R₂) :
    IsMatRep (fun g => Matrix.kronecker (R₁ g) (R₂ g)) := by
  refine ⟨?_, ?_⟩
  · simp [h₁.1, h₂.1]
  · intro g h
    simp [h₁.2, h₂.2, Matrix.mul_kronecker_mul]

private theorem isUnitaryRep_kronecker {G ι₁ ι₂ : Type} [Monoid G] [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h₁ : IsUnitaryRep R₁) (h₂ : IsUnitaryRep R₂) :
    IsUnitaryRep (fun g => Matrix.kronecker (R₁ g) (R₂ g)) := by
  refine ⟨isMatRep_kronecker h₁.1 h₂.1, fun g => ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [Matrix.star_eq_conjTranspose, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    isUnitaryRep_mul_conjTranspose h₁ g, isUnitaryRep_mul_conjTranspose h₂ g,
    Matrix.one_kronecker_one]

private theorem isUnitaryRep_inflation {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (l : ΛN)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : (inertia N RN l ⧸ N.subgroupOf (inertia N RN l)) → Matrix ι ι ℂ}
    (hR : IsUnitaryRep R) :
    IsUnitaryRep (inflation N RN l R) := by
  refine ⟨⟨?_, ?_⟩, fun k => ?_⟩
  · simpa [inflation] using hR.1.1
  · intro k₁ k₂
    simpa [inflation] using hR.1.2 (QuotientGroup.mk k₁) (QuotientGroup.mk k₂)
  · exact hR.2 (QuotientGroup.mk k)

private theorem ker_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₁ (LinearMap.ker A.mulVecLin) := by
  intro g v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← hA g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

private theorem range_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₂ (LinearMap.range A.mulVecLin) := by
  intro g w hw
  rcases hw with ⟨v, rfl⟩
  refine ⟨R₁ g *ᵥ v, ?_⟩
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, ← hA g, ← Matrix.mulVec_mulVec]

private theorem mulVecLin_eq_zero_iff {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : Matrix ι₂ ι₁ ℂ) : (∀ v, A *ᵥ v = 0) ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have := congr_fun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  · intro h v
    subst h
    simp

private theorem schur_zero_of_not_repEquiv {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
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
  have hAB : A * B = 1 := by
    rw [← hA_eq, ← LinearMap.toMatrix'_comp]
    have hc : A.mulVecLin.comp e.symm.toLinearMap = LinearMap.id :=
      LinearMap.ext fun v => e.apply_symm_apply v
    rw [hc, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← hA_eq, ← LinearMap.toMatrix'_comp]
    have hc : e.symm.toLinearMap.comp A.mulVecLin = LinearMap.id :=
      LinearMap.ext fun v => e.symm_apply_apply v
    rw [hc, LinearMap.toMatrix'_id]
  exact hne ⟨A, B, hAB, hBA, fun g _ => hA g⟩

private theorem schur_eq_smul_one {G ι : Type} [Fintype ι] [DecidableEq ι]
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
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa [Matrix.mulVecLin_apply, sub_eq_zero] using hv
  have hA' : ∀ g : G, R g * (A - c • (1 : Matrix ι ι ℂ)) =
      (A - c • (1 : Matrix ι ι ℂ)) * R g := by
    intro g
    simp [mul_sub, sub_mul, hA g]
  have hker_top : LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin = ⊤ :=
    (hi.2 _ (ker_invariant hA')).resolve_left hker_ne
  refine ⟨c, ?_⟩
  rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
  intro v
  have hv : v ∈ LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin := hker_top.symm ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  exact hv

/-! ### Section 2: Weyl-averaged inner product, Maschke projection, minimal subrep, Schur converse -/

private def repIP {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (u v : ι → ℂ) : ℂ :=
  ∑ g : G, ∑ i : ι, star ((ρ g *ᵥ u) i) * (ρ g *ᵥ v) i

private theorem repIP_add_left {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (u₁ u₂ v : ι → ℂ) :
    repIP ρ (u₁ + u₂) v = repIP ρ u₁ v + repIP ρ u₂ v := by
  simp only [repIP, Matrix.mulVec_add, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

private theorem repIP_smul_left {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (c : ℂ) (u v : ι → ℂ) :
    repIP ρ (c • u) v = star c * repIP ρ u v := by
  simp only [repIP, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem repIP_add_right {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (u v₁ v₂ : ι → ℂ) :
    repIP ρ u (v₁ + v₂) = repIP ρ u v₁ + repIP ρ u v₂ := by
  simp only [repIP, Matrix.mulVec_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem repIP_smul_right {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (c : ℂ) (u v : ι → ℂ) :
    repIP ρ u (c • v) = c * repIP ρ u v := by
  simp only [repIP, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem repIP_self_eq_zero {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) (u : ι → ℂ)
    (hu : repIP ρ u u = 0) : u = 0 := by
  have hre : (repIP ρ u u).re = 0 := by rw [hu]; simp
  have hsum : ∑ g : G, ∑ i : ι,
      (((ρ g *ᵥ u) i).re ^ 2 + ((ρ g *ᵥ u) i).im ^ 2) = 0 := by
    simpa [repIP, Complex.star_def, Complex.mul_re, sq] using hre
  have hnn : ∀ g ∈ (Finset.univ : Finset G),
      0 ≤ ∑ i : ι, (((ρ g *ᵥ u) i).re ^ 2 + ((ρ g *ᵥ u) i).im ^ 2) := fun g _ =>
    Finset.sum_nonneg fun i _ => by positivity
  have h1 : ∑ i : ι, (((ρ 1 *ᵥ u) i).re ^ 2 + ((ρ 1 *ᵥ u) i).im ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum 1 (Finset.mem_univ 1)
  rw [hρ.1, Matrix.one_mulVec] at h1
  have hnni : ∀ i ∈ (Finset.univ : Finset ι),
      0 ≤ ((u i).re ^ 2 + (u i).im ^ 2) := fun i _ => by positivity
  ext i
  simp only [Pi.zero_apply]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnni).mp h1 i (Finset.mem_univ i)
  exact Complex.ext
    (by simp; nlinarith [sq_nonneg (u i).re, sq_nonneg (u i).im])
    (by simp; nlinarith [sq_nonneg (u i).re, sq_nonneg (u i).im])

private theorem repIP_mulVec {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) (h : G) (u v : ι → ℂ) :
    repIP ρ (ρ h *ᵥ u) (ρ h *ᵥ v) = repIP ρ u v := by
  simp only [repIP, Matrix.mulVec_mulVec, ← hρ.2]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => rfl

private def repOrtho {G ι : Type} [Fintype G] [Fintype ι]
    (ρ : G → Matrix ι ι ℂ) (S : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {v | ∀ s ∈ S, repIP ρ s v = 0}
  zero_mem' := fun s _ => by simp [repIP]
  add_mem' := fun {v₁ v₂} h₁ h₂ s hs => by
    rw [repIP_add_right, h₁ s hs, h₂ s hs, add_zero]
  smul_mem' := fun c {v} hv s hs => by
    rw [repIP_smul_right, hv s hs, mul_zero]

private theorem repOrtho_invariant {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {S : Submodule ℂ (ι → ℂ)}
    (hS : IsInvariantSubspace ρ S) : IsInvariantSubspace ρ (repOrtho ρ S) := by
  intro g v hv s hs
  have hs' : ρ g⁻¹ *ᵥ s ∈ S := hS g⁻¹ s hs
  have h1 : repIP ρ s (ρ g *ᵥ v) = repIP ρ (ρ g *ᵥ (ρ g⁻¹ *ᵥ s)) (ρ g *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, isMatRep_mul_inv hρ g, Matrix.one_mulVec]
  rw [h1, repIP_mulVec hρ g]
  exact hv _ hs'

private theorem repOrtho_isCompl {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
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
      have hrepr : (⟨s, hs⟩ : S) = ∑ i : Fin k, b.repr ⟨s, hs⟩ i • b i := (b.sum_repr ⟨s, hs⟩).symm
      have hs_eq : s = ∑ i : Fin k, b.repr ⟨s, hs⟩ i • (b i : ι → ℂ) := by
        simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using
          congrArg Subtype.val hrepr
      rw [hs_eq]
      have hsum_zero : ∀ t : Finset (Fin k),
          repIP ρ (∑ i ∈ t, b.repr ⟨s, hs⟩ i • (b i : ι → ℂ)) v = 0 := by
        intro t
        induction t using Finset.induction_on with
        | empty => simp [repIP]
        | @insert i t hi ih =>
          have hvi : repIP ρ (b i : ι → ℂ) v = 0 := hv i
          rw [Finset.sum_insert hi, repIP_add_left, repIP_smul_left, hvi, mul_zero, zero_add]
          exact ih
      exact hsum_zero Finset.univ
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
    rw [hdisj, finrank_bot, add_zero] at hsum
    have hk : Module.finrank ℂ S = k := rfl
    omega
  have hsup : S ⊔ repOrtho ρ S = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le _) hsup_ge
  exact ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩

private theorem linearProj_invariant_eq {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {S : Submodule ℂ (ι → ℂ)}
    (hS : IsInvariantSubspace ρ S) (g : G) (v : ι → ℂ) :
    let hcompl := repOrtho_isCompl hρ S
    let π := Submodule.projectionOnto S (repOrtho ρ S) hcompl
    (π (ρ g *ᵥ v) : ι → ℂ) = ρ g *ᵥ (π v : ι → ℂ) := by
  intro hcompl π
  have hmem : v ∈ S ⊔ repOrtho ρ S := hcompl.codisjoint.eq_top ▸ Submodule.mem_top
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hmem
  have hπv : π (s + t) = ⟨s, hs⟩ := by
    dsimp only [π]
    rw [map_add, Submodule.projectionOnto_apply_of_mem_left hcompl hs,
      Submodule.projectionOnto_apply_of_mem_right hcompl ht, add_zero]
  have hgs : ρ g *ᵥ s ∈ S := hS g s hs
  have hgt : ρ g *ᵥ t ∈ repOrtho ρ S := repOrtho_invariant hρ hS g t ht
  have hπgv : π (ρ g *ᵥ (s + t)) = ⟨ρ g *ᵥ s, hgs⟩ := by
    dsimp only [π]
    rw [Matrix.mulVec_add, map_add, Submodule.projectionOnto_apply_of_mem_left hcompl hgs,
      Submodule.projectionOnto_apply_of_mem_right hcompl hgt, add_zero]
  rw [hπgv, hπv]

private theorem exists_invariant_proj {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {S : Submodule ℂ (ι → ℂ)}
    (hS : IsInvariantSubspace ρ S) :
    ∃ P : Matrix ι ι ℂ, P * P = P ∧ (∀ g : G, P * ρ g = ρ g * P) ∧
      (∀ v : ι → ℂ, P *ᵥ v ∈ S) ∧ (∀ v ∈ S, P *ᵥ v = v) := by
  let hcompl := repOrtho_isCompl hρ S
  let π := Submodule.projectionOnto S (repOrtho ρ S) hcompl
  let P_lin : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) := S.subtype.comp π
  let P : Matrix ι ι ℂ := LinearMap.toMatrix' P_lin
  have hP_apply : ∀ v, P *ᵥ v = (π v : ι → ℂ) := fun v =>
    LinearMap.toMatrix'_mulVec P_lin v
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
    intro v
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hP_apply, hP_apply]
    have hvS : (π v : ι → ℂ) ∈ S := (π v).2
    dsimp only [π]
    rw [Submodule.projectionOnto_apply_of_mem_left hcompl hvS, sub_self]
  · intro g
    rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
    intro v
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hP_apply, hP_apply, linearProj_invariant_eq hρ hS g v, sub_self]
  · intro v
    rw [hP_apply]
    exact (π v).2
  · intro v hv
    rw [hP_apply]
    dsimp only [π]
    rw [Submodule.projectionOnto_apply_of_mem_left hcompl hv]

private theorem isIrreducibleRep_of_end_eq_smul_one {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {R : G → Matrix ι ι ℂ} (hR : IsMatRep R)
    (hend : ∀ A : Matrix ι ι ℂ, (∀ g : G, A * R g = R g * A) → ∃ c : ℂ, A = c • (1 : Matrix ι ι ℂ)) :
    IsIrreducibleRep R := by
  refine ⟨‹Nonempty ι›, fun W hW => ?_⟩
  obtain ⟨P, hPP, hcomm, hrange, hfix⟩ := exists_invariant_proj hR hW
  obtain ⟨c, rfl⟩ := hend P hcomm
  have hc : c * c = c := by
    have hmul : (c • (1 : Matrix ι ι ℂ)) * (c • (1 : Matrix ι ι ℂ)) = (c * c) • 1 := by
      simp [smul_smul]
    rw [hmul] at hPP
    have i₀ : ι := Classical.arbitrary ι
    have := congr_fun (congr_fun hPP i₀) i₀
    simpa using this
  have h01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by linear_combination hc
    simpa [sub_eq_zero] using mul_eq_zero.mp this
  rcases h01 with rfl | rfl
  · left
    rw [Submodule.eq_bot_iff]
    intro v hv
    have := hfix v hv
    simpa using this.symm
  · right
    rw [eq_top_iff]
    intro v _
    simpa using hrange v

private theorem basis_toLin_equivFun_symm {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Type} [AddCommGroup M] [Module ℂ M] (b : Module.Basis ι ℂ M)
    (f : M →ₗ[ℂ] M) (v : ι → ℂ) :
    f (b.equivFun.symm v) = b.equivFun.symm (LinearMap.toMatrix b b f *ᵥ v) := by
  apply b.equivFun.injective
  rw [b.equivFun.apply_symm_apply]
  have h := LinearMap.toMatrix_mulVec_repr b b f (b.equivFun.symm v)
  have hr : ⇑(b.repr (b.equivFun.symm v)) = v := b.equivFun.apply_symm_apply v
  change ⇑(b.repr (f (b.equivFun.symm v))) = LinearMap.toMatrix b b f *ᵥ v
  rw [← h, hr]

private theorem exists_min_invariant_subrep {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {W : Submodule ℂ (ι → ℂ)}
    (hWne : W ≠ ⊥) (hWinv : IsInvariantSubspace ρ W) :
    ∃ (d : ℕ) (U : Submodule ℂ (ι → ℂ)) (b : Module.Basis (Fin d) ℂ U)
      (hUinv : IsInvariantSubspace ρ U),
      U ≤ W ∧ U ≠ ⊥ ∧
      (let L_U : G → U →ₗ[ℂ] U := fun g =>
        { toFun := fun u => ⟨ρ g *ᵥ u.1, hUinv g u.1 u.2⟩
          map_add' := fun _ _ => Subtype.ext (Matrix.mulVec_add _ _ _)
          map_smul' := fun _ _ => Subtype.ext (Matrix.mulVec_smul _ _ _) }
      let ρ_U : G → Matrix (Fin d) (Fin d) ℂ := fun g => LinearMap.toMatrix b b (L_U g)
      IsMatRep ρ_U ∧ IsIrreducibleRep ρ_U) := by
  let P : ℕ → Prop := fun d =>
    ∃ U : Submodule ℂ (ι → ℂ), U ≤ W ∧ U ≠ ⊥ ∧ IsInvariantSubspace ρ U ∧ Module.finrank ℂ U = d
  have hex : ∃ d, P d := ⟨Module.finrank ℂ W, W, le_rfl, hWne, hWinv, rfl⟩
  let d := Nat.find hex
  obtain ⟨U, hUW, hUne, hUinv, hUdim⟩ := Nat.find_spec hex
  have : FiniteDimensional ℂ (ι → ℂ) := inferInstance
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
  have hd_pos : 0 < d := by dsimp only [d]; rw [← hUdim]; exact Module.finrank_pos
  let b : Module.Basis (Fin d) ℂ U := Module.finBasisOfFinrankEq ℂ U hUdim
  let L_U : G → U →ₗ[ℂ] U := fun g =>
    { toFun := fun u => ⟨ρ g *ᵥ u.1, hUinv g u.1 u.2⟩
      map_add' := fun u₁ u₂ => Subtype.ext (Matrix.mulVec_add _ _ _)
      map_smul' := fun c u => Subtype.ext (Matrix.mulVec_smul _ _ _) }
  let ρ_U : G → Matrix (Fin d) (Fin d) ℂ := fun g => LinearMap.toMatrix b b (L_U g)
  have hρU_mat : IsMatRep ρ_U := by
    constructor
    · have h1 : L_U 1 = LinearMap.id := by
        ext u i; simp [L_U, hρ.1]
      simp [ρ_U, h1]
    · intro x y
      have hm : L_U (x * y) = (L_U x).comp (L_U y) := by
        ext u i; simp [L_U, hρ.2, Matrix.mulVec_mulVec]
      simp [ρ_U, hm, LinearMap.toMatrix_comp b b b]
  have hρU_irr : IsIrreducibleRep ρ_U := by
    refine ⟨⟨⟨0, hd_pos⟩⟩, fun V hV => ?_⟩
    let U' : Submodule ℂ U := V.map b.equivFun.symm.toLinearMap
    let U'' : Submodule ℂ (ι → ℂ) := U'.map U.subtype
    have hU''_le : U'' ≤ U := Submodule.map_subtype_le U U'
    have hU''_inv : IsInvariantSubspace ρ U'' := by
      intro x u hu
      rcases hu with ⟨u', ⟨v, hv, rfl⟩, rfl⟩
      have hLU : L_U x (b.equivFun.symm v) = b.equivFun.symm (ρ_U x *ᵥ v) :=
        basis_toLin_equivFun_symm b (L_U x) v
      refine ⟨L_U x (b.equivFun.symm v), ⟨ρ_U x *ᵥ v, hV x v hv, hLU.symm⟩, rfl⟩
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
      have : b.equivFun.symm v ∈ U' := ⟨v, hv, rfl⟩
      rw [hU'_bot] at this
      simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg b.equivFun this
    · right
      have hle_d : d ≤ Module.finrank ℂ U'' := Nat.find_min' hex
        ⟨U'', hU''_le.trans hUW, hbot, hU''_inv, rfl⟩
      have hge_d : Module.finrank ℂ U'' ≤ d := by
        dsimp only [d]
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
      have : w = v := b.equivFun.symm.injective hvw
      subst this
      exact hw
  exact ⟨d, U, b, hUinv, hUW, hUne, hρU_mat, hρU_irr⟩

/-! ### Section 3: Induced representation `indRep` -/

private theorem isComplement_mul_cancel {G : Type} [Group G] {K : Subgroup G} {T : Set G}
    (hT : Subgroup.IsComplement T (K : Set G)) {s t : T}
    (hk : (s : G)⁻¹ * (t : G) ∈ K) : s = t := by
  have h1 : (fun x : T × K => (x.1 : G) * (x.2 : G)) ⟨s, ⟨(s : G)⁻¹ * (t : G), hk⟩⟩ =
      (fun x : T × K => (x.1 : G) * (x.2 : G)) ⟨t, 1⟩ := by
    simp
  exact congrArg Prod.fst (hT.1 h1)

private theorem isComplement_existsUnique_left {G : Type} [Group G] {K : Subgroup G} {T : Set G}
    (hT : Subgroup.IsComplement T (K : Set G)) (g : G) (t : T) :
    ∃! s : T, (s : G)⁻¹ * g * (t : G) ∈ K := by
  obtain ⟨⟨s₀, k₀⟩, hmul, huniq⟩ := hT.existsUnique (g * (t : G))
  refine ⟨s₀, ?_, ?_⟩
  · have h : (s₀ : G)⁻¹ * g * (t : G) = (k₀ : G) := by
      calc (s₀ : G)⁻¹ * g * (t : G) = (s₀ : G)⁻¹ * (g * (t : G)) := by rw [mul_assoc]
        _ = (s₀ : G)⁻¹ * ((s₀ : G) * (k₀ : G)) := by rw [hmul]
        _ = (k₀ : G) := by simp
    dsimp
    rw [h]
    exact k₀.2
  · intro s hs
    have hmul' : (s : G) * (⟨(s : G)⁻¹ * g * (t : G), hs⟩ : K) = g * (t : G) := by
      simp [mul_assoc]
    exact congrArg Prod.fst (huniq ⟨s, ⟨_, hs⟩⟩ hmul')

private theorem isComplement_existsUnique_right {G : Type} [Group G] {K : Subgroup G} {T : Set G}
    (hT : Subgroup.IsComplement T (K : Set G)) (g : G) (s : T) :
    ∃! t : T, (s : G)⁻¹ * g * (t : G) ∈ K := by
  obtain ⟨⟨t₀, k₀⟩, hmul, huniq⟩ := hT.existsUnique (g⁻¹ * (s : G))
  refine ⟨t₀, ?_, ?_⟩
  · have h : (s : G)⁻¹ * g * (t₀ : G) = ((k₀⁻¹ : K) : G) := by
      have hk : (t₀ : G) * (k₀ : G) = g⁻¹ * (s : G) := hmul
      calc (s : G)⁻¹ * g * (t₀ : G)
          = (g⁻¹ * (s : G))⁻¹ * (t₀ : G) := by simp [mul_inv_rev]
        _ = ((t₀ : G) * (k₀ : G))⁻¹ * (t₀ : G) := by rw [hk]
        _ = (k₀ : G)⁻¹ := by simp [mul_inv_rev, mul_assoc]
    dsimp
    rw [h]
    exact k₀⁻¹.2
  · intro t ht
    have hk : (t : G) * ((⟨(s : G)⁻¹ * g * (t : G), ht⟩⁻¹ : K) : G) = g⁻¹ * (s : G) := by
      simp [mul_inv_rev, mul_assoc]
    exact congrArg Prod.fst (huniq ⟨t, ⟨_, ht⟩⁻¹⟩ hk)

private theorem indRep_isMatRep {G : Type} [Group G] [Fintype G] (K : Subgroup G) (T : Set G)
    (hT : Subgroup.IsComplement T (K : Set G)) {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : K → Matrix ι ι ℂ} (hR : IsMatRep R) :
    IsMatRep (indRep K T R) := by
  constructor
  · ext ⟨s, j⟩ ⟨t, i⟩
    simp only [indRep, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq]
    by_cases hst : s = t
    · subst hst
      have hm : (s : G)⁻¹ * 1 * (s : G) ∈ K := by simp [K.one_mem]
      rw [dif_pos hm]
      have h1 : (⟨(s : G)⁻¹ * 1 * (s : G), hm⟩ : K) = 1 := by ext; simp
      rw [h1, hR.1, Matrix.one_apply]
      simp
    · rw [dif_neg]
      · simp [hst]
      · intro hm
        apply hst
        apply isComplement_mul_cancel hT
        simpa using hm
  · intro g₁ g₂
    ext ⟨s, j⟩ ⟨u, l⟩
    rw [Matrix.mul_apply]
    simp only [indRep, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    obtain ⟨t₀, ht₀, ht₀_uniq⟩ := isComplement_existsUnique_left hT g₂ u
    rw [Finset.sum_eq_single t₀]
    · dsimp only
      simp only [dif_pos ht₀]
      by_cases hs : (s : G)⁻¹ * g₁ * (t₀ : G) ∈ K
      · simp only [dif_pos hs]
        have htot : (s : G)⁻¹ * (g₁ * g₂) * (u : G) ∈ K := by
          have := K.mul_mem hs ht₀
          simpa [mul_assoc] using this
        simp only [dif_pos htot]
        have hkeq : (⟨(s : G)⁻¹ * g₁ * (t₀ : G), hs⟩ : K) *
            (⟨(t₀ : G)⁻¹ * g₂ * (u : G), ht₀⟩ : K) =
            ⟨(s : G)⁻¹ * (g₁ * g₂) * (u : G), htot⟩ := by
          ext; simp [mul_assoc]
        change R ⟨(s : G)⁻¹ * (g₁ * g₂) * (u : G), htot⟩ j l =
          (R ⟨(s : G)⁻¹ * g₁ * (t₀ : G), hs⟩ * R ⟨(t₀ : G)⁻¹ * g₂ * (u : G), ht₀⟩) j l
        rw [← hR.2, hkeq]
      · simp only [dif_neg hs]
        have htot : ¬ ((s : G)⁻¹ * (g₁ * g₂) * (u : G) ∈ K) := by
          intro hmem
          apply hs
          have := K.mul_mem hmem (K.inv_mem ht₀)
          simpa [mul_assoc] using this
        simp only [dif_neg htot]
        simp
    · intro t _ hne
      have hnt : ¬ ((t : G)⁻¹ * g₂ * (u : G) ∈ K) := fun hm => hne (ht₀_uniq t hm)
      simp [hnt]
    · intro ht₀_mem
      exact absurd (Finset.mem_univ t₀) ht₀_mem

private theorem indRep_conjTranspose {G : Type} [Group G] [Fintype G] (K : Subgroup G) (T : Set G)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : K → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    (indRep K T R g)ᴴ = indRep K T R g⁻¹ := by
  ext ⟨t, i⟩ ⟨s, j⟩
  simp only [Matrix.conjTranspose_apply, indRep, Matrix.of_apply]
  by_cases h : (s : G)⁻¹ * g * (t : G) ∈ K
  · have h' : (t : G)⁻¹ * g⁻¹ * (s : G) ∈ K := by
      have := K.inv_mem h
      simpa [mul_assoc, mul_inv_rev] using this
    rw [dif_pos h, dif_pos h']
    have hinv : (⟨(t : G)⁻¹ * g⁻¹ * (s : G), h'⟩ : K) =
        (⟨(s : G)⁻¹ * g * (t : G), h⟩ : K)⁻¹ := by
      ext; simp [mul_assoc, mul_inv_rev]
    rw [hinv, isUnitaryRep_inv_eq_conjTranspose hR]
    rfl
  · have h' : ¬ ((t : G)⁻¹ * g⁻¹ * (s : G) ∈ K) := by
      intro hmem
      apply h
      have := K.inv_mem hmem
      simpa [mul_assoc, mul_inv_rev] using this
    rw [dif_neg h, dif_neg h', star_zero]

private theorem indRep_isUnitaryRep {G : Type} [Group G] [Fintype G] (K : Subgroup G) (T : Set G)
    (hT : Subgroup.IsComplement T (K : Set G)) {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : K → Matrix ι ι ℂ} (hR : IsUnitaryRep R) :
    IsUnitaryRep (indRep K T R) := by
  have hmat := indRep_isMatRep K T hT hR.1
  refine ⟨hmat, fun g => ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [Matrix.star_eq_conjTranspose, indRep_conjTranspose K T hR g]
  exact isMatRep_mul_inv hmat g

private theorem indRep_apply_normal {G : Type} [Group G] (N K : Subgroup G) [N.Normal]
    (hNK : ∀ x ∈ N, x ∈ K) (T : Set G) (hT : Subgroup.IsComplement T (K : Set G))
    {ι : Type} [Fintype ι] (R : K → Matrix ι ι ℂ)
    (n : N) (s t : T) (j i : ι) :
    indRep K T R (n : G) (s, j) (t, i) =
      if s = t then R ⟨(t : G)⁻¹ * (n : G) * (t : G), hNK _ (conj_inv_mem N (t : G) n)⟩ j i
      else 0 := by
  simp only [indRep, Matrix.of_apply]
  by_cases hst : s = t
  · subst hst
    have hm : (s : G)⁻¹ * (n : G) * (s : G) ∈ K := hNK _ (conj_inv_mem N (s : G) n)
    rw [dif_pos hm, if_pos rfl]
  · rw [dif_neg, if_neg hst]
    intro hm
    apply hst
    apply isComplement_mul_cancel hT
    have hconj : (s : G)⁻¹ * (n : G) * (s : G) ∈ K := hNK _ (conj_inv_mem N (s : G) n)
    have hmul : (s : G)⁻¹ * (t : G) = ((s : G)⁻¹ * (n : G) * (s : G))⁻¹ *
        ((s : G)⁻¹ * (n : G) * (t : G)) := by
      group
    rw [hmul]
    exact K.mul_mem (K.inv_mem hconj) hm

private theorem indRep_apply_transversal_right {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    (hT : Subgroup.IsComplement T (K : Set G)) (h1 : (1 : G) ∈ T)
    {ι : Type} [Fintype ι] [DecidableEq ι] {R : K → Matrix ι ι ℂ} (hR1 : R 1 = 1)
    (t s : T) (j i : ι) :
    indRep K T R (t : G) (s, j) (⟨1, h1⟩, i) = if s = t ∧ j = i then 1 else 0 := by
  simp only [indRep, Matrix.of_apply]
  by_cases hst : s = t
  · subst hst
    have hm : (s : G)⁻¹ * (s : G) * ((⟨1, h1⟩ : T) : G) ∈ K := by simp [K.one_mem]
    rw [dif_pos hm]
    have h1k : (⟨(s : G)⁻¹ * (s : G) * ((⟨1, h1⟩ : T) : G), hm⟩ : K) = 1 := by ext; simp
    rw [h1k, hR1, Matrix.one_apply]
    simp
  · rw [dif_neg]
    · simp [hst]
    · intro hm
      apply hst
      apply isComplement_mul_cancel hT
      simpa using hm

private theorem indRep_apply_transversal_left {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    (hT : Subgroup.IsComplement T (K : Set G)) (h1 : (1 : G) ∈ T)
    {ι : Type} [Fintype ι] [DecidableEq ι] {R : K → Matrix ι ι ℂ} (hR1 : R 1 = 1)
    (t s : T) (j i : ι) :
    indRep K T R (t : G) (t, j) (s, i) = if s = ⟨1, h1⟩ ∧ j = i then 1 else 0 := by
  simp only [indRep, Matrix.of_apply]
  by_cases hs : s = ⟨1, h1⟩
  · subst hs
    have hm : (t : G)⁻¹ * (t : G) * ((⟨1, h1⟩ : T) : G) ∈ K := by simp [K.one_mem]
    rw [dif_pos hm]
    have h1k : (⟨(t : G)⁻¹ * (t : G) * ((⟨1, h1⟩ : T) : G), hm⟩ : K) = 1 := by ext; simp
    rw [h1k, hR1, Matrix.one_apply]
    simp
  · rw [dif_neg]
    · simp [hs]
    · intro hm
      apply hs
      symm
      apply isComplement_mul_cancel hT
      simpa using hm

private theorem indRep_apply_subgroup_left_one {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    (hT : Subgroup.IsComplement T (K : Set G)) (h1 : (1 : G) ∈ T)
    {ι : Type} [Fintype ι] (R : K → Matrix ι ι ℂ) (k : K) (s : T) (j i : ι) :
    indRep K T R (k : G) (s, j) (⟨1, h1⟩, i) = if s = ⟨1, h1⟩ then R k j i else 0 := by
  simp only [indRep, Matrix.of_apply]
  by_cases hs : s = ⟨1, h1⟩
  · subst hs
    have hm : ((⟨1, h1⟩ : T) : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G) ∈ K := by simp [k.2]
    rw [dif_pos hm, if_pos rfl]
    have hk : (⟨((⟨1, h1⟩ : T) : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G), hm⟩ : K) = k := by
      ext; simp
    rw [hk]
  · rw [dif_neg, if_neg hs]
    intro hm
    apply hs
    symm
    apply isComplement_mul_cancel hT
    have hsinv : (s : G)⁻¹ ∈ K := by
      have := K.mul_mem hm (K.inv_mem k.2)
      simpa using this
    have hsK : (s : G) ∈ K := by simpa using K.inv_mem hsinv
    simpa using hsK

private theorem indRep_apply_subgroup_right_one {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    (hT : Subgroup.IsComplement T (K : Set G)) (h1 : (1 : G) ∈ T)
    {ι : Type} [Fintype ι] (R : K → Matrix ι ι ℂ) (k : K) (s : T) (j i : ι) :
    indRep K T R (k : G) (⟨1, h1⟩, j) (s, i) = if s = ⟨1, h1⟩ then R k j i else 0 := by
  simp only [indRep, Matrix.of_apply]
  by_cases hs : s = ⟨1, h1⟩
  · subst hs
    have hm : ((⟨1, h1⟩ : T) : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G) ∈ K := by simp [k.2]
    rw [dif_pos hm, if_pos rfl]
    have hk : (⟨((⟨1, h1⟩ : T) : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G), hm⟩ : K) = k := by
      ext; simp
    rw [hk]
  · rw [dif_neg, if_neg hs]
    intro hm
    apply hs
    symm
    apply isComplement_mul_cancel hT
    have hsK : (s : G) ∈ K := by
      have := K.mul_mem (K.inv_mem k.2) hm
      simpa using this
    simpa using hsK

/-! ### Section 4: Clifford theory primitives (`transport`, `InOrbit`, `inertia`) -/

private theorem transport_one_fun {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ι : Type} (R : N → Matrix ι ι ℂ) :
    transport N R 1 = R :=
  funext (transport_one N R)

private theorem transport_isMatRep {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : N → Matrix ι ι ℂ} (hR : IsMatRep R) (g : G) :
    IsMatRep (transport N R g) := by
  constructor
  · have h1 : (⟨g⁻¹ * ((1 : N) : G) * g, conj_inv_mem N g 1⟩ : N) = 1 := by ext; simp
    unfold transport
    rw [h1, hR.1]
  · intro m n
    unfold transport
    have hmul : (⟨g⁻¹ * ((m * n : N) : G) * g, conj_inv_mem N g (m * n)⟩ : N) =
        ⟨g⁻¹ * (m : G) * g, conj_inv_mem N g m⟩ * ⟨g⁻¹ * (n : G) * g, conj_inv_mem N g n⟩ := by
      ext; simp [mul_assoc]
    rw [hmul, hR.2]

private theorem transport_isIrreducibleRep {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ι : Type} [Fintype ι]
    {R : N → Matrix ι ι ℂ} (hR : IsIrreducibleRep R) (g : G) :
    IsIrreducibleRep (transport N R g) := by
  refine ⟨hR.1, fun W hW => hR.2 W fun n v hv => ?_⟩
  let m : N := ⟨g * (n : G) * g⁻¹, by simpa using (inferInstance : N.Normal).conj_mem n n.2 g⟩
  have heq : transport N R g m = R n := by
    unfold transport
    congr 1; ext; simp [m, mul_assoc]
  rw [← heq]
  exact hW m v hv

private theorem inOrbit_refl {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (l : ΛN) :
    InOrbit N RN l l := by
  refine ⟨1, ?_⟩
  rw [transport_one_fun]
  exact repEquiv_refl (RN l)

private theorem mem_inertia_of_mem {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : ∀ l, IsMatRep (RN l))
    (l : ΛN) {x : G} (hx : x ∈ N) :
    x ∈ inertia N RN l := by
  let nx : N := ⟨x, hx⟩
  refine ⟨RN l nx, RN l nx⁻¹, isMatRep_mul_inv (hRN l) nx, isMatRep_inv_mul (hRN l) nx, ?_⟩
  intro n _
  unfold transport
  have hconj : (⟨x⁻¹ * (n : G) * x, conj_inv_mem N x n⟩ : N) = nx⁻¹ * n * nx := by
    ext; rfl
  rw [hconj, (hRN l).2, (hRN l).2, Matrix.mul_assoc, ← Matrix.mul_assoc (RN l nx),
    isMatRep_mul_inv (hRN l) nx, Matrix.one_mul]

private theorem repEquiv_transport_conj {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : N → Matrix ι₁ ι₁ ℂ} {R₂ : N → Matrix ι₂ ι₂ ℂ} {t₁ t₂ : G}
    (h : RepEquiv (transport N R₁ t₁) (transport N R₂ t₂)) :
    RepEquiv R₁ (transport N R₂ (t₁⁻¹ * t₂)) := by
  obtain ⟨A, B, hAB, hBA, hinter⟩ := h
  refine ⟨A, B, hAB, hBA, fun m _ => ?_⟩
  let n : N := ⟨t₁ * (m : G) * t₁⁻¹, by simpa using (inferInstance : N.Normal).conj_mem m m.2 t₁⟩
  have hn := hinter n (Set.mem_univ _)
  have e1 : transport N R₁ t₁ n = R₁ m := by
    unfold transport; congr 1; ext; simp [n, mul_assoc]
  have e2 : transport N R₂ t₂ n = transport N R₂ (t₁⁻¹ * t₂) m := by
    unfold transport; congr 1; ext; simp [n, mul_assoc]
  rw [e1, e2] at hn
  exact hn

private theorem repEquiv_transport_mem_inertia {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (σ : ΛN) {t₁ t₂ : G}
    (h : RepEquiv (transport N (RN σ) t₁) (transport N (RN σ) t₂)) :
    t₂⁻¹ * t₁ ∈ inertia N RN σ :=
  repEquiv_symm (repEquiv_transport_conj N (repEquiv_symm h))

/-! ### Section 5: Little-group representation `RI` and intertwiner classification for `Φ` -/

private def littleKernelRep {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    (σ : ΛN) (η : Λη σ) (k : inertia N RN σ) :
    Matrix (BN σ × Bη σ η) (BN σ × Bη σ η) ℂ :=
  Matrix.kronecker (Rext σ k) (inflation N RN σ (Rη σ η) k)

private theorem littleKernelRep_isUnitaryRep {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)] [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    {σ : ΛN} (hRησ : IsIrrepSystem (Rη σ)) (η : Λη σ) :
    IsUnitaryRep (littleKernelRep N RN Rext Rη σ η) :=
  isUnitaryRep_kronecker (hext σ).1 (isUnitaryRep_inflation N RN σ (hRησ.1 η))

private theorem littleKernelRep_apply_normal {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)] [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    {σ : ΛN} (hRησ : IsIrrepSystem (Rη σ)) (η : Λη σ)
    (n : N) (t : G) (i₁ i₂ : BN σ) (j₁ j₂ : Bη σ η) :
    littleKernelRep N RN Rext Rη σ η
      ⟨(t : G)⁻¹ * (n : G) * (t : G),
        mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ (conj_inv_mem N t n)⟩
      (i₁, j₁) (i₂, j₂) =
      if j₁ = j₂ then transport N (RN σ) t n i₁ i₂ else 0 := by
  let x : N.subgroupOf (inertia N RN σ) :=
    ⟨⟨t⁻¹ * (n : G) * t, mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ (conj_inv_mem N t n)⟩,
      conj_inv_mem N t n⟩
  have h1 : Rext σ x.1 = transport N (RN σ) t n := by
    have := (hext σ).2 x
    simpa [inNInertia, inertiaToN, transport, x] using this
  have h2 : inflation N RN σ (Rη σ η) x.1 = 1 := by
    unfold inflation
    have hq : (QuotientGroup.mk x.1 : inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) = 1 :=
      (QuotientGroup.eq_one_iff x.1).mpr x.2
    rw [hq, (hRησ.1 η).1.1]
  change (Matrix.kronecker (Rext σ x.1) (inflation N RN σ (Rη σ η) x.1)) (i₁, j₁) (i₂, j₂) = _
  rw [h1, h2]
  simp only [Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply]
  split_ifs with hj
  · simp
  · simp

private theorem intertwiner_normal_block {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    (T : ΛN → Set G)
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)] [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    {σ σ' : ΛN} (hTσ : Subgroup.IsComplement (T σ) (inertia N RN σ : Set G))
    (hTσ' : Subgroup.IsComplement (T σ') (inertia N RN σ' : Set G))
    (hRησ : IsIrrepSystem (Rη σ)) (hRησ'' : IsIrrepSystem (Rη σ'))
    {η : Λη σ} {η' : Λη σ'}
    {M : Matrix (T σ' × (BN σ' × Bη σ' η')) (T σ × (BN σ × Bη σ η)) ℂ}
    (hM : ∀ g : G,
      M * indRep (inertia N RN σ) (T σ) (littleKernelRep N RN Rext Rη σ η) g =
      indRep (inertia N RN σ') (T σ') (littleKernelRep N RN Rext Rη σ' η') g * M)
    (t' : T σ') (t : T σ) (j' : Bη σ' η') (j : Bη σ η) :
    let B : Matrix (BN σ') (BN σ) ℂ := Matrix.of fun i' i => M (t', (i', j')) (t, (i, j))
    ∀ n : N, B * transport N (RN σ) (t : G) n = transport N (RN σ') (t' : G) n * B := by
  intro B n
  ext i' i
  have hent := congr_fun (congr_fun (hM (n : G)) (t', (i', j'))) (t, (i, j))
  rw [Matrix.mul_apply, Matrix.mul_apply] at hent
  rw [Fintype.sum_prod_type] at hent
  have hLHS : ∑ s : T σ, ∑ x : BN σ × Bη σ η,
      M (t', (i', j')) (s, x) *
        indRep (inertia N RN σ) (T σ) (littleKernelRep N RN Rext Rη σ η) (n : G) (s, x) (t, (i, j)) =
      (B * transport N (RN σ) (t : G) n) i' i := by
    rw [Finset.sum_eq_single t]
    · rw [Fintype.sum_prod_type_right, Finset.sum_eq_single j]
      · simp only [Matrix.mul_apply, B, Matrix.of_apply]
        refine Finset.sum_congr rfl fun i₁ _ => ?_
        rw [indRep_apply_normal N (inertia N RN σ)
          (fun _ hx => mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ hx) (T σ) hTσ
          (littleKernelRep N RN Rext Rη σ η) n t t (i₁, j) (i, j), if_pos rfl]
        rw [littleKernelRep_apply_normal N RN hRN Rext hext Rη hRησ η n (t : G) i₁ i j j,
          if_pos rfl]
      · intro j₁ _ hj₁
        refine Finset.sum_eq_zero fun i₁ _ => ?_
        rw [indRep_apply_normal N (inertia N RN σ)
          (fun _ hx => mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ hx) (T σ) hTσ
          (littleKernelRep N RN Rext Rη σ η) n t t (i₁, j₁) (i, j), if_pos rfl]
        rw [littleKernelRep_apply_normal N RN hRN Rext hext Rη hRησ η n (t : G) i₁ i j₁ j,
          if_neg hj₁, mul_zero]
      · intro hj_mem; exact absurd (Finset.mem_univ j) hj_mem
    · intro s _ hs
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [indRep_apply_normal N (inertia N RN σ)
        (fun _ hx => mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ hx) (T σ) hTσ
        (littleKernelRep N RN Rext Rη σ η) n s t x (i, j), if_neg hs, mul_zero]
    · intro ht_mem; exact absurd (Finset.mem_univ t) ht_mem
  rw [Fintype.sum_prod_type] at hent
  have hRHS : ∑ s' : T σ', ∑ x' : BN σ' × Bη σ' η',
      indRep (inertia N RN σ') (T σ') (littleKernelRep N RN Rext Rη σ' η') (n : G) (t', (i', j')) (s', x') *
        M (s', x') (t, (i, j)) =
      (transport N (RN σ') (t' : G) n * B) i' i := by
    rw [Finset.sum_eq_single t']
    · rw [Fintype.sum_prod_type_right, Finset.sum_eq_single j']
      · simp only [Matrix.mul_apply, B, Matrix.of_apply]
        refine Finset.sum_congr rfl fun i₁' _ => ?_
        rw [indRep_apply_normal N (inertia N RN σ')
          (fun _ hx => mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ' hx) (T σ') hTσ'
          (littleKernelRep N RN Rext Rη σ' η') n t' t' (i', j') (i₁', j'), if_pos rfl]
        rw [littleKernelRep_apply_normal N RN hRN Rext hext Rη hRησ'' η' n (t' : G) i' i₁' j' j',
          if_pos rfl]
      · intro j₁' _ hj₁'
        refine Finset.sum_eq_zero fun i₁' _ => ?_
        rw [indRep_apply_normal N (inertia N RN σ')
          (fun _ hx => mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ' hx) (T σ') hTσ'
          (littleKernelRep N RN Rext Rη σ' η') n t' t' (i', j') (i₁', j₁'), if_pos rfl]
        rw [littleKernelRep_apply_normal N RN hRN Rext hext Rη hRησ'' η' n (t' : G) i' i₁' j' j₁',
          if_neg hj₁'.symm, zero_mul]
      · intro hj'_mem; exact absurd (Finset.mem_univ j') hj'_mem
    · intro s' _ hs'
      refine Finset.sum_eq_zero fun x' _ => ?_
      rw [indRep_apply_normal N (inertia N RN σ')
        (fun _ hx => mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ' hx) (T σ') hTσ'
        (littleKernelRep N RN Rext Rη σ' η') n t' s' (i', j') x', if_neg hs'.symm, zero_mul]
    · intro ht'_mem; exact absurd (Finset.mem_univ t') ht'_mem
  rw [hLHS, hRHS] at hent
  exact hent

private theorem intertwiner_eq_zero_of_ne_sigma {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O) (T : ΛN → Set G)
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)] [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    {σ σ' : ΛN} (hσ : σ ∈ O) (hσ' : σ' ∈ O) (hne : σ ≠ σ')
    (hTσ : Subgroup.IsComplement (T σ) (inertia N RN σ : Set G))
    (hTσ' : Subgroup.IsComplement (T σ') (inertia N RN σ' : Set G))
    (hRησ : IsIrrepSystem (Rη σ)) (hRησ' : IsIrrepSystem (Rη σ'))
    {η : Λη σ} {η' : Λη σ'}
    {M : Matrix (T σ' × (BN σ' × Bη σ' η')) (T σ × (BN σ × Bη σ η)) ℂ}
    (hM : ∀ g : G,
      M * indRep (inertia N RN σ) (T σ) (littleKernelRep N RN Rext Rη σ η) g =
      indRep (inertia N RN σ') (T σ') (littleKernelRep N RN Rext Rη σ' η') g * M) :
    M = 0 := by
  ext ⟨t', i', j'⟩ ⟨t, i, j⟩
  have hB := intertwiner_normal_block N RN hRN Rext hext T Rη hTσ hTσ' hRησ hRησ' hM t' t j' j
  have hnot : ¬ RepEquiv (transport N (RN σ) (t : G)) (transport N (RN σ') (t' : G)) := by
    intro hrep
    have hin : InOrbit N RN σ σ' := ⟨(t : G)⁻¹ * (t' : G), repEquiv_transport_conj N hrep⟩
    have huniq := (hO σ).unique (y₁ := ⟨σ, hσ⟩) (y₂ := ⟨σ', hσ'⟩) (inOrbit_refl N RN σ) hin
    exact hne (congrArg Subtype.val huniq)
  have hB0 := schur_zero_of_not_repEquiv
    (transport_isIrreducibleRep N (hRN.2.1 σ) (t : G))
    (transport_isIrreducibleRep N (hRN.2.1 σ') (t' : G))
    hnot hB
  exact congr_fun (congr_fun hB0 i') i

private theorem intertwiner_same_sigma_structure {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    (T : ΛN → Set G)
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)] [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    {σ : ΛN}
    (hTσ : Subgroup.IsComplement (T σ) (inertia N RN σ : Set G)) (h1 : (1 : G) ∈ T σ)
    (hRησ : IsIrrepSystem (Rη σ))
    {η η' : Λη σ}
    {M : Matrix (T σ × (BN σ × Bη σ η')) (T σ × (BN σ × Bη σ η)) ℂ}
    (hM : ∀ g : G,
      M * indRep (inertia N RN σ) (T σ) (littleKernelRep N RN Rext Rη σ η) g =
      indRep (inertia N RN σ) (T σ) (littleKernelRep N RN Rext Rη σ η') g * M) :
    (∀ t' t : T σ, t' ≠ t → ∀ x' x, M (t', x') (t, x) = 0) ∧
    (∃ C : Matrix (Bη σ η') (Bη σ η) ℂ,
      (∀ t : T σ, ∀ i' j' i j,
        M (t, (i', j')) (t, (i, j)) = (1 : Matrix (BN σ) (BN σ) ℂ) i' i * C j' j) ∧
      (∀ q : inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ),
        C * Rη σ η q = Rη σ η' q * C)) := by
  have hdiag : ∀ t' t : T σ, t' ≠ t → ∀ x' x, M (t', x') (t, x) = 0 := by
    intro t' t hne ⟨i', j'⟩ ⟨i, j⟩
    have hB := intertwiner_normal_block N RN hRN Rext hext T Rη hTσ hTσ hRησ hRησ hM t' t j' j
    have hnot : ¬ RepEquiv (transport N (RN σ) (t : G)) (transport N (RN σ) (t' : G)) := by
      intro hrep
      apply hne
      exact isComplement_mul_cancel hTσ (repEquiv_transport_mem_inertia N RN σ hrep)
    have hB0 := schur_zero_of_not_repEquiv
      (transport_isIrreducibleRep N (hRN.2.1 σ) (t : G))
      (transport_isIrreducibleRep N (hRN.2.1 σ) (t' : G))
      hnot hB
    exact congr_fun (congr_fun hB0 i') i
  let t₁ : T σ := ⟨1, h1⟩
  have hblk1 : ∀ j' : Bη σ η', ∀ j : Bη σ η,
      ∃ c : ℂ, (Matrix.of fun i' i => M (t₁, (i', j')) (t₁, (i, j))) =
        c • (1 : Matrix (BN σ) (BN σ) ℂ) := by
    intro j' j
    have hB := intertwiner_normal_block N RN hRN Rext hext T Rη hTσ hTσ hRησ hRησ hM t₁ t₁ j' j
    have hBcomm : ∀ n : N, RN σ n * (Matrix.of fun i' i => M (t₁, (i', j')) (t₁, (i, j))) =
        (Matrix.of fun i' i => M (t₁, (i', j')) (t₁, (i, j))) * RN σ n := by
      intro n
      have hn := hB n
      change _ * transport N (RN σ) (1 : G) n = transport N (RN σ) (1 : G) n * _ at hn
      rw [transport_one_fun] at hn
      exact hn.symm
    exact schur_eq_smul_one (hRN.2.1 σ) hBcomm
  let C : Matrix (Bη σ η') (Bη σ η) ℂ := Matrix.of fun j' j => Classical.choose (hblk1 j' j)
  have hC1 : ∀ i' j' i j,
      M (t₁, (i', j')) (t₁, (i, j)) = (1 : Matrix (BN σ) (BN σ) ℂ) i' i * C j' j := by
    intro i' j' i j
    have hspec := Classical.choose_spec (hblk1 j' j)
    have hent := congr_fun (congr_fun hspec i') i
    simpa [C, mul_comm] using hent
  have hsame : ∀ t : T σ, ∀ x' x, M (t, x') (t, x) = M (t₁, x') (t₁, x) := by
    intro t x' x
    have hent := congr_fun (congr_fun (hM (t : G)) (t, x')) (t₁, x)
    rw [Matrix.mul_apply, Matrix.mul_apply] at hent
    have hL : ∑ z : T σ × (BN σ × Bη σ η),
        M (t, x') z * indRep (inertia N RN σ) (T σ) (littleKernelRep N RN Rext Rη σ η) (t : G) z (t₁, x) =
        M (t, x') (t, x) := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single x]
        · rw [indRep_apply_transversal_right (inertia N RN σ) (T σ) hTσ h1
            (littleKernelRep_isUnitaryRep N RN Rext hext Rη hRησ η).1.1 t t x x]
          simp
        · intro y _ hy
          rw [indRep_apply_transversal_right (inertia N RN σ) (T σ) hTσ h1
            (littleKernelRep_isUnitaryRep N RN Rext hext Rη hRησ η).1.1 t t y x]
          simp [hy]
        · intro hx_mem; exact absurd (Finset.mem_univ x) hx_mem
      · intro s _ hs
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [indRep_apply_transversal_right (inertia N RN σ) (T σ) hTσ h1
          (littleKernelRep_isUnitaryRep N RN Rext hext Rη hRησ η).1.1 t s y x]
        simp [hs]
      · intro ht_mem; exact absurd (Finset.mem_univ t) ht_mem
    have hR : ∑ z : T σ × (BN σ × Bη σ η'),
        indRep (inertia N RN σ) (T σ) (littleKernelRep N RN Rext Rη σ η') (t : G) (t, x') z *
          M z (t₁, x) =
        M (t₁, x') (t₁, x) := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single t₁]
      · rw [Finset.sum_eq_single x']
        · rw [indRep_apply_transversal_left (inertia N RN σ) (T σ) hTσ h1
            (littleKernelRep_isUnitaryRep N RN Rext hext Rη hRησ η').1.1 t t₁ x' x']
          dsimp only [t₁]
          simp
        · intro y _ hy
          rw [indRep_apply_transversal_left (inertia N RN σ) (T σ) hTσ h1
            (littleKernelRep_isUnitaryRep N RN Rext hext Rη hRησ η').1.1 t t₁ x' y]
          simp [hy.symm]
        · intro hx'_mem; exact absurd (Finset.mem_univ x') hx'_mem
      · intro s _ hs
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [indRep_apply_transversal_left (inertia N RN σ) (T σ) hTσ h1
          (littleKernelRep_isUnitaryRep N RN Rext hext Rη hRησ η').1.1 t s x' y]
        have hs' : s ≠ ⟨1, h1⟩ := hs
        simp [hs']
      · intro ht₁_mem; exact absurd (Finset.mem_univ t₁) ht₁_mem
    rw [hL, hR] at hent
    exact hent
  have hC_inter : ∀ q : inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ),
      C * Rη σ η q = Rη σ η' q * C := by
    intro q
    refine QuotientGroup.induction_on q fun k => ?_
    have hM₁₁ : Matrix.kronecker (1 : Matrix (BN σ) (BN σ) ℂ) C *
          littleKernelRep N RN Rext Rη σ η k =
        littleKernelRep N RN Rext Rη σ η' k *
          Matrix.kronecker (1 : Matrix (BN σ) (BN σ) ℂ) C := by
      ext ⟨i', j'⟩ ⟨i, j⟩
      have hent := congr_fun (congr_fun (hM (k : G)) (t₁, (i', j'))) (t₁, (i, j))
      rw [Matrix.mul_apply, Matrix.mul_apply] at hent
      rw [Fintype.sum_prod_type] at hent
      have hL : ∑ s : T σ, ∑ y : BN σ × Bη σ η,
          M (t₁, (i', j')) (s, y) *
            indRep (inertia N RN σ) (T σ) (littleKernelRep N RN Rext Rη σ η) (k : G) (s, y) (t₁, (i, j)) =
          (Matrix.kronecker (1 : Matrix (BN σ) (BN σ) ℂ) C *
            littleKernelRep N RN Rext Rη σ η k) (i', j') (i, j) := by
        rw [Finset.sum_eq_single t₁]
        · rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [indRep_apply_subgroup_left_one (inertia N RN σ) (T σ) hTσ h1
            (littleKernelRep N RN Rext Rη σ η) k t₁ y (i, j), if_pos rfl]
          rcases y with ⟨i₁, j₁⟩
          rw [hC1 i' j' i₁ j₁]
          simp [Matrix.kronecker]
        · intro s _ hs
          refine Finset.sum_eq_zero fun y _ => ?_
          rw [indRep_apply_subgroup_left_one (inertia N RN σ) (T σ) hTσ h1
            (littleKernelRep N RN Rext Rη σ η) k s y (i, j), if_neg hs, mul_zero]
        · intro ht₁_mem; exact absurd (Finset.mem_univ t₁) ht₁_mem
      rw [Fintype.sum_prod_type] at hent
      have hR : ∑ s : T σ, ∑ y : BN σ × Bη σ η',
          indRep (inertia N RN σ) (T σ) (littleKernelRep N RN Rext Rη σ η') (k : G) (t₁, (i', j')) (s, y) *
            M (s, y) (t₁, (i, j)) =
          (littleKernelRep N RN Rext Rη σ η' k *
            Matrix.kronecker (1 : Matrix (BN σ) (BN σ) ℂ) C) (i', j') (i, j) := by
        rw [Finset.sum_eq_single t₁]
        · rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [indRep_apply_subgroup_right_one (inertia N RN σ) (T σ) hTσ h1
            (littleKernelRep N RN Rext Rη σ η') k t₁ (i', j') y, if_pos rfl]
          rcases y with ⟨i₁, j₁⟩
          rw [hC1 i₁ j₁ i j]
          simp [Matrix.kronecker]
        · intro s _ hs
          refine Finset.sum_eq_zero fun y _ => ?_
          rw [indRep_apply_subgroup_right_one (inertia N RN σ) (T σ) hTσ h1
            (littleKernelRep N RN Rext Rη σ η') k s (i', j') y, if_neg hs, zero_mul]
        · intro ht₁_mem; exact absurd (Finset.mem_univ t₁) ht₁_mem
      rw [hL, hR] at hent
      exact hent
    have hkron :
        Matrix.kronecker (Rext σ k) (C * Rη σ η (QuotientGroup.mk k)) =
        Matrix.kronecker (Rext σ k) (Rη σ η' (QuotientGroup.mk k) * C) := by
      simpa [littleKernelRep, inflation, ← Matrix.mul_kronecker_mul] using hM₁₁
    have : Nonempty (BN σ) := (hRN.2.1 σ).1
    have hne0 : Rext σ k ≠ 0 := isUnitaryRep_ne_zero (hext σ).1 k
    have hex_nz : ∃ i₀ i₁ : BN σ, Rext σ k i₀ i₁ ≠ 0 := by
      by_contra h
      push Not at h
      apply hne0
      ext i₀ i₁
      exact h i₀ i₁
    obtain ⟨i₀, i₁, hi₀₁⟩ := hex_nz
    ext j' j
    have hent := congr_fun (congr_fun hkron (i₀, j')) (i₁, j)
    simp only [Matrix.kronecker, Matrix.kronecker_apply] at hent
    exact mul_left_cancel₀ hi₀₁ hent
  refine ⟨hdiag, C, ?_, hC_inter⟩
  intro t i' j' i j
  rw [hsame t (i', j') (i, j)]
  exact hC1 i' j' i j

/-! ### Section 6: Clifford–Gallagher surjectivity (Clause 3) -/

private theorem exists_N_intertwiner {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ_mat : IsMatRep ρ) (hρ_irr : IsIrreducibleRep ρ) :
    ∃ (σ : O) (A : Matrix ι (BN σ.1) ℂ),
      A ≠ 0 ∧ ∀ n : N, A * RN σ.1 n = ρ (n : G) * A := by
  have : Nonempty ι := hρ_irr.1
  let ρN : N → Matrix ι ι ℂ := fun n => ρ (n : G)
  have hρN_mat : IsMatRep ρN := ⟨hρ_mat.1, fun m n => hρ_mat.2 m n⟩
  have htop_ne : (⊤ : Submodule ℂ (ι → ℂ)) ≠ ⊥ := by
    intro h
    have i₀ : ι := Classical.arbitrary ι
    have hv : (Pi.single i₀ (1 : ℂ) : ι → ℂ) ∈ (⊥ : Submodule ℂ (ι → ℂ)) :=
      h ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hv
    have := congr_fun hv i₀
    simp at this
  have htop_inv : IsInvariantSubspace ρN ⊤ := fun _ _ _ => Submodule.mem_top
  obtain ⟨d, U, b, hUinv, _, _, hρU_mat, hρU_irr⟩ :=
    exists_min_invariant_subrep hρN_mat htop_ne htop_inv
  let L_U : N → U →ₗ[ℂ] U := fun n =>
    { toFun := fun u => ⟨ρN n *ᵥ u.1, hUinv n u.1 u.2⟩
      map_add' := fun u₁ u₂ => Subtype.ext (Matrix.mulVec_add _ _ _)
      map_smul' := fun c u => Subtype.ext (Matrix.mulVec_smul _ _ _) }
  let ρ_U : N → Matrix (Fin d) (Fin d) ℂ := fun n => LinearMap.toMatrix b b (L_U n)
  change IsMatRep ρ_U at hρU_mat
  change IsIrreducibleRep ρ_U at hρU_irr
  obtain ⟨l, A₀, B₀, _, hBA₀, hinter₀⟩ := hRN.2.2.2 (Fin d) ρ_U hρU_mat hρU_irr
  let E : Matrix ι (Fin d) ℂ := Matrix.of fun i j => (b j : ι → ℂ) i
  have hE_inj : Function.Injective E.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    have hvU : (∑ j : Fin d, v j • b j : U) = 0 := by
      apply Subtype.ext
      ext i
      have hi := congr_fun hv i
      simpa [E, Matrix.mulVec, dotProduct, mul_comm, Finset.sum_apply, Pi.smul_apply] using hi
    have hlin := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hlin
    ext j
    exact hlin v hvU j
  have hE_inter : ∀ n : N, E * ρ_U n = ρN n * E := by
    intro n
    ext i j
    have hL : (L_U n (b j) : ι → ℂ) i = (ρN n * E) i j := by
      simp [L_U, E, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hR : (E * ρ_U n) i j = (L_U n (b j) : ι → ℂ) i := by
      have hrepr : L_U n (b j) = ∑ j' : Fin d, ρ_U n j' j • b j' := by
        conv_lhs => rw [← b.sum_repr (L_U n (b j))]
        refine Finset.sum_congr rfl fun j' _ => ?_
        dsimp only [ρ_U]
        rw [LinearMap.toMatrix_apply]
      have := congr_fun (congrArg Subtype.val hrepr) i
      simpa [E, Matrix.mul_apply, mul_comm, Finset.sum_apply, Pi.smul_apply] using this.symm
    exact hR.trans hL
  let A₁ : Matrix ι (BN l) ℂ := E * A₀
  have hA₁_ne : A₁ ≠ 0 := by
    intro h0
    have : Nonempty (BN l) := (hRN.2.1 l).1
    have i₀ : BN l := Classical.arbitrary (BN l)
    let w : Fin d → ℂ := A₀ *ᵥ Pi.single i₀ 1
    have hEw : E.mulVecLin w = 0 := by
      change E *ᵥ (A₀ *ᵥ Pi.single i₀ 1) = 0
      rw [Matrix.mulVec_mulVec]
      change A₁ *ᵥ Pi.single i₀ 1 = 0
      rw [h0, Matrix.zero_mulVec]
    have hw0 : w = 0 := hE_inj (by simpa using hEw)
    have hB0 : B₀ *ᵥ w = Pi.single i₀ (1 : ℂ) := by
      dsimp [w]
      rw [Matrix.mulVec_mulVec, hBA₀, Matrix.one_mulVec]
    rw [hw0, Matrix.mulVec_zero] at hB0
    have := congr_fun hB0 i₀
    simp at this
  have hA₁_inter : ∀ n : N, A₁ * RN l n = ρN n * A₁ := by
    intro n
    calc A₁ * RN l n = E * (A₀ * RN l n) := Matrix.mul_assoc _ _ _
      _ = E * (ρ_U n * A₀) := by rw [hinter₀ n (Set.mem_univ _)]
      _ = (E * ρ_U n) * A₀ := (Matrix.mul_assoc _ _ _).symm
      _ = (ρN n * E) * A₀ := by rw [hE_inter n]
      _ = ρN n * A₁ := Matrix.mul_assoc _ _ _
  obtain ⟨σ, ⟨g₀, C₀, D₀, hCD₀, hDC₀, hinterC⟩, _⟩ := hO l
  let A₂ : Matrix ι (BN σ.1) ℂ := A₁ * D₀
  have hA₂_ne : A₂ ≠ 0 := by
    intro h0
    have : A₂ * C₀ = A₁ := by rw [Matrix.mul_assoc, hDC₀, Matrix.mul_one]
    rw [h0, Matrix.zero_mul] at this
    exact hA₁_ne this.symm
  have hA₂_inter : ∀ n : N, A₂ * transport N (RN σ.1) g₀ n = ρN n * A₂ := by
    intro n
    have hD : D₀ * transport N (RN σ.1) g₀ n = RN l n * D₀ := by
      calc D₀ * transport N (RN σ.1) g₀ n
          = D₀ * transport N (RN σ.1) g₀ n * (C₀ * D₀) := by rw [hCD₀, Matrix.mul_one]
        _ = D₀ * (transport N (RN σ.1) g₀ n * C₀) * D₀ := by simp only [Matrix.mul_assoc]
        _ = D₀ * (C₀ * RN l n) * D₀ := by rw [hinterC n (Set.mem_univ _)]
        _ = (D₀ * C₀) * RN l n * D₀ := by simp only [Matrix.mul_assoc]
        _ = RN l n * D₀ := by rw [hDC₀, Matrix.one_mul]
    calc A₂ * transport N (RN σ.1) g₀ n
        = A₁ * (D₀ * transport N (RN σ.1) g₀ n) := Matrix.mul_assoc _ _ _
      _ = A₁ * (RN l n * D₀) := by rw [hD]
      _ = (A₁ * RN l n) * D₀ := (Matrix.mul_assoc _ _ _).symm
      _ = (ρN n * A₁) * D₀ := by rw [hA₁_inter n]
      _ = ρN n * A₂ := Matrix.mul_assoc _ _ _
  let A : Matrix ι (BN σ.1) ℂ := ρ g₀⁻¹ * A₂
  refine ⟨σ, A, ?_, ?_⟩
  · intro h0
    have : ρ g₀ * A = A₂ := by
      dsimp [A]
      rw [← Matrix.mul_assoc, isMatRep_mul_inv hρ_mat g₀, Matrix.one_mul]
    rw [h0, Matrix.mul_zero] at this
    exact hA₂_ne this.symm
  · intro m
    let n : N := ⟨g₀ * (m : G) * g₀⁻¹, by
      simpa using (inferInstance : N.Normal).conj_mem m m.2 g₀⟩
    have ht : transport N (RN σ.1) g₀ n = RN σ.1 m := by
      unfold transport; congr 1; ext; simp [n, mul_assoc]
    have hconj : ρ g₀⁻¹ * ρ (n : G) = ρ (m : G) * ρ g₀⁻¹ := by
      rw [← hρ_mat.2, ← hρ_mat.2]
      congr 1
      simp [n, mul_assoc]
    calc A * RN σ.1 m
        = ρ g₀⁻¹ * (A₂ * transport N (RN σ.1) g₀ n) := by rw [ht, Matrix.mul_assoc]
      _ = ρ g₀⁻¹ * (ρN n * A₂) := by rw [hA₂_inter n]
      _ = (ρ g₀⁻¹ * ρ (n : G)) * A₂ := (Matrix.mul_assoc _ _ _).symm
      _ = (ρ (m : G) * ρ g₀⁻¹) * A₂ := by rw [hconj]
      _ = ρ (m : G) * A := Matrix.mul_assoc _ _ _

private theorem exists_little_intertwiner {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)] [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    (σ : ΛN) (hRησ : IsIrrepSystem (Rη σ))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ_mat : IsMatRep ρ)
    (A₀ : Matrix ι (BN σ) ℂ) (hA₀_ne : A₀ ≠ 0)
    (hA₀_inter : ∀ n : N, A₀ * RN σ n = ρ (n : G) * A₀) :
    ∃ (η : Λη σ) (W_I : Matrix ι (BN σ × Bη σ η) ℂ),
      W_I ≠ 0 ∧ ∀ k : inertia N RN σ,
        W_I * littleKernelRep N RN Rext Rη σ η k = ρ (k : G) * W_I := by
  let H : Submodule ℂ (Matrix ι (BN σ) ℂ) :=
    { carrier := {B | ∀ n : N, B * RN σ n = ρ (n : G) * B}
      zero_mem' := fun n => by simp
      add_mem' := fun {B₁ B₂} h₁ h₂ n => by
        rw [Matrix.add_mul, Matrix.mul_add, h₁ n, h₂ n]
      smul_mem' := fun c {B} hB n => by
        rw [Matrix.smul_mul, Matrix.mul_smul, hB n] }
  have hH_ne : H ≠ ⊥ := by
    intro hbot
    apply hA₀_ne
    have hmem : A₀ ∈ (⊥ : Submodule ℂ (Matrix ι (BN σ) ℂ)) := hbot ▸ hA₀_inter
    simpa [Submodule.mem_bot] using hmem
  have hconj_Rext : ∀ (k : inertia N RN σ) (n : N),
      Rext σ k⁻¹ * RN σ n =
        RN σ ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * Rext σ k⁻¹ := by
    intro k n
    let n' : N := ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩
    let x : N.subgroupOf (inertia N RN σ) :=
      ⟨⟨(n : G), mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ n.2⟩, n.2⟩
    let x' : N.subgroupOf (inertia N RN σ) :=
      ⟨⟨(n' : G), mem_inertia_of_mem N RN (fun l => (hRN.1 l).1) σ n'.2⟩, n'.2⟩
    have hx : Rext σ (inNInertia N RN σ x) = RN σ n := by
      simpa [inertiaToN] using (hext σ).2 x
    have hx' : Rext σ (inNInertia N RN σ x') = RN σ n' := by
      simpa [inertiaToN] using (hext σ).2 x'
    have hI : k⁻¹ * inNInertia N RN σ x = inNInertia N RN σ x' * k⁻¹ := by
      ext; simp [inNInertia, x, x', n', mul_assoc]
    have hm := congrArg (Rext σ) hI
    rw [(hext σ).1.1.2, (hext σ).1.1.2, hx, hx'] at hm
    exact hm
  let π_fun : inertia N RN σ → Module.End ℂ H := fun k =>
    { toFun := fun B => ⟨ρ (k : G) * B.1 * Rext σ k⁻¹, fun n => by
        let n' : N := ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩
        have hkρ : ρ (k : G) * ρ (n' : G) = ρ (n : G) * ρ (k : G) := by
          rw [← hρ_mat.2, ← hρ_mat.2]
          congr 1
          dsimp [n']
          group
        calc (ρ (k : G) * B.1 * Rext σ k⁻¹) * RN σ n
            = ρ (k : G) * B.1 * (Rext σ k⁻¹ * RN σ n) := by simp only [Matrix.mul_assoc]
          _ = ρ (k : G) * B.1 * (RN σ n' * Rext σ k⁻¹) := by rw [hconj_Rext k n]
          _ = ρ (k : G) * (B.1 * RN σ n') * Rext σ k⁻¹ := by simp only [Matrix.mul_assoc]
          _ = ρ (k : G) * (ρ (n' : G) * B.1) * Rext σ k⁻¹ := by rw [B.2 n']
          _ = (ρ (k : G) * ρ (n' : G)) * B.1 * Rext σ k⁻¹ := by simp only [Matrix.mul_assoc]
          _ = (ρ (n : G) * ρ (k : G)) * B.1 * Rext σ k⁻¹ := by rw [hkρ]
          _ = ρ (n : G) * (ρ (k : G) * B.1 * Rext σ k⁻¹) := by simp only [Matrix.mul_assoc]⟩
      map_add' := fun B₁ B₂ => Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
      map_smul' := fun c B => Subtype.ext (by simp [Matrix.mul_smul, Matrix.smul_mul]) }
  let π_hom : inertia N RN σ →* Module.End ℂ H :=
    { toFun := π_fun
      map_one' := by
        refine LinearMap.ext fun B => Subtype.ext ?_
        simp [π_fun, hρ_mat.1, (hext σ).1.1.1]
      map_mul' := fun k₁ k₂ => by
        refine LinearMap.ext fun B => Subtype.ext ?_
        change ρ ((k₁ : G) * (k₂ : G)) * B.1 * Rext σ (k₁ * k₂)⁻¹ =
          ρ (k₁ : G) * (ρ (k₂ : G) * B.1 * Rext σ k₂⁻¹) * Rext σ k₁⁻¹
        rw [hρ_mat.2, mul_inv_rev, (hext σ).1.1.2]
        simp only [Matrix.mul_assoc] }
  have hker : N.subgroupOf (inertia N RN σ) ≤ π_hom.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    refine LinearMap.ext fun B => Subtype.ext ?_
    change ρ (k : G) * B.1 * Rext σ k⁻¹ = B.1
    let x : N.subgroupOf (inertia N RN σ) := ⟨k, hk⟩
    let xinv : N.subgroupOf (inertia N RN σ) := ⟨k⁻¹, Subgroup.inv_mem _ hk⟩
    have hxinv : Rext σ k⁻¹ = RN σ (inertiaToN N RN σ x)⁻¹ := by
      have h1 := (hext σ).2 xinv
      have h2 : inNInertia N RN σ xinv = k⁻¹ := rfl
      have h3 : inertiaToN N RN σ xinv = (inertiaToN N RN σ x)⁻¹ := by ext; rfl
      rw [h2, h3] at h1
      exact h1
    rw [hxinv]
    change ρ (inertiaToN N RN σ x : G) * B.1 * RN σ (inertiaToN N RN σ x)⁻¹ = B.1
    rw [← B.2 (inertiaToN N RN σ x), Matrix.mul_assoc,
      isMatRep_mul_inv (hRN.1 σ).1 (inertiaToN N RN σ x), Matrix.mul_one]
  let Hσ := inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)
  let π_quot : Hσ →* Module.End ℂ H := QuotientGroup.lift (N.subgroupOf (inertia N RN σ)) π_hom hker
  have : FiniteDimensional ℂ H := inferInstance
  have : Nontrivial H := Submodule.nontrivial_iff_ne_bot.mpr hH_ne
  let m := Module.finrank ℂ H
  have hm_pos : 0 < m := Module.finrank_pos
  let bH : Module.Basis (Fin m) ℂ H := Module.finBasisOfFinrankEq ℂ H rfl
  let ρ_H : Hσ → Matrix (Fin m) (Fin m) ℂ := fun q => LinearMap.toMatrix bH bH (π_quot q)
  have hρH_mat : IsMatRep ρ_H := by
    constructor
    · simp [ρ_H]
    · intro q₁ q₂
      dsimp only [ρ_H]
      rw [map_mul]
      change LinearMap.toMatrix bH bH ((π_quot q₁).comp (π_quot q₂)) =
        LinearMap.toMatrix bH bH (π_quot q₁) * LinearMap.toMatrix bH bH (π_quot q₂)
      rw [LinearMap.toMatrix_comp bH bH bH]
  have htop_ne : (⊤ : Submodule ℂ (Fin m → ℂ)) ≠ ⊥ := by
    intro h
    have hv : (Pi.single ⟨0, hm_pos⟩ (1 : ℂ) : Fin m → ℂ) ∈ (⊥ : Submodule ℂ (Fin m → ℂ)) :=
      h ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hv
    have := congr_fun hv ⟨0, hm_pos⟩
    simp at this
  have htop_inv : IsInvariantSubspace ρ_H ⊤ := fun _ _ _ => Submodule.mem_top
  obtain ⟨d, U, bU, hUinv, _, _, hρU_mat, hρU_irr⟩ :=
    exists_min_invariant_subrep hρH_mat htop_ne htop_inv
  let L_U : Hσ → U →ₗ[ℂ] U := fun q =>
    { toFun := fun u => ⟨ρ_H q *ᵥ u.1, hUinv q u.1 u.2⟩
      map_add' := fun u₁ u₂ => Subtype.ext (by simp [Matrix.mulVec_add])
      map_smul' := fun c u => Subtype.ext (by simp [Matrix.mulVec_smul]) }
  let ρ_U : Hσ → Matrix (Fin d) (Fin d) ℂ := fun q => LinearMap.toMatrix bU bU (L_U q)
  change IsMatRep ρ_U at hρU_mat
  change IsIrreducibleRep ρ_U at hρU_irr
  obtain ⟨η, P, Q, _, hQP, hPQ_inter⟩ := hRησ.2.2.2 (Fin d) ρ_U hρU_mat hρU_irr
  let L : (Bη σ η → ℂ) →ₗ[ℂ] H :=
    bH.equivFun.symm.toLinearMap.comp (U.subtype.comp (bU.equivFun.symm.toLinearMap.comp P.mulVecLin))
  have hL_inj : Function.Injective L := by
    apply bH.equivFun.symm.injective.comp
    apply Subtype.coe_injective.comp
    apply bU.equivFun.symm.injective.comp
    intro v₁ v₂ hv
    have := congrArg (Q *ᵥ ·) hv
    simpa [Matrix.mulVec_mulVec, hQP] using this
  have hL_inter : ∀ (q : Hσ) (v : Bη σ η → ℂ), L (Rη σ η q *ᵥ v) = π_quot q (L v) := by
    intro q v
    have h1 : P.mulVecLin (Rη σ η q *ᵥ v) = ρ_U q *ᵥ P.mulVecLin v := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hPQ_inter q (Set.mem_univ _)]
    have h2 : bU.equivFun.symm (ρ_U q *ᵥ P.mulVecLin v) =
        L_U q (bU.equivFun.symm (P.mulVecLin v)) :=
      (basis_toLin_equivFun_symm bU (L_U q) (P.mulVecLin v)).symm
    have h3 : (U.subtype (L_U q (bU.equivFun.symm (P.mulVecLin v)))) =
        ρ_H q *ᵥ (U.subtype (bU.equivFun.symm (P.mulVecLin v))) := rfl
    have h4 : bH.equivFun.symm (ρ_H q *ᵥ (U.subtype (bU.equivFun.symm (P.mulVecLin v)))) =
        π_quot q (bH.equivFun.symm (U.subtype (bU.equivFun.symm (P.mulVecLin v)))) :=
      (basis_toLin_equivFun_symm bH (π_quot q)
        (U.subtype (bU.equivFun.symm (P.mulVecLin v)))).symm
    change bH.equivFun.symm (U.subtype (bU.equivFun.symm (P.mulVecLin (Rη σ η q *ᵥ v)))) =
      π_quot q (bH.equivFun.symm (U.subtype (bU.equivFun.symm (P.mulVecLin v))))
    rw [h1, h2, h3, h4]
  let B : Bη σ η → Matrix ι (BN σ) ℂ := fun j => (L (Pi.single j 1) : Matrix ι (BN σ) ℂ)
  have hB_eq : ∀ (k : inertia N RN σ) (j : Bη σ η),
      ρ (k : G) * B j = ∑ j' : Bη σ η, Rη σ η (QuotientGroup.mk k) j' j • (B j' * Rext σ k) := by
    intro k j
    have hmv : Rη σ η (QuotientGroup.mk k) *ᵥ (Pi.single j (1 : ℂ)) =
        ∑ j' : Bη σ η, Rη σ η (QuotientGroup.mk k) j' j • Pi.single j' (1 : ℂ) := by
      ext j''
      simp [Matrix.mulVec_single, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    have hLkj := hL_inter (QuotientGroup.mk k) (Pi.single j 1)
    rw [hmv, map_sum] at hLkj
    simp_rw [map_smul] at hLkj
    have hval := congrArg Subtype.val hLkj
    have hLval : (π_quot (QuotientGroup.mk k) (L (Pi.single j 1))).val =
        ρ (k : G) * B j * Rext σ k⁻¹ := rfl
    have hRval : (∑ j' : Bη σ η, Rη σ η (QuotientGroup.mk k) j' j • L (Pi.single j' 1)).val =
        ∑ j' : Bη σ η, Rη σ η (QuotientGroup.mk k) j' j • B j' := by
      simp [B]
    rw [hLval, hRval] at hval
    calc ρ (k : G) * B j
        = (ρ (k : G) * B j * Rext σ k⁻¹) * Rext σ k := by
          rw [Matrix.mul_assoc, isMatRep_inv_mul (hext σ).1.1 k, Matrix.mul_one]
      _ = (∑ j' : Bη σ η, Rη σ η (QuotientGroup.mk k) j' j • B j') * Rext σ k := by
          rw [← hval]
      _ = ∑ j' : Bη σ η, Rη σ η (QuotientGroup.mk k) j' j • (B j' * Rext σ k) := by
          ext x i
          simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
            Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun i' _ => ?_
          ring
  let W_I : Matrix ι (BN σ × Bη σ η) ℂ := Matrix.of fun x ij => B ij.2 x ij.1
  have hWI_ne : W_I ≠ 0 := by
    have : Nonempty (Bη σ η) := (hRησ.2.1 η).1
    have j₀ : Bη σ η := Classical.arbitrary (Bη σ η)
    have hLj : L (Pi.single j₀ 1) ≠ 0 := by
      intro h0
      have := hL_inj (h0.trans (map_zero L).symm)
      have := congr_fun this j₀
      simp at this
    have hBj : B j₀ ≠ 0 := fun h0 => hLj (Subtype.ext h0)
    intro h0
    apply hBj
    ext x i
    exact congr_fun (congr_fun h0 x) (i, j₀)
  refine ⟨η, W_I, hWI_ne, fun k => ?_⟩
  ext x ⟨i, j⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type_right]
  have hLHS : ∑ j' : Bη σ η, ∑ i' : BN σ,
      W_I x (i', j') * littleKernelRep N RN Rext Rη σ η k (i', j') (i, j) =
      (∑ j' : Bη σ η, Rη σ η (QuotientGroup.mk k) j' j • (B j' * Rext σ k)) x i := by
    simp only [W_I, littleKernelRep, Matrix.of_apply, Matrix.kronecker, Matrix.kronecker_apply,
      inflation, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    ring
  have hRHS : ∑ y : ι, ρ (k : G) x y * W_I y (i, j) = (ρ (k : G) * B j) x i := by
    simp [W_I, Matrix.mul_apply]
  rw [hLHS, hRHS, hB_eq k j]

end GL2QFT.Supplement.Thm712Helpers

open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.Thm712Helpers in
theorem solution {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (T : ΛN → Set G)
    (hT : ∀ σ ∈ O, Subgroup.IsComplement (T σ) (inertia N RN σ : Set G) ∧ (1 : G) ∈ T σ)
    (Λη : ΛN → Type) [∀ σ, Fintype (Λη σ)] (Bη : ∀ σ, Λη σ → Type) [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ)) :
    let Φ : ∀ p : Σ σ : ΛN, Λη σ,
        G → Matrix (T p.1 × (BN p.1 × Bη p.1 p.2)) (T p.1 × (BN p.1 × Bη p.1 p.2)) ℂ :=
      fun p => indRep (inertia N RN p.1) (T p.1)
        (fun k => Matrix.kronecker (Rext p.1 k) (inflation N RN p.1 (Rη p.1 p.2) k))
    (∀ p : Σ σ : ΛN, Λη σ, p.1 ∈ O → IsUnitaryRep (Φ p) ∧ IsIrreducibleRep (Φ p)) ∧
    (∀ p p' : Σ σ : ΛN, Λη σ, p.1 ∈ O → p'.1 ∈ O → RepEquiv (Φ p) (Φ p') → p = p') ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : G → Matrix ι ι ℂ),
      IsMatRep ρ → IsIrreducibleRep ρ →
        ∃ p : Σ σ : ΛN, Λη σ, p.1 ∈ O ∧ RepEquiv (Φ p) ρ) := by
  intro Φ
  have hClause1 : ∀ p : Σ σ : ΛN, Λη σ, p.1 ∈ O → IsUnitaryRep (Φ p) ∧ IsIrreducibleRep (Φ p) := by
    rintro ⟨σ, η⟩ hσ
    have hU : IsUnitaryRep (Φ ⟨σ, η⟩) :=
      indRep_isUnitaryRep (inertia N RN σ) (T σ) (hT σ hσ).1
        (littleKernelRep_isUnitaryRep N RN Rext hext Rη (hRη σ hσ) η)
    refine ⟨hU, ?_⟩
    have : Nonempty (T σ) := ⟨⟨1, (hT σ hσ).2⟩⟩
    have : Nonempty (BN σ) := (hRN.2.1 σ).1
    have : Nonempty (Bη σ η) := ((hRη σ hσ).2.1 η).1
    refine isIrreducibleRep_of_end_eq_smul_one hU.1 fun M hM => ?_
    obtain ⟨hdiag, C, hMC, hCcomm⟩ :=
      intertwiner_same_sigma_structure N RN hRN Rext hext T Rη (hT σ hσ).1 (hT σ hσ).2
        (hRη σ hσ) hM
    obtain ⟨c, hc⟩ := schur_eq_smul_one ((hRη σ hσ).2.1 η) (fun q => (hCcomm q).symm)
    refine ⟨c, ?_⟩
    ext ⟨t', i', j'⟩ ⟨t, i, j⟩
    by_cases hst : t' = t
    · subst hst
      rw [hMC t' i' j' i j, hc, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        Matrix.one_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      simp only [Prod.mk.injEq, true_and]
      split_ifs with hi hj <;> simp_all
    · rw [hdiag t' t hst (i', j') (i, j), Matrix.smul_apply, Matrix.one_apply]
      simp [hst]
  refine ⟨hClause1, ?_, ?_⟩
  · rintro ⟨σ, η⟩ ⟨σ', η'⟩ hσ hσ' ⟨M, M', hMM', hM'M, hM⟩
    have hσeq : σ = σ' := by
      by_contra hne
      have hM0 := intertwiner_eq_zero_of_ne_sigma N RN hRN Rext hext O hO T Rη hσ hσ' hne
        (hT σ hσ).1 (hT σ' hσ').1 (hRη σ hσ) (hRη σ' hσ') (fun g => hM g (Set.mem_univ _))
      have : Nonempty (T σ') := ⟨⟨1, (hT σ' hσ').2⟩⟩
      have : Nonempty (BN σ') := (hRN.2.1 σ').1
      have : Nonempty (Bη σ' η') := ((hRη σ' hσ').2.1 η').1
      exact repEquiv_ne_zero_left hMM' hM0
    subst hσeq
    have hηeq : η = η' := by
      by_contra hne
      obtain ⟨hdiag, C, hMC, hC⟩ :=
        intertwiner_same_sigma_structure N RN hRN Rext hext T Rη (hT σ hσ).1 (hT σ hσ).2
          (hRη σ hσ) (fun g => hM g (Set.mem_univ _))
      have hC0 : C = 0 :=
        schur_zero_of_not_repEquiv ((hRη σ hσ).2.1 η) ((hRη σ hσ).2.1 η')
          ((hRη σ hσ).2.2.1 η η' hne) hC
      have hM0 : M = 0 := by
        ext ⟨t', i', j'⟩ ⟨t, i, j⟩
        by_cases hst : t' = t
        · subst hst
          rw [hMC t' i' j' i j, hC0]
          simp
        · exact hdiag t' t hst (i', j') (i, j)
      have : Nonempty (T σ) := ⟨⟨1, (hT σ hσ).2⟩⟩
      have : Nonempty (BN σ) := (hRN.2.1 σ).1
      have : Nonempty (Bη σ η') := ((hRη σ hσ).2.1 η').1
      exact repEquiv_ne_zero_left hMM' hM0
    subst hηeq
    rfl
  · intro ι _ _ ρ hρ_mat hρ_irr
    obtain ⟨⟨σ, hσ⟩, A₀, hA₀_ne, hA₀_inter⟩ :=
      exists_N_intertwiner N RN hRN O hO hρ_mat hρ_irr
    obtain ⟨η, W_I, hWI_ne, hWI_inter⟩ :=
      exists_little_intertwiner N RN hRN Rext hext Rη σ (hRη σ hσ) hρ_mat A₀ hA₀_ne hA₀_inter
    let W_G : Matrix ι (T σ × (BN σ × Bη σ η)) ℂ := Matrix.of fun x tij => (ρ (tij.1 : G) * W_I) x tij.2
    have hWG_ne : W_G ≠ 0 := by
      intro h0
      apply hWI_ne
      ext x ij
      have hent := congr_fun (congr_fun h0 x) (⟨1, (hT σ hσ).2⟩, ij)
      simpa [W_G, hρ_mat.1] using hent
    have hWG_inter : ∀ g : G, W_G * Φ ⟨σ, η⟩ g = ρ g * W_G := by
      intro g
      ext x ⟨t, ij⟩
      rw [Matrix.mul_apply, Matrix.mul_apply]
      rw [Fintype.sum_prod_type]
      obtain ⟨s₀, hs₀, hs₀_uniq⟩ := isComplement_existsUnique_left (hT σ hσ).1 g t
      rw [Finset.sum_eq_single s₀]
      · have hL : ∑ ij' : BN σ × Bη σ η,
            W_G x (s₀, ij') * Φ ⟨σ, η⟩ g (s₀, ij') (t, ij) =
            (ρ (s₀ : G) * (W_I * littleKernelRep N RN Rext Rη σ η ⟨_, hs₀⟩)) x ij := by
          simp only [W_G, Φ, indRep, Matrix.of_apply, dif_pos hs₀]
          simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ij' _ => ?_
          dsimp only [littleKernelRep]
          ring
        rw [hL, hWI_inter ⟨_, hs₀⟩, ← Matrix.mul_assoc, ← hρ_mat.2]
        have hmul : (s₀ : G) * ((s₀ : G)⁻¹ * g * (t : G)) = g * (t : G) := by group
        rw [hmul, hρ_mat.2, Matrix.mul_assoc]
        simp [W_G, Matrix.mul_apply]
      · intro s _ hs
        refine Finset.sum_eq_zero fun ij' _ => ?_
        have hns : ¬ ((s : G)⁻¹ * g * (t : G) ∈ inertia N RN σ) := fun hm => hs (hs₀_uniq s hm)
        simp [Φ, indRep, hns]
      · intro hs₀_mem; exact absurd (Finset.mem_univ s₀) hs₀_mem
    refine ⟨⟨σ, η⟩, hσ, ?_⟩
    by_contra hnot
    exact hWG_ne (schur_zero_of_not_repEquiv (hClause1 ⟨σ, η⟩ hσ).2 hρ_irr hnot hWG_inter)
