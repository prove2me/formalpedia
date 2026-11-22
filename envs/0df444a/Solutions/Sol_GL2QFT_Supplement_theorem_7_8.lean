-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_7_8
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:27:08.83501+00:00
-- url     : https://prove2.me/submissions/8d34e61d-8ffd-4630-9015-f9539482b116

import Definitions.Def_GL2QFT_Supplement_RepTheory

noncomputable section

open Classical
open scoped Matrix ComplexConjugate
open GL2QFT GL2QFT.Supplement

namespace GL2QFT.Supplement.Thm78Helpers

/-! ### Section 1: Basic matrix representation facts and Schur's lemma -/

private theorem isUnitaryRep_mul_conjTranspose {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g * (R g)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hR.2 g)

private theorem isUnitaryRep_conjTranspose_mul {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    (R g)ᴴ * R g = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hR.2 g)

private theorem isUnitaryRep_inv_eq_conjTranspose {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g⁻¹ = (R g)ᴴ := by
  have h1 : R g * R g⁻¹ = 1 := by
    rw [← hR.1.2, mul_inv_cancel, hR.1.1]
  have h2 : (R g)ᴴ * R g = 1 := isUnitaryRep_conjTranspose_mul hR g
  calc R g⁻¹ = 1 * R g⁻¹ := (Matrix.one_mul _).symm
    _ = ((R g)ᴴ * R g) * R g⁻¹ := by rw [h2]
    _ = (R g)ᴴ * (R g * R g⁻¹) := Matrix.mul_assoc _ _ _
    _ = (R g)ᴴ := by rw [h1, Matrix.mul_one]

private theorem isMatRep_mul_inv {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsMatRep R) (g : G) :
    R g * R g⁻¹ = 1 := by
  rw [← hR.2, mul_inv_cancel, hR.1]

private theorem isMatRep_inv_mul {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsMatRep R) (g : G) :
    R g⁻¹ * R g = 1 := by
  rw [← hR.2, inv_mul_cancel, hR.1]

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
    have hc : A.mulVecLin.comp e.symm.toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      change e (e.symm x) = x
      simp
    rw [hc, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← hA_eq, ← LinearMap.toMatrix'_comp]
    have hc : e.symm.toLinearMap.comp A.mulVecLin = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      change e.symm (e x) = x
      simp
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

/-! ### Section 2: Weyl-averaged inner product, Maschke's theorem, minimal subreps -/

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
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnni).mp h1 i (Finset.mem_univ i)
  have hre0 : (u i).re = 0 := by nlinarith
  have him0 : (u i).im = 0 := by nlinarith
  exact Complex.ext hre0 him0

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
        simpa only [Submodule.coe_sum, SetLike.val_smul] using congrArg Subtype.val hrepr
      rw [hs_eq]
      have hsum_zero : ∀ F : Finset (Fin k),
          repIP ρ (∑ i ∈ F, b.repr ⟨s, hs⟩ i • (b i : ι → ℂ)) v = 0 := by
        intro F
        induction F using Finset.induction_on with
        | empty => simp [repIP]
        | @insert i F hi ih =>
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
    have hk_eq : Module.finrank ℂ S = k := rfl
    omega
  have hsup : S ⊔ repOrtho ρ S = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le _) hsup_ge
  exact ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩

private theorem linearProj_invariant_eq {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {S : Submodule ℂ (ι → ℂ)}
    (hS : IsInvariantSubspace ρ S) (g : G) (v : ι → ℂ) :
    let hcompl := repOrtho_isCompl hρ S
    let π := S.projectionOnto (repOrtho ρ S) hcompl
    (π (ρ g *ᵥ v) : ι → ℂ) = ρ g *ᵥ (π v : ι → ℂ) := by
  intro hcompl π
  have hmem : v ∈ S ⊔ repOrtho ρ S := hcompl.codisjoint.eq_top ▸ Submodule.mem_top
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hmem
  have hπv : π (s + t) = ⟨s, hs⟩ := by
    rw [map_add]
    have h1 : π s = ⟨s, hs⟩ := Submodule.projectionOnto_apply_left hcompl ⟨s, hs⟩
    have h2 : π t = 0 := Submodule.projectionOnto_apply_right hcompl ⟨t, ht⟩
    rw [h1, h2, add_zero]
  have hgs : ρ g *ᵥ s ∈ S := hS g s hs
  have hgt : ρ g *ᵥ t ∈ repOrtho ρ S := repOrtho_invariant hρ hS g t ht
  have hπgv : π (ρ g *ᵥ (s + t)) = ⟨ρ g *ᵥ s, hgs⟩ := by
    rw [Matrix.mulVec_add, map_add]
    have h1 : π (ρ g *ᵥ s) = ⟨ρ g *ᵥ s, hgs⟩ :=
      Submodule.projectionOnto_apply_left hcompl ⟨ρ g *ᵥ s, hgs⟩
    have h2 : π (ρ g *ᵥ t) = 0 :=
      Submodule.projectionOnto_apply_right hcompl ⟨ρ g *ᵥ t, hgt⟩
    rw [h1, h2, add_zero]
  rw [hπgv, hπv]

private theorem exists_invariant_proj {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {S : Submodule ℂ (ι → ℂ)}
    (hS : IsInvariantSubspace ρ S) :
    ∃ P : Matrix ι ι ℂ, P * P = P ∧ (∀ g : G, P * ρ g = ρ g * P) ∧
      (∀ v : ι → ℂ, P *ᵥ v ∈ S) ∧ (∀ v ∈ S, P *ᵥ v = v) := by
  let hcompl := repOrtho_isCompl hρ S
  let π := S.projectionOnto (repOrtho ρ S) hcompl
  let P_lin : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) := S.subtype.comp π
  let P : Matrix ι ι ℂ := LinearMap.toMatrix' P_lin
  have hP_lin : P.mulVecLin = P_lin := LinearMap.toMatrix'.injective (LinearMap.toMatrix'_toLin' P)
  have hP_apply : ∀ v, P *ᵥ v = (π v : ι → ℂ) := fun v => by
    change P.mulVecLin v = P_lin v
    rw [hP_lin]
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
    intro v
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hP_apply, hP_apply]
    have h1 : π (π v : ι → ℂ) = π v := Submodule.projectionOnto_apply_left hcompl (π v)
    rw [h1, sub_self]
  · intro g
    rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
    intro v
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hP_apply, hP_apply, linearProj_invariant_eq hρ hS g v, sub_self]
  · intro v
    rw [hP_apply]
    exact (π v).2
  · intro v hv
    rw [hP_apply]
    have h1 : π v = ⟨v, hv⟩ := by simpa using Submodule.projectionOnto_apply_left hcompl ⟨v, hv⟩
    rw [h1]

private theorem exists_min_invariant_subrep {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hρ : IsMatRep ρ) {W : Submodule ℂ (ι → ℂ)}
    (hWne : W ≠ ⊥) (hWinv : IsInvariantSubspace ρ W) :
    ∃ (d : ℕ) (U : Submodule ℂ (ι → ℂ)) (hUinv : IsInvariantSubspace ρ U)
      (b : Module.Basis (Fin d) ℂ U),
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
  have hd_pos : 0 < d := by dsimp [d]; rw [← hUdim]; exact Module.finrank_pos
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
      have hLU : L_U x (b.equivFun.symm v) = b.equivFun.symm (ρ_U x *ᵥ v) := by
        have hthis := Matrix.toLin_apply b b (ρ_U x) (b.equivFun.symm v)
        rw [Matrix.toLin_toMatrix] at hthis
        have hrepr : (b.repr (b.equivFun.symm v) : Fin d → ℂ) = v := b.equivFun.apply_symm_apply v
        rw [hrepr, ← b.equivFun_symm_apply] at hthis
        exact hthis
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
      have h0v := congrArg b.equivFun this
      rw [b.equivFun.apply_symm_apply, map_zero] at h0v
      exact h0v
    · right
      have hle_d : d ≤ Module.finrank ℂ U'' := Nat.find_min' hex
        ⟨U'', hU''_le.trans hUW, hbot, hU''_inv, rfl⟩
      have hge_d : Module.finrank ℂ U'' ≤ d := by
        dsimp [d]
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
      have h0v : w = v := by
        simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] using
          congrArg b.equivFun hvw
      subst h0v
      exact hw
  exact ⟨d, U, hUinv, b, hUW, hUne, hρU_mat, hρU_irr⟩

/-! ### Section 3: Clifford theory primitives (`transport`, `InOrbit`, `inertia`, `IsSuccessor`) -/

private theorem transport_isMatRep {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : N → Matrix ι ι ℂ} (hR : IsMatRep R) (g : G) :
    IsMatRep (transport N R g) := by
  constructor
  · unfold transport
    have h1 : (⟨g⁻¹ * ((1 : N) : G) * g, conj_inv_mem N g 1⟩ : N) = 1 := by ext; simp
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

private theorem repEquiv_transport_iff {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (R₁ : N → Matrix ι₁ ι₁ ℂ) (R₂ : N → Matrix ι₂ ι₂ ℂ) (g : G) :
    RepEquiv (transport N R₁ g⁻¹) R₂ ↔ RepEquiv R₁ (transport N R₂ g) := by
  constructor
  · rintro ⟨A, B, hAB, hBA, h⟩
    refine ⟨A, B, hAB, hBA, fun n _ => ?_⟩
    let m : N := ⟨g⁻¹ * (n : G) * g, conj_inv_mem N g n⟩
    have hm := h m (Set.mem_univ _)
    have heq : transport N R₁ g⁻¹ m = R₁ n := by
      unfold transport
      congr 1; ext; simp [m, mul_assoc]
    rw [heq] at hm
    exact hm
  · rintro ⟨A, B, hAB, hBA, h⟩
    refine ⟨A, B, hAB, hBA, fun n _ => ?_⟩
    let m : N := ⟨g * (n : G) * g⁻¹, by simpa using (inferInstance : N.Normal).conj_mem n n.2 g⟩
    have hm := h m (Set.mem_univ _)
    have heq : transport N R₂ g m = R₂ n := by
      unfold transport
      congr 1; ext; simp [m, mul_assoc]
    rw [heq] at hm
    simpa [transport, m, mul_assoc] using hm

private theorem inOrbit_refl {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (l : ΛN) :
    InOrbit N RN l l := by
  refine ⟨1, ?_⟩
  have h1 : transport N (RN l) 1 = RN l := funext (transport_one N (RN l))
  rw [h1]
  exact repEquiv_refl (RN l)

private theorem orbitTransversal_eq {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) {O : Set ΛN} (hO : IsOrbitTransversal N RN O)
    {σ σ' : ΛN} (hσ : σ ∈ O) (hσ' : σ' ∈ O) (hin : InOrbit N RN σ σ') : σ = σ' := by
  obtain ⟨τ, _, huniq⟩ := hO σ
  have h1 : (⟨σ, hσ⟩ : O) = τ := huniq ⟨σ, hσ⟩ (inOrbit_refl N RN σ)
  have h2 : (⟨σ', hσ'⟩ : O) = τ := huniq ⟨σ', hσ'⟩ hin
  exact congrArg Subtype.val (h1.trans h2.symm)

private theorem mem_inertia_of_mem_normal {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (l : ΛN) (hR : IsMatRep (RN l))
    (n₀ : N) : (n₀ : G) ∈ inertia N RN l := by
  refine ⟨RN l n₀, RN l n₀⁻¹, isMatRep_mul_inv hR n₀, isMatRep_inv_mul hR n₀, fun n _ => ?_⟩
  unfold transport
  have heq : (⟨(n₀ : G)⁻¹ * (n : G) * (n₀ : G), conj_inv_mem N (n₀ : G) n⟩ : N) =
      n₀⁻¹ * n * n₀ := by ext; rfl
  rw [heq, hR.2, hR.2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, isMatRep_mul_inv hR n₀, Matrix.one_mul]

private theorem isSuccessor_intertwiner_zero {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (σ : ΛN) {Bη κ : Type} [Fintype Bη] [DecidableEq Bη] [Fintype κ] [DecidableEq κ]
    {R : inertia N RN σ → Matrix Bη Bη ℂ} (hR_unit : IsUnitaryRep R) (hR_irr : IsIrreducibleRep R)
    (hsucc : IsSuccessor N RN σ R)
    {Q : N → Matrix κ κ ℂ} (hQ_irr : IsIrreducibleRep Q) (hne : ¬ RepEquiv Q (RN σ))
    {X : Matrix Bη κ ℂ}
    (hX : ∀ n : N, X * Q n = R ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ * X) :
    X = 0 := by
  obtain ⟨S₀, hS₀_ne, hS₀_inter⟩ := hsucc
  have hS₀_N : ∀ n : N,
      S₀ * RN σ n = R ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ * S₀ := by
    intro n
    let nK : inertia N RN σ := ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩
    let x : N.subgroupOf (inertia N RN σ) := ⟨nK, n.2⟩
    exact hS₀_inter x
  let U : Submodule ℂ (Bη → ℂ) :=
    Submodule.span ℂ {v | ∃ k : inertia N RN σ, ∃ u : BN σ → ℂ, (R k * S₀) *ᵥ u = v}
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hS₀_ne
    rw [← mulVecLin_eq_zero_iff]
    intro u
    have huU : S₀ *ᵥ u ∈ U := by
      refine Submodule.subset_span ⟨1, u, ?_⟩
      rw [hR_unit.1.1, Matrix.one_mul]
    rw [hbot] at huU
    exact huU
  have hUinv : IsInvariantSubspace R U := by
    intro k₀ v hv
    refine Submodule.span_induction (p := fun v _ => R k₀ *ᵥ v ∈ U) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, u, rfl⟩
      refine Submodule.subset_span ⟨k₀ * k, u, ?_⟩
      rw [hR_unit.1.2, Matrix.mul_assoc, Matrix.mulVec_mulVec]
    · simp [Matrix.mulVec_zero]
    · intro a b _ _ ha hb; rw [Matrix.mulVec_add]; exact U.add_mem ha hb
    · intro c a _ ha; rw [Matrix.mulVec_smul]; exact U.smul_mem c ha
  have hUtop : U = ⊤ := (hR_irr.2 U hUinv).resolve_left hUne
  have hkill : ∀ k : inertia N RN σ, (R k * S₀)ᴴ * X = 0 := by
    intro k
    obtain ⟨C, D, hCD, hDC, hinter⟩ := k.2
    have hinter' : ∀ n : N,
        RN σ ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * D = D * RN σ n := by
      intro n
      calc RN σ ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * D
          = (D * C) * RN σ ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * D := by
              rw [hDC, Matrix.one_mul]
        _ = D * (C * transport N (RN σ) (k : G) n) * D := by
              simp only [transport, Matrix.mul_assoc]
        _ = D * (RN σ n * C) * D := by rw [hinter n (Set.mem_univ _)]
        _ = D * RN σ n * (C * D) := by simp only [Matrix.mul_assoc]
        _ = D * RN σ n := by rw [hCD, Matrix.mul_one]
    let M : Matrix Bη (BN σ) ℂ := R k * S₀ * D
    have hM_N : ∀ n : N,
        M * RN σ n = R ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ * M := by
      intro n
      let nK : inertia N RN σ := ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩
      let m : N := ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩
      let mK : inertia N RN σ := ⟨m.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 m⟩
      have hkm : k * mK = nK * k := by
        ext; simp [m, mK, nK, mul_assoc]
      calc M * RN σ n
          = R k * S₀ * (D * RN σ n) := by simp only [M, Matrix.mul_assoc]
        _ = R k * S₀ * (RN σ m * D) := by rw [hinter' n]
        _ = R k * (S₀ * RN σ m) * D := by simp only [Matrix.mul_assoc]
        _ = R k * (R mK * S₀) * D := by rw [hS₀_N m]
        _ = (R k * R mK) * S₀ * D := by simp only [Matrix.mul_assoc]
        _ = R (k * mK) * S₀ * D := by rw [← hR_unit.1.2]
        _ = R (nK * k) * S₀ * D := by rw [hkm]
        _ = (R nK * R k) * S₀ * D := by rw [hR_unit.1.2]
        _ = R nK * M := by simp only [M, Matrix.mul_assoc]
    have hM_conj : ∀ n : N,
        Mᴴ * R ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ = RN σ n * Mᴴ := by
      intro n
      let nK : inertia N RN σ := ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩
      have hnK_inv : (nK⁻¹ : inertia N RN σ) =
          ⟨(n⁻¹ : N).1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⁻¹⟩ := by
        ext; rfl
      have h1 := congrArg Matrix.conjTranspose (hM_N n⁻¹)
      simp only [Matrix.conjTranspose_mul] at h1
      rw [← hnK_inv] at h1
      have hRN_inv : (RN σ n⁻¹)ᴴ = RN σ n := by
        rw [← isUnitaryRep_inv_eq_conjTranspose (hRN.1 σ) n⁻¹, inv_inv]
      have hR_inv : (R nK⁻¹)ᴴ = R nK := by
        rw [← isUnitaryRep_inv_eq_conjTranspose hR_unit nK⁻¹, inv_inv]
      rw [hRN_inv, hR_inv] at h1
      exact h1.symm
    let Y : Matrix (BN σ) κ ℂ := Mᴴ * X
    have hY : ∀ n : N, Y * Q n = RN σ n * Y := fun n => by
      calc Y * Q n = Mᴴ * (X * Q n) := Matrix.mul_assoc _ _ _
        _ = Mᴴ * (R ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ * X) := by rw [hX n]
        _ = (Mᴴ * R ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩) * X :=
            (Matrix.mul_assoc _ _ _).symm
        _ = (RN σ n * Mᴴ) * X := by rw [hM_conj n]
        _ = RN σ n * Y := Matrix.mul_assoc _ _ _
    have hY0 : Y = 0 := schur_zero_of_not_repEquiv hQ_irr (hRN.2.1 σ) hne hY
    have hC_D : Cᴴ * Dᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hDC, Matrix.conjTranspose_one]
    calc (R k * S₀)ᴴ * X
        = (Cᴴ * Dᴴ) * (R k * S₀)ᴴ * X := by rw [hC_D, Matrix.one_mul]
      _ = Cᴴ * (Dᴴ * (R k * S₀)ᴴ) * X := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * (Mᴴ * X) := by simp only [M, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Cᴴ * Y := rfl
      _ = 0 := by rw [hY0, Matrix.mul_zero]
  rw [← mulVecLin_eq_zero_iff]
  intro w
  let z : Bη → ℂ := X *ᵥ w
  have hz_perp : ∀ v ∈ U, ∑ i : Bη, star (v i) * z i = 0 := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∑ i : Bη, star (v i) * z i = 0) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, u, rfl⟩
      have hvec : (R k * S₀)ᴴ *ᵥ z = 0 := by
        simp only [z, Matrix.mulVec_mulVec, hkill k, Matrix.zero_mulVec]
      have hdot : ∑ i : Bη, star (((R k * S₀) *ᵥ u) i) * z i =
          ∑ j : BN σ, star (u j) * (((R k * S₀)ᴴ *ᵥ z) j) := by
        simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul',
          Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hdot, hvec]
      simp
    · simp
    · intro a b _ _ ha hb
      simp only [Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib, ha, hb, add_zero]
    · intro c a _ ha
      simp only [Pi.smul_apply, smul_eq_mul, star_mul']
      calc ∑ i : Bη, star c * star (a i) * z i
          = star c * ∑ i : Bη, star (a i) * z i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [ha, mul_zero]
  have hzU : z ∈ U := hUtop.symm ▸ Submodule.mem_top
  have hzz := hz_perp z hzU
  have hre : (∑ i : Bη, star (z i) * z i).re = 0 := by rw [hzz]; simp
  have hsum : ∑ i : Bη, ((z i).re * (z i).re + (z i).im * (z i).im) = 0 := by
    simpa [Complex.star_def, Complex.mul_re] using hre
  have hnn : ∀ i ∈ (Finset.univ : Finset Bη),
      0 ≤ (z i).re * (z i).re + (z i).im * (z i).im := fun i _ =>
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  ext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
  have hre0 : (z i).re = 0 := by nlinarith
  have him0 : (z i).im = 0 := by nlinarith
  exact Complex.ext hre0 him0

/-! ### Section 4: `indRep` unitarity and block-intertwiner rigidity -/

private theorem complement_mul_mem_iff {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    (hT : Subgroup.IsComplement T (K : Set G)) (g : G) (s t : T) :
    ((s : G)⁻¹ * g * (t : G)) ∈ K ↔
      s = ((Equiv.ofBijective (fun x : T × K => (x.1 : G) * (x.2 : G)) hT).symm (g * (t : G))).1 := by
  let e : T × K ≃ G := Equiv.ofBijective (fun x : T × K => (x.1 : G) * (x.2 : G)) hT
  change ((s : G)⁻¹ * g * (t : G)) ∈ K ↔ s = (e.symm (g * (t : G))).1
  have hgt : g * (t : G) = ((e.symm (g * (t : G))).1 : G) * ((e.symm (g * (t : G))).2 : G) :=
    (e.apply_symm_apply (g * (t : G))).symm
  constructor
  · intro hm
    have heq : e (s, ⟨(s : G)⁻¹ * g * (t : G), hm⟩) = e (e.symm (g * (t : G))) := by
      change (s : G) * ((s : G)⁻¹ * g * (t : G)) = (e (e.symm (g * (t : G))) : G)
      rw [← mul_assoc (s : G), ← mul_assoc (s : G), mul_inv_cancel, one_mul, e.apply_symm_apply]
    exact congrArg Prod.fst (e.injective heq)
  · intro hs
    rw [hs, mul_assoc]
    nth_rw 2 [hgt]
    rw [← mul_assoc, inv_mul_cancel, one_mul]
    exact (e.symm (g * (t : G))).2.2

private theorem indRep_isUnitaryRep {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    [Fintype T] [DecidableEq T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hT : Subgroup.IsComplement T (K : Set G))
    {R : K → Matrix ι ι ℂ} (hR : IsUnitaryRep R) :
    IsUnitaryRep (indRep K T R) := by
  let e : T × K ≃ G := Equiv.ofBijective (fun x : T × K => (x.1 : G) * (x.2 : G)) hT
  have hmat : IsMatRep (indRep K T R) := by
    constructor
    · ext ⟨s, j⟩ ⟨t, i⟩
      simp only [indRep, Matrix.of_apply, Matrix.one_apply]
      have h1t : (e.symm ((1 : G) * (t : G))) = (t, 1) := by
        apply e.injective
        change ((e (e.symm ((1 : G) * (t : G)))) : G) = (t : G) * ((1 : K) : G)
        rw [e.apply_symm_apply]
        simp
      by_cases hst : s = t
      · subst hst
        have hm : ((s : G)⁻¹ * 1 * (s : G)) ∈ K := by simp
        rw [dif_pos hm]
        have h1 : (⟨(s : G)⁻¹ * 1 * (s : G), hm⟩ : K) = 1 := by ext; simp
        rw [h1, hR.1.1, Matrix.one_apply]
        simp
      · have hnot : ((s : G)⁻¹ * 1 * (t : G)) ∉ K := by
          have hiff := complement_mul_mem_iff K T hT 1 s t
          change ((s : G)⁻¹ * 1 * (t : G)) ∈ K ↔ s = (e.symm ((1 : G) * (t : G))).1 at hiff
          rw [hiff, h1t]
          exact hst
        rw [dif_neg hnot]
        simp [hst]
    · intro g₁ g₂
      ext ⟨s, j⟩ ⟨t, i⟩
      simp only [Matrix.mul_apply, indRep, Matrix.of_apply]
      let sk₂ := e.symm (g₂ * (t : G))
      let r₀ := sk₂.1
      let k₂ := sk₂.2
      have hg₂t : g₂ * (t : G) = (r₀ : G) * (k₂ : G) :=
        (e.apply_symm_apply (g₂ * (t : G))).symm
      have hm₂ : ((r₀ : G)⁻¹ * g₂ * (t : G)) ∈ K := by
        rw [mul_assoc, hg₂t, ← mul_assoc, inv_mul_cancel, one_mul]
        exact k₂.2
      have hk₂ : (⟨(r₀ : G)⁻¹ * g₂ * (t : G), hm₂⟩ : K) = k₂ := by
        ext; simp [mul_assoc, hg₂t]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single r₀]
      · simp only [dif_pos hm₂, hk₂]
        have hm_iff : ((s : G)⁻¹ * g₁ * (r₀ : G)) ∈ K ↔ ((s : G)⁻¹ * (g₁ * g₂) * (t : G)) ∈ K := by
          have heq : (s : G)⁻¹ * (g₁ * g₂) * (t : G) = ((s : G)⁻¹ * g₁ * (r₀ : G)) * (k₂ : G) := by
            calc (s : G)⁻¹ * (g₁ * g₂) * (t : G)
                = (s : G)⁻¹ * g₁ * (g₂ * (t : G)) := by simp only [mul_assoc]
              _ = (s : G)⁻¹ * g₁ * ((r₀ : G) * (k₂ : G)) := by rw [hg₂t]
              _ = ((s : G)⁻¹ * g₁ * (r₀ : G)) * (k₂ : G) := by simp only [mul_assoc]
          rw [heq]
          exact ⟨fun h => K.mul_mem h k₂.2, fun h => by
            simpa [mul_assoc] using K.mul_mem h (K.inv_mem k₂.2)⟩
        by_cases hm₁ : ((s : G)⁻¹ * g₁ * (r₀ : G)) ∈ K
        · have hm₁₂ := hm_iff.mp hm₁
          simp only [dif_pos hm₁, dif_pos hm₁₂]
          have hmulK : (⟨(s : G)⁻¹ * g₁ * (r₀ : G), hm₁⟩ : K) * k₂ =
              ⟨(s : G)⁻¹ * (g₁ * g₂) * (t : G), hm₁₂⟩ := by
            ext
            calc ((s : G)⁻¹ * g₁ * (r₀ : G)) * (k₂ : G)
                = (s : G)⁻¹ * g₁ * ((r₀ : G) * (k₂ : G)) := by simp only [mul_assoc]
              _ = (s : G)⁻¹ * g₁ * (g₂ * (t : G)) := by rw [← hg₂t]
              _ = (s : G)⁻¹ * (g₁ * g₂) * (t : G) := by simp only [mul_assoc]
          rw [← hmulK, hR.1.2, Matrix.mul_apply]
        · have hm₁₂ : ((s : G)⁻¹ * (g₁ * g₂) * (t : G)) ∉ K := mt hm_iff.mpr hm₁
          simp only [dif_neg hm₁, dif_neg hm₁₂, zero_mul, Finset.sum_const_zero]
      · intro r _ hr
        have hnot : ((r : G)⁻¹ * g₂ * (t : G)) ∉ K := by
          have hiff := complement_mul_mem_iff K T hT g₂ r t
          change ((r : G)⁻¹ * g₂ * (t : G)) ∈ K ↔ r = r₀ at hiff
          rw [hiff]
          exact hr
        simp [dif_neg hnot]
      · intro hr₀; exact False.elim (hr₀ (Finset.mem_univ _))
  refine ⟨hmat, fun g => Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  have hconj : (indRep K T R g)ᴴ = indRep K T R g⁻¹ := by
    ext ⟨s, j⟩ ⟨t, i⟩
    simp only [Matrix.conjTranspose_apply, indRep, Matrix.of_apply]
    have hm_iff : ((t : G)⁻¹ * g * (s : G)) ∈ K ↔ ((s : G)⁻¹ * g⁻¹ * (t : G)) ∈ K := by
      have heq : (s : G)⁻¹ * g⁻¹ * (t : G) = ((t : G)⁻¹ * g * (s : G))⁻¹ := by
        simp [mul_assoc]
      rw [heq]
      exact (K.inv_mem_iff).symm
    by_cases hm : ((t : G)⁻¹ * g * (s : G)) ∈ K
    · have hm' := hm_iff.mp hm
      simp only [dif_pos hm, dif_pos hm']
      have hinvK : (⟨(t : G)⁻¹ * g * (s : G), hm⟩ : K)⁻¹ = ⟨(s : G)⁻¹ * g⁻¹ * (t : G), hm'⟩ := by
        ext; simp [mul_assoc]
      rw [← hinvK, show star (R ⟨(t : G)⁻¹ * g * (s : G), hm⟩ i j) =
          (R ⟨(t : G)⁻¹ * g * (s : G), hm⟩)ᴴ j i from rfl,
        ← isUnitaryRep_inv_eq_conjTranspose hR]
    · have hm' : ((s : G)⁻¹ * g⁻¹ * (t : G)) ∉ K := mt hm_iff.mpr hm
      simp only [dif_neg hm, dif_neg hm', star_zero]
  rw [Matrix.star_eq_conjTranspose, hconj, ← hmat.2, mul_inv_cancel, hmat.1]

private theorem indRep_apply_col_one {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    [Fintype T] [DecidableEq T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hT : Subgroup.IsComplement T (K : Set G)) (h1 : (1 : G) ∈ T)
    (R : K → Matrix ι ι ℂ) (hR : IsMatRep R) (t s : T) (l j : ι) :
    indRep K T R (t : G) (s, l) (⟨1, h1⟩, j) =
      if s = t then (if l = j then 1 else 0) else 0 := by
  let e : T × K ≃ G := Equiv.ofBijective (fun x : T × K => (x.1 : G) * (x.2 : G)) hT
  simp only [indRep, Matrix.of_apply]
  have h1t : e.symm ((t : G) * ((⟨1, h1⟩ : T) : G)) = (t, 1) := by
    apply e.injective
    change e (e.symm ((t : G) * ((⟨1, h1⟩ : T) : G))) = (t : G) * ((1 : K) : G)
    rw [e.apply_symm_apply]
    simp
  by_cases hst : s = t
  · subst hst
    have hm : ((s : G)⁻¹ * (s : G) * ((⟨1, h1⟩ : T) : G)) ∈ K := by simp
    rw [dif_pos hm]
    have hK1 : (⟨(s : G)⁻¹ * (s : G) * ((⟨1, h1⟩ : T) : G), hm⟩ : K) = 1 := by ext; simp
    rw [hK1, hR.1, Matrix.one_apply]
    simp
  · have hnot : ((s : G)⁻¹ * (t : G) * ((⟨1, h1⟩ : T) : G)) ∉ K := by
      have hiff := complement_mul_mem_iff K T hT (t : G) s ⟨1, h1⟩
      change ((s : G)⁻¹ * (t : G) * ((⟨1, h1⟩ : T) : G)) ∈ K ↔
        s = (e.symm ((t : G) * ((⟨1, h1⟩ : T) : G))).1 at hiff
      rw [hiff, h1t]
      exact hst
    rw [dif_neg hnot, if_neg hst]

private theorem indRep_apply_sub_col_one {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    [Fintype T] [DecidableEq T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hT : Subgroup.IsComplement T (K : Set G)) (h1 : (1 : G) ∈ T)
    (R : K → Matrix ι ι ℂ) (k : K) (s : T) (l j : ι) :
    indRep K T R (k : G) (s, l) (⟨1, h1⟩, j) =
      if s = ⟨1, h1⟩ then R k l j else 0 := by
  let e : T × K ≃ G := Equiv.ofBijective (fun x : T × K => (x.1 : G) * (x.2 : G)) hT
  simp only [indRep, Matrix.of_apply]
  have h1k : e.symm ((k : G) * ((⟨1, h1⟩ : T) : G)) = (⟨1, h1⟩, k) := by
    apply e.injective
    change e (e.symm ((k : G) * ((⟨1, h1⟩ : T) : G))) = ((⟨1, h1⟩ : T) : G) * (k : G)
    rw [e.apply_symm_apply]
    simp
  by_cases hs1 : s = ⟨1, h1⟩
  · subst hs1
    have hm : (((⟨1, h1⟩ : T) : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G)) ∈ K := by
      simp [k.2]
    rw [dif_pos hm]
    have hk : (⟨((⟨1, h1⟩ : T) : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G), hm⟩ : K) = k := by
      ext; simp
    rw [hk, if_pos rfl]
  · have hnot : ((s : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G)) ∉ K := by
      have hiff := complement_mul_mem_iff K T hT (k : G) s ⟨1, h1⟩
      change ((s : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G)) ∈ K ↔
        s = (e.symm ((k : G) * ((⟨1, h1⟩ : T) : G))).1 at hiff
      rw [hiff, h1k]
      exact hs1
    rw [dif_neg hnot, if_neg hs1]

private theorem indRep_apply_sub_row_one {G : Type} [Group G] (K : Subgroup G) (T : Set G)
    [Fintype T] [DecidableEq T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hT : Subgroup.IsComplement T (K : Set G)) (h1 : (1 : G) ∈ T)
    (R : K → Matrix ι ι ℂ) (k : K) (s : T) (j' l : ι) :
    indRep K T R (k : G) (⟨1, h1⟩, j') (s, l) =
      if s = ⟨1, h1⟩ then R k j' l else 0 := by
  let e : T × K ≃ G := Equiv.ofBijective (fun x : T × K => (x.1 : G) * (x.2 : G)) hT
  simp only [indRep, Matrix.of_apply]
  by_cases hs1 : s = ⟨1, h1⟩
  · subst hs1
    have hm : (((⟨1, h1⟩ : T) : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G)) ∈ K := by
      simp [k.2]
    rw [dif_pos hm]
    have hk : (⟨((⟨1, h1⟩ : T) : G)⁻¹ * (k : G) * ((⟨1, h1⟩ : T) : G), hm⟩ : K) = k := by
      ext; simp
    rw [hk, if_pos rfl]
  · have hnot : (((⟨1, h1⟩ : T) : G)⁻¹ * (k : G) * (s : G)) ∉ K := by
      intro hm
      have hmem : ((k : G) * (s : G)) ∈ K := by simpa using hm
      have hsK : (s : G) ∈ K := (K.mul_mem_cancel_left k.2).mp hmem
      have heq : e (s, 1) = e (⟨1, h1⟩, ⟨(s : G), hsK⟩) := by
        change (s : G) * ((1 : K) : G) = ((⟨1, h1⟩ : T) : G) * (s : G)
        simp
      exact hs1 (congrArg Prod.fst (e.injective heq))
    rw [dif_neg hnot, if_neg hs1]

private theorem indRep_apply_normal_row {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (K : Subgroup G) (hNK : ∀ n : N, (n : G) ∈ K) (T : Set G)
    [Fintype T] [DecidableEq T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hT : Subgroup.IsComplement T (K : Set G))
    (R : K → Matrix ι ι ℂ) (n : N) (t s : T) (j' l : ι) :
    indRep K T R (n : G) (t, j') (s, l) =
      if s = t then R ⟨(t : G)⁻¹ * (n : G) * (t : G), hNK ⟨_, conj_inv_mem N (t : G) n⟩⟩ j' l
      else 0 := by
  let e : T × K ≃ G := Equiv.ofBijective (fun x : T × K => (x.1 : G) * (x.2 : G)) hT
  simp only [indRep, Matrix.of_apply]
  by_cases hst : s = t
  · subst hst
    have hm : ((s : G)⁻¹ * (n : G) * (s : G)) ∈ K := hNK ⟨_, conj_inv_mem N (s : G) n⟩
    rw [dif_pos hm, if_pos rfl]
  · have hnot : ((t : G)⁻¹ * (n : G) * (s : G)) ∉ K := by
      intro hm
      let m : N := ⟨(t : G)⁻¹ * (n : G) * (t : G), conj_inv_mem N (t : G) n⟩
      have hmK : (m : G) ∈ K := hNK m
      have hprod : ((t : G)⁻¹ * (s : G)) ∈ K := by
        have heq : (t : G)⁻¹ * (s : G) = (m : G)⁻¹ * ((t : G)⁻¹ * (n : G) * (s : G)) := by
          simp [m, mul_assoc]
        rw [heq]
        exact K.mul_mem (K.inv_mem hmK) hm
      have heq : e (s, 1) = e (t, ⟨(t : G)⁻¹ * (s : G), hprod⟩) := by
        change (s : G) * ((1 : K) : G) = (t : G) * ((t : G)⁻¹ * (s : G))
        simp
      exact hst (congrArg Prod.fst (e.injective heq))
    rw [dif_neg hnot, if_neg hst]

private def indBlock {G : Type} (T₁ T₂ : Set G) {ι₁ ι₂ : Type}
    (A : Matrix (T₂ × ι₂) (T₁ × ι₁) ℂ) (t₂ : T₂) (t₁ : T₁) : Matrix ι₂ ι₁ ℂ :=
  Matrix.of fun j₂ j₁ => A (t₂, j₂) (t₁, j₁)

private theorem indBlock_col_one_vanish {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (T : ΛN → Set G)
    (hT : ∀ σ ∈ O, Subgroup.IsComplement (T σ) (inertia N RN σ : Set G) ∧ (1 : G) ∈ T σ)
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, inertia N RN σ → Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ))
    {σ σ' : ΛN} (hσ : σ ∈ O) (hσ' : σ' ∈ O)
    {η : Λη σ} {η' : Λη σ'}
    (hsucc : IsSuccessor N RN σ (Rη σ η)) (hsucc' : IsSuccessor N RN σ' (Rη σ' η'))
    {A : Matrix (T σ' × Bη σ' η') (T σ × Bη σ η) ℂ}
    (hA : ∀ g : G,
      A * indRep (inertia N RN σ) (T σ) (Rη σ η) g =
        indRep (inertia N RN σ') (T σ') (Rη σ' η') g * A)
    (t' : T σ') (hne : σ ≠ σ' ∨ (t' : G) ≠ 1) :
    indBlock (T σ) (T σ') A t' ⟨1, (hT σ hσ).2⟩ = 0 := by
  let K := inertia N RN σ
  let K' := inertia N RN σ'
  let e₁ : T σ := ⟨1, (hT σ hσ).2⟩
  let A₀ : Matrix (Bη σ' η') (Bη σ η) ℂ := indBlock (T σ) (T σ') A t' e₁
  have hA₀_N : ∀ n : N,
      A₀ * Rη σ η ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ =
        Rη σ' η' ⟨(t' : G)⁻¹ * (n : G) * (t' : G),
          mem_inertia_of_mem_normal N RN σ' (hRN.1 σ').1 ⟨_, conj_inv_mem N (t' : G) n⟩⟩ * A₀ := by
    intro n
    ext j' j
    have heval := congr_fun (congr_fun (hA (n : G)) (t', j')) (e₁, j)
    simp only [Matrix.mul_apply] at heval
    have hLHS :
        ∑ x : T σ × Bη σ η,
          A (t', j') x * indRep K (T σ) (Rη σ η) (n : G) x (e₁, j) =
        (A₀ * Rη σ η ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩) j' j := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single e₁]
      · simp only [Matrix.mul_apply, A₀, indBlock, Matrix.of_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [indRep_apply_sub_col_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η)
          ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ e₁ l j, if_pos rfl]
      · intro s _ hs
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [indRep_apply_sub_col_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η)
          ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ s l j, if_neg hs, mul_zero]
      · intro he; exact False.elim (he (Finset.mem_univ _))
    have hRHS :
        ∑ x : T σ' × Bη σ' η',
          indRep K' (T σ') (Rη σ' η') (n : G) (t', j') x * A x (e₁, j) =
        (Rη σ' η' ⟨(t' : G)⁻¹ * (n : G) * (t' : G),
          mem_inertia_of_mem_normal N RN σ' (hRN.1 σ').1 ⟨_, conj_inv_mem N (t' : G) n⟩⟩ * A₀)
            j' j := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single t']
      · simp only [Matrix.mul_apply, A₀, indBlock, Matrix.of_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [indRep_apply_normal_row N K' (mem_inertia_of_mem_normal N RN σ' (hRN.1 σ').1)
          (T σ') (hT σ' hσ').1 (Rη σ' η') n t' t' j' l, if_pos rfl]
      · intro s _ hs
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [indRep_apply_normal_row N K' (mem_inertia_of_mem_normal N RN σ' (hRN.1 σ').1)
          (T σ') (hT σ' hσ').1 (Rη σ' η') n t' s j' l, if_neg hs, zero_mul]
      · intro ht'; exact False.elim (ht' (Finset.mem_univ _))
    rw [hLHS, hRHS] at heval
    exact heval
  have hnot_equiv : ¬ RepEquiv (transport N (RN σ) (t' : G)⁻¹) (RN σ') := by
    intro heq
    have heq' : RepEquiv (RN σ) (transport N (RN σ') (t' : G)) :=
      (repEquiv_transport_iff N (RN σ) (RN σ') (t' : G)).mp (by simpa using heq)
    have hσ_eq : σ = σ' := orbitTransversal_eq N RN hO hσ hσ' ⟨(t' : G), heq'⟩
    rcases hne with hσne | htne
    · exact hσne hσ_eq
    · subst hσ_eq
      have ht_mem : (t' : G) ∈ inertia N RN σ := (inertia N RN σ).inv_mem_iff.mp heq
      let e : T σ × inertia N RN σ ≃ G :=
        Equiv.ofBijective (fun x : T σ × inertia N RN σ => (x.1 : G) * (x.2 : G)) (hT σ hσ).1
      have heeq : e (t', 1) = e (⟨1, (hT σ hσ).2⟩, ⟨(t' : G), ht_mem⟩) := by
        change (t' : G) * ((1 : inertia N RN σ) : G) = ((⟨1, (hT σ hσ).2⟩ : T σ) : G) * (t' : G)
        simp
      have ht1 : t' = ⟨1, (hT σ hσ).2⟩ := congrArg Prod.fst (e.injective heeq)
      exact htne (congrArg Subtype.val ht1)
  obtain ⟨S₀, hS₀_ne, hS₀_inter⟩ := hsucc
  have hS₀_N : ∀ n : N,
      S₀ * RN σ n = Rη σ η ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ * S₀ := by
    intro n
    exact hS₀_inter ⟨⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩, n.2⟩
  let U : Submodule ℂ (Bη σ η → ℂ) :=
    Submodule.span ℂ {v | ∃ k : K, ∃ u : BN σ → ℂ, (Rη σ η k * S₀) *ᵥ u = v}
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hS₀_ne
    rw [← mulVecLin_eq_zero_iff]
    intro u
    have huU : S₀ *ᵥ u ∈ U := by
      refine Submodule.subset_span ⟨1, u, ?_⟩
      rw [(hRη σ hσ).1 η |>.1.1, Matrix.one_mul]
    rw [hbot] at huU
    exact huU
  have hUinv : IsInvariantSubspace (Rη σ η) U := by
    intro k₀ v hv
    refine Submodule.span_induction (p := fun v _ => Rη σ η k₀ *ᵥ v ∈ U) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, u, rfl⟩
      refine Submodule.subset_span ⟨k₀ * k, u, ?_⟩
      rw [(hRη σ hσ).1 η |>.1.2, Matrix.mul_assoc, Matrix.mulVec_mulVec]
    · simp [Matrix.mulVec_zero]
    · intro a b _ _ ha hb; rw [Matrix.mulVec_add]; exact U.add_mem ha hb
    · intro c a _ ha; rw [Matrix.mulVec_smul]; exact U.smul_mem c ha
  have hUtop : U = ⊤ := ((hRη σ hσ).2.1 η |>.2 U hUinv).resolve_left hUne
  have hkill : ∀ k : K, A₀ * (Rη σ η k * S₀) = 0 := by
    intro k
    obtain ⟨C, D, hCD, hDC, hinter⟩ := k.2
    have hinter' : ∀ n : N,
        RN σ ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * D = D * RN σ n := by
      intro n
      calc RN σ ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * D
          = (D * C) * RN σ ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * D := by
              rw [hDC, Matrix.one_mul]
        _ = D * (C * transport N (RN σ) (k : G) n) * D := by
              simp only [transport, Matrix.mul_assoc]
        _ = D * (RN σ n * C) * D := by rw [hinter n (Set.mem_univ _)]
        _ = D * RN σ n * (C * D) := by simp only [Matrix.mul_assoc]
        _ = D * RN σ n := by rw [hCD, Matrix.mul_one]
    let M : Matrix (Bη σ η) (BN σ) ℂ := Rη σ η k * S₀ * D
    have hM_N : ∀ n : N,
        M * RN σ n = Rη σ η ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ * M := by
      intro n
      let nK : K := ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩
      let m : N := ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩
      let mK : K := ⟨m.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 m⟩
      have hkm : k * mK = nK * k := by ext; simp [m, mK, nK, mul_assoc]
      calc M * RN σ n
          = Rη σ η k * S₀ * (D * RN σ n) := by simp only [M, Matrix.mul_assoc]
        _ = Rη σ η k * S₀ * (RN σ m * D) := by rw [hinter' n]
        _ = Rη σ η k * (S₀ * RN σ m) * D := by simp only [Matrix.mul_assoc]
        _ = Rη σ η k * (Rη σ η mK * S₀) * D := by rw [hS₀_N m]
        _ = (Rη σ η k * Rη σ η mK) * S₀ * D := by simp only [Matrix.mul_assoc]
        _ = Rη σ η (k * mK) * S₀ * D := by rw [← (hRη σ hσ).1 η |>.1.2]
        _ = Rη σ η (nK * k) * S₀ * D := by rw [hkm]
        _ = (Rη σ η nK * Rη σ η k) * S₀ * D := by rw [(hRη σ hσ).1 η |>.1.2]
        _ = Rη σ η nK * M := by simp only [M, Matrix.mul_assoc]
    let X : Matrix (Bη σ' η') (BN σ) ℂ := A₀ * M
    have hX : ∀ m : N,
        X * transport N (RN σ) (t' : G)⁻¹ m =
          Rη σ' η' ⟨m.1, mem_inertia_of_mem_normal N RN σ' (hRN.1 σ').1 m⟩ * X := by
      intro m
      let n : N := ⟨(t' : G) * (m : G) * (t' : G)⁻¹,
        by simpa using (inferInstance : N.Normal).conj_mem m m.2 (t' : G)⟩
      have htr : transport N (RN σ) (t' : G)⁻¹ m = RN σ n := by
        unfold transport; congr 1; ext; simp [n, mul_assoc]
      have hconj_n : (t' : G)⁻¹ * (n : G) * (t' : G) = (m : G) := by
        simp [n, mul_assoc]
      calc X * transport N (RN σ) (t' : G)⁻¹ m
          = A₀ * (M * RN σ n) := by rw [htr, Matrix.mul_assoc]
        _ = A₀ * (Rη σ η ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩ * M) := by
            rw [hM_N n]
        _ = (A₀ * Rη σ η ⟨n.1, mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 n⟩) * M :=
            (Matrix.mul_assoc _ _ _).symm
        _ = (Rη σ' η' ⟨(t' : G)⁻¹ * (n : G) * (t' : G),
              mem_inertia_of_mem_normal N RN σ' (hRN.1 σ').1 ⟨_, conj_inv_mem N (t' : G) n⟩⟩ * A₀) * M := by
            rw [hA₀_N n]
        _ = Rη σ' η' ⟨m.1, mem_inertia_of_mem_normal N RN σ' (hRN.1 σ').1 m⟩ * X := by
            have heq : (⟨(t' : G)⁻¹ * (n : G) * (t' : G),
                mem_inertia_of_mem_normal N RN σ' (hRN.1 σ').1 ⟨_, conj_inv_mem N (t' : G) n⟩⟩ : K') =
                ⟨m.1, mem_inertia_of_mem_normal N RN σ' (hRN.1 σ').1 m⟩ := by
              ext; exact hconj_n
            rw [heq, Matrix.mul_assoc]
    have hX0 : X = 0 := isSuccessor_intertwiner_zero N RN hRN σ'
      ((hRη σ' hσ').1 η') ((hRη σ' hσ').2.1 η') hsucc'
      (transport_isIrreducibleRep N (hRN.2.1 σ) (t' : G)⁻¹) hnot_equiv hX
    calc A₀ * (Rη σ η k * S₀)
        = A₀ * (Rη σ η k * S₀) * (D * C) := by rw [hDC, Matrix.mul_one]
      _ = (A₀ * M) * C := by simp only [M, Matrix.mul_assoc]
      _ = X * C := rfl
      _ = 0 := by rw [hX0, Matrix.zero_mul]
  rw [← mulVecLin_eq_zero_iff]
  intro v
  have hvU : v ∈ U := hUtop.symm ▸ Submodule.mem_top
  refine Submodule.span_induction (p := fun v _ => A₀ *ᵥ v = 0) ?_ ?_ ?_ ?_ hvU
  · rintro _ ⟨k, u, rfl⟩
    rw [Matrix.mulVec_mulVec, hkill k, Matrix.zero_mulVec]
  · simp [Matrix.mulVec_zero]
  · intro a b _ _ ha hb; rw [Matrix.mulVec_add, ha, hb, add_zero]
  · intro c a _ ha; rw [Matrix.mulVec_smul, ha, smul_zero]

private theorem indRep_intertwiner_structure {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (T : ΛN → Set G)
    (hT : ∀ σ ∈ O, Subgroup.IsComplement (T σ) (inertia N RN σ : Set G) ∧ (1 : G) ∈ T σ)
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, inertia N RN σ → Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ))
    {σ : ΛN} (hσ : σ ∈ O) {η η' : Λη σ}
    (hsucc : IsSuccessor N RN σ (Rη σ η)) (hsucc' : IsSuccessor N RN σ (Rη σ η'))
    {A : Matrix (T σ × Bη σ η') (T σ × Bη σ η) ℂ}
    (hA : ∀ g : G,
      A * indRep (inertia N RN σ) (T σ) (Rη σ η) g =
        indRep (inertia N RN σ) (T σ) (Rη σ η') g * A) :
    (∀ k : inertia N RN σ,
      indBlock (T σ) (T σ) A ⟨1, (hT σ hσ).2⟩ ⟨1, (hT σ hσ).2⟩ * Rη σ η k =
        Rη σ η' k * indBlock (T σ) (T σ) A ⟨1, (hT σ hσ).2⟩ ⟨1, (hT σ hσ).2⟩) ∧
    (∀ s t : T σ,
      indBlock (T σ) (T σ) A s t =
        if s = t then indBlock (T σ) (T σ) A ⟨1, (hT σ hσ).2⟩ ⟨1, (hT σ hσ).2⟩ else 0) := by
  let K := inertia N RN σ
  let e₁ : T σ := ⟨1, (hT σ hσ).2⟩
  have hoff : ∀ r : T σ, r ≠ e₁ → indBlock (T σ) (T σ) A r e₁ = 0 := by
    intro r hr
    apply indBlock_col_one_vanish N BN RN hRN O hO T hT Rη hRη hσ hσ hsucc hsucc' hA r
    right
    intro hr1
    apply hr
    exact Subtype.ext hr1
  have hK : ∀ k : K,
      indBlock (T σ) (T σ) A e₁ e₁ * Rη σ η k =
        Rη σ η' k * indBlock (T σ) (T σ) A e₁ e₁ := by
    intro k
    ext j' j
    have heval := congr_fun (congr_fun (hA (k : G)) (e₁, j')) (e₁, j)
    simp only [Matrix.mul_apply] at heval
    have hLHS :
        ∑ x : T σ × Bη σ η, A (e₁, j') x * indRep K (T σ) (Rη σ η) (k : G) x (e₁, j) =
        (indBlock (T σ) (T σ) A e₁ e₁ * Rη σ η k) j' j := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single e₁]
      · simp only [Matrix.mul_apply, indBlock, Matrix.of_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [indRep_apply_sub_col_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η) k e₁ l j,
          if_pos rfl]
      · intro s _ hs
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [indRep_apply_sub_col_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η) k s l j,
          if_neg hs, mul_zero]
      · intro he; exact False.elim (he (Finset.mem_univ _))
    have hRHS :
        ∑ x : T σ × Bη σ η', indRep K (T σ) (Rη σ η') (k : G) (e₁, j') x * A x (e₁, j) =
        (Rη σ η' k * indBlock (T σ) (T σ) A e₁ e₁) j' j := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single e₁]
      · simp only [Matrix.mul_apply, indBlock, Matrix.of_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [indRep_apply_sub_row_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η') k e₁ j' l,
          if_pos rfl]
      · intro s _ hs
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [indRep_apply_sub_row_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η') k s j' l,
          if_neg hs, zero_mul]
      · intro he; exact False.elim (he (Finset.mem_univ _))
    rw [hLHS, hRHS] at heval
    exact heval
  refine ⟨hK, fun s t => ?_⟩
  ext j' j
  have heval := congr_fun (congr_fun (hA (t : G)) (s, j')) (e₁, j)
  simp only [Matrix.mul_apply] at heval
  have hLHS :
      ∑ x : T σ × Bη σ η, A (s, j') x * indRep K (T σ) (Rη σ η) (t : G) x (e₁, j) =
      indBlock (T σ) (T σ) A s t j' j := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single t]
    · rw [Finset.sum_eq_single j]
      · rw [indRep_apply_col_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η)
          ((hRη σ hσ).1 η).1 t t j j, if_pos rfl, if_pos rfl, mul_one]
        rfl
      · intro l _ hl
        rw [indRep_apply_col_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η)
          ((hRη σ hσ).1 η).1 t t l j, if_pos rfl, if_neg hl, mul_zero]
      · intro hj; exact False.elim (hj (Finset.mem_univ _))
    · intro r _ hr
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [indRep_apply_col_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η)
        ((hRη σ hσ).1 η).1 t r l j, if_neg hr, mul_zero]
    · intro ht; exact False.elim (ht (Finset.mem_univ _))
  have hRHS :
      ∑ x : T σ × Bη σ η', indRep K (T σ) (Rη σ η') (t : G) (s, j') x * A x (e₁, j) =
      if s = t then indBlock (T σ) (T σ) A e₁ e₁ j' j else 0 := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single e₁]
    · have hind : ∀ l, indRep K (T σ) (Rη σ η') (t : G) (s, j') (e₁, l) =
          if s = t then (if j' = l then 1 else 0) else 0 := fun l =>
        indRep_apply_col_one K (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η')
          ((hRη σ hσ).1 η').1 t s j' l
      simp_rw [hind]
      split_ifs with hst
      · rw [Finset.sum_eq_single j']
        · simp [indBlock]
        · intro l _ hl; simp [Ne.symm hl]
        · intro hj'; exact False.elim (hj' (Finset.mem_univ _))
      · simp
    · intro r _ hr
      refine Finset.sum_eq_zero fun l _ => ?_
      have hzero : A (r, l) (e₁, j) = 0 := by
        have := congr_fun (congr_fun (hoff r hr) l) j
        simpa [indBlock] using this
      rw [hzero, mul_zero]
    · intro he; exact False.elim (he (Finset.mem_univ _))
  rw [hLHS, hRHS] at heval
  by_cases hst : s = t
  · subst hst
    simpa [if_pos rfl] using heval
  · simpa [if_neg hst] using heval

/-! ### Section 5: Clauses 1, 2, 3 of Theorem 7.8 -/

private theorem clause_1 {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (T : ΛN → Set G)
    (hT : ∀ σ ∈ O, Subgroup.IsComplement (T σ) (inertia N RN σ : Set G) ∧ (1 : G) ∈ T σ)
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, inertia N RN σ → Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ))
    {σ : ΛN} (hσ : σ ∈ O) (η : Λη σ) (hsucc : IsSuccessor N RN σ (Rη σ η)) :
    IsUnitaryRep (indRep (inertia N RN σ) (T σ) (Rη σ η)) ∧
      IsIrreducibleRep (indRep (inertia N RN σ) (T σ) (Rη σ η)) := by
  have hunit : IsUnitaryRep (indRep (inertia N RN σ) (T σ) (Rη σ η)) :=
    indRep_isUnitaryRep (inertia N RN σ) (T σ) (hT σ hσ).1 ((hRη σ hσ).1 η)
  refine ⟨hunit, ?_⟩
  have : Nonempty (T σ) := ⟨⟨1, (hT σ hσ).2⟩⟩
  have : Nonempty (Bη σ η) := ((hRη σ hσ).2.1 η).1
  refine ⟨inferInstance, fun W hW => ?_⟩
  obtain ⟨P, hPP, hP_comm, hP_range, hP_fix⟩ := exists_invariant_proj hunit.1 hW
  obtain ⟨hK, hblocks⟩ := indRep_intertwiner_structure N BN RN hRN O hO T hT Rη hRη hσ hsucc hsucc
    (A := P) hP_comm
  obtain ⟨c, hc⟩ := schur_eq_smul_one ((hRη σ hσ).2.1 η) (fun k => (hK k).symm)
  have hP_entry : ∀ (s t : T σ) (j' j : Bη σ η),
      P (s, j') (t, j) = if s = t then (if j' = j then c else 0) else 0 := by
    intro s t j' j
    have hblk := hblocks s t
    by_cases hst : s = t
    · rw [if_pos hst, hc] at hblk
      have he := congr_fun (congr_fun hblk j') j
      change P (s, j') (t, j) = (c • (1 : Matrix (Bη σ η) (Bη σ η) ℂ)) j' j at he
      rw [he, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, if_pos hst]
      by_cases hj : j' = j
      · subst hj; simp
      · simp [hj]
    · rw [if_neg hst] at hblk
      have he := congr_fun (congr_fun hblk j') j
      change P (s, j') (t, j) = 0 at he
      rw [he, if_neg hst]
  have hc_idem : c * c = c := by
    let t0 : T σ := ⟨1, (hT σ hσ).2⟩
    let j0 : Bη σ η := Classical.arbitrary (Bη σ η)
    have hdiag := congr_fun (congr_fun hPP (t0, j0)) (t0, j0)
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single t0] at hdiag
    · rw [Finset.sum_eq_single j0] at hdiag
      · simp only [hP_entry] at hdiag
        simpa using hdiag
      · intro j _ hj
        simp [hP_entry, hj, Ne.symm hj]
      · intro hj0; exact False.elim (hj0 (Finset.mem_univ _))
    · intro t _ ht
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hP_entry, ht, ht.symm]
    · intro ht0; exact False.elim (ht0 (Finset.mem_univ _))
  have hc01 : c = 0 ∨ c = 1 := by
    have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hc_idem, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · left; exact h
    · right; exact sub_eq_zero.mp h
  rcases hc01 with rfl | rfl
  · left
    have hP0 : P = 0 := by
      ext ⟨s, j'⟩ ⟨t, j⟩
      rw [hP_entry]
      split_ifs <;> simp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hfix := hP_fix v hv
    rw [hP0, Matrix.zero_mulVec] at hfix
    exact hfix.symm
  · right
    have hP1 : P = 1 := by
      ext ⟨s, j'⟩ ⟨t, j⟩
      rw [hP_entry]
      by_cases hst : s = t <;> by_cases hj : j' = j
      · subst hst; subst hj; simp
      · subst hst; simp [hj]
      · simp [hst]
      · simp [hst]
    rw [eq_top_iff]
    intro v _
    have hv := hP_range v
    rw [hP1, Matrix.one_mulVec] at hv
    exact hv

private theorem clause_2 {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (T : ΛN → Set G)
    (hT : ∀ σ ∈ O, Subgroup.IsComplement (T σ) (inertia N RN σ : Set G) ∧ (1 : G) ∈ T σ)
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, inertia N RN σ → Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ))
    {p p' : Σ σ : ΛN, Λη σ}
    (hp : p.1 ∈ O ∧ IsSuccessor N RN p.1 (Rη p.1 p.2))
    (hp' : p'.1 ∈ O ∧ IsSuccessor N RN p'.1 (Rη p'.1 p'.2))
    (heq : RepEquiv (indRep (inertia N RN p.1) (T p.1) (Rη p.1 p.2))
      (indRep (inertia N RN p'.1) (T p'.1) (Rη p'.1 p'.2))) :
    p = p' := by
  rcases p with ⟨σ, η⟩
  rcases p' with ⟨σ', η'⟩
  rcases hp with ⟨hσ, hsucc⟩
  rcases hp' with ⟨hσ', hsucc'⟩
  obtain ⟨A, B, hAB, hBA, hA_inter⟩ := heq
  have hA : ∀ g : G,
      A * indRep (inertia N RN σ) (T σ) (Rη σ η) g =
        indRep (inertia N RN σ') (T σ') (Rη σ' η') g * A := fun g => hA_inter g (Set.mem_univ _)
  have hAne : A ≠ 0 := by
    intro hA0
    rw [hA0, Matrix.zero_mul] at hAB
    have : Nonempty (T σ' × Bη σ' η') := ⟨⟨⟨1, (hT σ' hσ').2⟩, ((hRη σ' hσ').2.1 η').1.some⟩⟩
    have hdiag := congr_fun (congr_fun hAB (Classical.arbitrary _)) (Classical.arbitrary _)
    simp at hdiag
  have hσ_eq : σ = σ' := by
    by_contra hσne
    have hcol1 : ∀ r : T σ', indBlock (T σ) (T σ') A r ⟨1, (hT σ hσ).2⟩ = 0 := fun r =>
      indBlock_col_one_vanish N BN RN hRN O hO T hT Rη hRη hσ hσ' hsucc hsucc' hA r (Or.inl hσne)
    apply hAne
    ext ⟨s', j'⟩ ⟨t, j⟩
    have heval := congr_fun (congr_fun (hA (t : G)) (s', j')) (⟨1, (hT σ hσ).2⟩, j)
    simp only [Matrix.mul_apply] at heval
    have hLHS :
        ∑ x : T σ × Bη σ η, A (s', j') x *
          indRep (inertia N RN σ) (T σ) (Rη σ η) (t : G) x (⟨1, (hT σ hσ).2⟩, j) =
        A (s', j') (t, j) := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single j]
        · rw [indRep_apply_col_one (inertia N RN σ) (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η)
            ((hRη σ hσ).1 η).1 t t j j, if_pos rfl, if_pos rfl, mul_one]
        · intro l _ hl
          rw [indRep_apply_col_one (inertia N RN σ) (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η)
            ((hRη σ hσ).1 η).1 t t l j, if_pos rfl, if_neg hl, mul_zero]
        · intro hj; exact False.elim (hj (Finset.mem_univ _))
      · intro r _ hr
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [indRep_apply_col_one (inertia N RN σ) (T σ) (hT σ hσ).1 (hT σ hσ).2 (Rη σ η)
          ((hRη σ hσ).1 η).1 t r l j, if_neg hr, mul_zero]
      · intro ht; exact False.elim (ht (Finset.mem_univ _))
    have hRHS :
        ∑ x : T σ' × Bη σ' η',
          indRep (inertia N RN σ') (T σ') (Rη σ' η') (t : G) (s', j') x *
            A x (⟨1, (hT σ hσ).2⟩, j) = 0 := by
      refine Finset.sum_eq_zero fun ⟨r, l⟩ _ => ?_
      have h0 := congr_fun (congr_fun (hcol1 r) l) j
      simp only [indBlock, Matrix.of_apply, Matrix.zero_apply] at h0
      rw [h0, mul_zero]
    rw [hLHS, hRHS] at heval
    exact heval
  subst hσ_eq
  obtain ⟨hK, hblocks⟩ := indRep_intertwiner_structure N BN RN hRN O hO T hT Rη hRη hσ hsucc hsucc' hA
  let A11 := indBlock (T σ) (T σ) A ⟨1, (hT σ hσ).2⟩ ⟨1, (hT σ hσ).2⟩
  have hA11_ne : A11 ≠ 0 := by
    intro h0
    apply hAne
    ext ⟨s, j'⟩ ⟨t, j⟩
    have hst := congr_fun (congr_fun (hblocks s t) j') j
    simp only [indBlock, Matrix.of_apply] at hst
    rw [hst]
    split_ifs
    · simpa [A11, indBlock] using congr_fun (congr_fun h0 j') j
    · rfl
  have hequiv_η : RepEquiv (Rη σ η) (Rη σ η') := by
    by_contra hne
    exact hA11_ne (schur_zero_of_not_repEquiv ((hRη σ hσ).2.1 η) ((hRη σ hσ).2.1 η') hne hK)
  have hη_eq : η = η' := by
    by_contra hηne'
    exact (hRη σ hσ).2.2.1 η η' hηne' hequiv_η
  exact congrArg (Sigma.mk σ) hη_eq

private theorem clause_3 {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (T : ΛN → Set G)
    (hT : ∀ σ ∈ O, Subgroup.IsComplement (T σ) (inertia N RN σ : Set G) ∧ (1 : G) ∈ T σ)
    (Λη : ΛN → Type) [∀ σ, Fintype (Λη σ)] (Bη : ∀ σ, Λη σ → Type) [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, inertia N RN σ → Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : G → Matrix ι ι ℂ)
    (hρ_mat : IsMatRep ρ) (hρ_irr : IsIrreducibleRep ρ) :
    ∃ p : Σ σ : ΛN, Λη σ,
      (p.1 ∈ O ∧ IsSuccessor N RN p.1 (Rη p.1 p.2)) ∧
        RepEquiv (indRep (inertia N RN p.1) (T p.1) (Rη p.1 p.2)) ρ := by
  have : Nonempty ι := hρ_irr.1
  -- Step 1: Restrict `ρ` to `N`, extract a minimal `N`-invariant subspace, and match with `RN l`
  let ρN : N → Matrix ι ι ℂ := fun n => ρ (n : G)
  have hρN_mat : IsMatRep ρN := ⟨hρ_mat.1, fun m n => hρ_mat.2 m.1 n.1⟩
  have htop_ne : (⊤ : Submodule ℂ (ι → ℂ)) ≠ ⊥ := by
    intro htop
    have h1 : Pi.single (Classical.arbitrary ι) (1 : ℂ) ∈ (⊥ : Submodule ℂ (ι → ℂ)) :=
      htop ▸ Submodule.mem_top
    have h0 := congr_fun h1 (Classical.arbitrary ι)
    simp at h0
  have htop_inv : IsInvariantSubspace ρN (⊤ : Submodule ℂ (ι → ℂ)) := fun _ _ _ => Submodule.mem_top
  obtain ⟨d₀, U₀, hU₀inv, b₀, _, hU₀ne, hρ₀_mat, hρ₀_irr⟩ :=
    exists_min_invariant_subrep hρN_mat htop_ne htop_inv
  let L_U₀ : N → U₀ →ₗ[ℂ] U₀ := fun n =>
    { toFun := fun u => ⟨ρN n *ᵥ u.1, hU₀inv n u.1 u.2⟩
      map_add' := fun u₁ u₂ => Subtype.ext (Matrix.mulVec_add _ _ _)
      map_smul' := fun c u => Subtype.ext (Matrix.mulVec_smul _ _ _) }
  let ρ₀ : N → Matrix (Fin d₀) (Fin d₀) ℂ := fun n => LinearMap.toMatrix b₀ b₀ (L_U₀ n)
  let M₀_lin : (Fin d₀ → ℂ) →ₗ[ℂ] (ι → ℂ) := U₀.subtype.comp b₀.equivFun.symm.toLinearMap
  let M₀ : Matrix ι (Fin d₀) ℂ := LinearMap.toMatrix' M₀_lin
  have hM₀_lin : M₀.mulVecLin = M₀_lin :=
    LinearMap.toMatrix'.injective (LinearMap.toMatrix'_toLin' M₀)
  have hM₀_apply : ∀ v : Fin d₀ → ℂ, M₀ *ᵥ v = (b₀.equivFun.symm v : ι → ℂ) := fun v => by
    change M₀.mulVecLin v = M₀_lin v
    rw [hM₀_lin]
  have hM₀_ne : M₀ ≠ 0 := by
    intro h0
    have : Nonempty (Fin d₀) := hρ₀_irr.1
    let v : Fin d₀ → ℂ := Pi.single (Classical.arbitrary (Fin d₀)) 1
    have hv : v ≠ 0 := by
      intro hv0
      have := congr_fun hv0 (Classical.arbitrary (Fin d₀))
      simp [v] at this
    have hmv := hM₀_apply v
    rw [h0, Matrix.zero_mulVec] at hmv
    apply hv
    have hsub : b₀.equivFun.symm v = 0 := Subtype.ext hmv.symm
    have h0v := congrArg b₀.equivFun hsub
    rw [b₀.equivFun.apply_symm_apply, map_zero] at h0v
    exact h0v
  have hM₀_inter : ∀ n : N, M₀ * ρ₀ n = ρ (n : G) * M₀ := fun n => by
    rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
    intro v
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hM₀_apply, hM₀_apply]
    have hLU : L_U₀ n (b₀.equivFun.symm v) = b₀.equivFun.symm (ρ₀ n *ᵥ v) := by
      have hthis := Matrix.toLin_apply b₀ b₀ (ρ₀ n) (b₀.equivFun.symm v)
      rw [Matrix.toLin_toMatrix] at hthis
      have hrepr : (b₀.repr (b₀.equivFun.symm v) : Fin d₀ → ℂ) = v := b₀.equivFun.apply_symm_apply v
      rw [hrepr, ← b₀.equivFun_symm_apply] at hthis
      exact hthis
    have hval := congrArg Subtype.val hLU
    change ρ (n : G) *ᵥ (b₀.equivFun.symm v : ι → ℂ) = (b₀.equivFun.symm (ρ₀ n *ᵥ v) : ι → ℂ) at hval
    rw [hval, sub_self]
  obtain ⟨l, A₀, B₀, hAB₀, hBA₀, hA₀_inter⟩ := hRN.2.2.2 (Fin d₀) ρ₀ hρ₀_mat hρ₀_irr
  -- Step 2: Move from `l` to the orbit representative `σ ∈ O`
  obtain ⟨σ, hσ, _⟩ := hO l
  have hσO : σ.1 ∈ O := σ.2
  obtain ⟨g₀, C₀, D₀, hCD₀, hDC₀, hC₀_inter⟩ := hσ
  have hD₀_inter : ∀ m : N, RN l m * D₀ = D₀ * transport N (RN σ.1) g₀ m := fun m => by
    calc RN l m * D₀ = (D₀ * C₀) * RN l m * D₀ := by rw [hDC₀, Matrix.one_mul]
      _ = D₀ * (C₀ * RN l m) * D₀ := by simp only [Matrix.mul_assoc]
      _ = D₀ * (transport N (RN σ.1) g₀ m * C₀) * D₀ := by rw [hC₀_inter m (Set.mem_univ _)]
      _ = D₀ * transport N (RN σ.1) g₀ m * (C₀ * D₀) := by simp only [Matrix.mul_assoc]
      _ = D₀ * transport N (RN σ.1) g₀ m := by rw [hCD₀, Matrix.mul_one]
  let A₁ : Matrix ι (BN σ.1) ℂ := ρ g₀⁻¹ * (M₀ * A₀) * D₀
  have hA₁_ne : A₁ ≠ 0 := by
    intro h0
    apply hM₀_ne
    have h1 : ρ g₀ * A₁ * C₀ * B₀ = M₀ := by
      calc ρ g₀ * A₁ * C₀ * B₀
          = (ρ g₀ * ρ g₀⁻¹) * (M₀ * A₀) * (D₀ * C₀) * B₀ := by simp only [A₁, Matrix.mul_assoc]
        _ = M₀ * A₀ * B₀ := by
              rw [isMatRep_mul_inv hρ_mat g₀, Matrix.one_mul, hDC₀, Matrix.mul_one]
        _ = M₀ * (A₀ * B₀) := Matrix.mul_assoc _ _ _
        _ = M₀ := by rw [hAB₀, Matrix.mul_one]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at h1
    exact h1.symm
  have hA₁_inter : ∀ n : N, A₁ * RN σ.1 n = ρ (n : G) * A₁ := fun n => by
    let m : N := ⟨g₀ * (n : G) * g₀⁻¹, by simpa using (inferInstance : N.Normal).conj_mem n n.2 g₀⟩
    have htr : transport N (RN σ.1) g₀ m = RN σ.1 n := by
      unfold transport; congr 1; ext; simp [m, mul_assoc]
    calc A₁ * RN σ.1 n
        = ρ g₀⁻¹ * (M₀ * A₀) * (D₀ * transport N (RN σ.1) g₀ m) := by
            rw [htr]; simp only [A₁, Matrix.mul_assoc]
      _ = ρ g₀⁻¹ * (M₀ * A₀) * (RN l m * D₀) := by rw [hD₀_inter m]
      _ = ρ g₀⁻¹ * (M₀ * (A₀ * RN l m)) * D₀ := by simp only [Matrix.mul_assoc]
      _ = ρ g₀⁻¹ * (M₀ * (ρ₀ m * A₀)) * D₀ := by rw [hA₀_inter m (Set.mem_univ _)]
      _ = ρ g₀⁻¹ * ((M₀ * ρ₀ m) * A₀) * D₀ := by simp only [Matrix.mul_assoc]
      _ = ρ g₀⁻¹ * ((ρ (m : G) * M₀) * A₀) * D₀ := by rw [hM₀_inter m]
      _ = (ρ g₀⁻¹ * ρ (m : G)) * (M₀ * A₀) * D₀ := by simp only [Matrix.mul_assoc]
      _ = (ρ (n : G) * ρ g₀⁻¹) * (M₀ * A₀) * D₀ := by
            have hg : g₀⁻¹ * (m : G) = (n : G) * g₀⁻¹ := by simp [m, mul_assoc]
            rw [← hρ_mat.2, hg, hρ_mat.2]
      _ = ρ (n : G) * A₁ := by simp only [A₁, Matrix.mul_assoc]
  -- Step 3: Form the `σ`-isotypic subspace `Wσ` and prove it is `I_σ`-invariant
  let K := inertia N RN σ.1
  let Wσ : Submodule ℂ (ι → ℂ) :=
    Submodule.span ℂ {v | ∃ A : Matrix ι (BN σ.1) ℂ, (∀ n : N, A * RN σ.1 n = ρ (n : G) * A) ∧
      ∃ u : BN σ.1 → ℂ, A *ᵥ u = v}
  have hWσ_ne : Wσ ≠ ⊥ := by
    intro hbot
    apply hA₁_ne
    rw [← mulVecLin_eq_zero_iff]
    intro u
    have hu : A₁ *ᵥ u ∈ Wσ := Submodule.subset_span ⟨A₁, hA₁_inter, u, rfl⟩
    rw [hbot] at hu
    exact hu
  let ρK : K → Matrix ι ι ℂ := fun k => ρ (k : G)
  have hρK_mat : IsMatRep ρK := ⟨hρ_mat.1, fun k₁ k₂ => hρ_mat.2 k₁.1 k₂.1⟩
  have hWσ_inv : IsInvariantSubspace ρK Wσ := by
    intro k v hv
    refine Submodule.span_induction (p := fun v _ => ρK k *ᵥ v ∈ Wσ) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨A, hA_inter, u, rfl⟩
      obtain ⟨C, D, hCD, hDC, hinter⟩ := k.2
      have hD_inter : ∀ n : N,
          RN σ.1 ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * D = D * RN σ.1 n := by
        intro n
        calc RN σ.1 ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * D
            = (D * C) * RN σ.1 ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩ * D := by
                rw [hDC, Matrix.one_mul]
          _ = D * (C * transport N (RN σ.1) (k : G) n) * D := by
                simp only [transport, Matrix.mul_assoc]
          _ = D * (RN σ.1 n * C) * D := by rw [hinter n (Set.mem_univ _)]
          _ = D * RN σ.1 n * (C * D) := by simp only [Matrix.mul_assoc]
          _ = D * RN σ.1 n := by rw [hCD, Matrix.mul_one]
      let A' : Matrix ι (BN σ.1) ℂ := ρ (k : G) * A * D
      have hA'_inter : ∀ n : N, A' * RN σ.1 n = ρ (n : G) * A' := fun n => by
        let m : N := ⟨(k : G)⁻¹ * (n : G) * (k : G), conj_inv_mem N (k : G) n⟩
        calc A' * RN σ.1 n
            = ρ (k : G) * A * (D * RN σ.1 n) := by simp only [A', Matrix.mul_assoc]
          _ = ρ (k : G) * A * (RN σ.1 m * D) := by rw [hD_inter n]
          _ = ρ (k : G) * (A * RN σ.1 m) * D := by simp only [Matrix.mul_assoc]
          _ = ρ (k : G) * (ρ (m : G) * A) * D := by rw [hA_inter m]
          _ = (ρ (k : G) * ρ (m : G)) * A * D := by simp only [Matrix.mul_assoc]
          _ = (ρ (n : G) * ρ (k : G)) * A * D := by
                have hk : (k : G) * (m : G) = (n : G) * (k : G) := by simp [m, mul_assoc]
                rw [← hρ_mat.2, hk, hρ_mat.2]
          _ = ρ (n : G) * A' := by simp only [A', Matrix.mul_assoc]
      refine Submodule.subset_span ⟨A', hA'_inter, C *ᵥ u, ?_⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      calc A' * C = ρ (k : G) * A * (D * C) := by simp only [A', Matrix.mul_assoc]
        _ = ρ (k : G) * A := by rw [hDC, Matrix.mul_one]
    · simp [Matrix.mulVec_zero]
    · intro a b _ _ ha hb; rw [Matrix.mulVec_add]; exact Wσ.add_mem ha hb
    · intro c a _ ha; rw [Matrix.mulVec_smul]; exact Wσ.smul_mem c ha
  -- Step 4: Minimal `K`-invariant subspace `U ≤ Wσ`, identify with `η : Λη σ.1`
  obtain ⟨m, U, hUinv, b, hUWσ, hUne, hρK_U_mat, hρK_U_irr⟩ :=
    exists_min_invariant_subrep hρK_mat hWσ_ne hWσ_inv
  let L_U : K → U →ₗ[ℂ] U := fun k =>
    { toFun := fun u => ⟨ρK k *ᵥ u.1, hUinv k u.1 u.2⟩
      map_add' := fun u₁ u₂ => Subtype.ext (Matrix.mulVec_add _ _ _)
      map_smul' := fun c u => Subtype.ext (Matrix.mulVec_smul _ _ _) }
  let ρ_U : K → Matrix (Fin m) (Fin m) ℂ := fun k => LinearMap.toMatrix b b (L_U k)
  let M_lin : (Fin m → ℂ) →ₗ[ℂ] (ι → ℂ) := U.subtype.comp b.equivFun.symm.toLinearMap
  let M : Matrix ι (Fin m) ℂ := LinearMap.toMatrix' M_lin
  have hM_lin : M.mulVecLin = M_lin :=
    LinearMap.toMatrix'.injective (LinearMap.toMatrix'_toLin' M)
  have hM_apply : ∀ v : Fin m → ℂ, M *ᵥ v = (b.equivFun.symm v : ι → ℂ) := fun v => by
    change M.mulVecLin v = M_lin v
    rw [hM_lin]
  have hM_inter : ∀ k : K, M * ρ_U k = ρ (k : G) * M := fun k => by
    rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
    intro v
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hM_apply, hM_apply]
    have hLU : L_U k (b.equivFun.symm v) = b.equivFun.symm (ρ_U k *ᵥ v) := by
      have hthis := Matrix.toLin_apply b b (ρ_U k) (b.equivFun.symm v)
      rw [Matrix.toLin_toMatrix] at hthis
      have hrepr : (b.repr (b.equivFun.symm v) : Fin m → ℂ) = v := b.equivFun.apply_symm_apply v
      rw [hrepr, ← b.equivFun_symm_apply] at hthis
      exact hthis
    have hval := congrArg Subtype.val hLU
    change ρ (k : G) *ᵥ (b.equivFun.symm v : ι → ℂ) = (b.equivFun.symm (ρ_U k *ᵥ v) : ι → ℂ) at hval
    rw [hval, sub_self]
  obtain ⟨η, A_η, B_η, hABη, hBAη, hAη_inter⟩ :=
    (hRη σ.1 hσO).2.2.2 (Fin m) ρ_U hρK_U_mat hρK_U_irr
  let J : Matrix ι (Bη σ.1 η) ℂ := M * A_η
  have hJ_apply : ∀ w : Bη σ.1 η → ℂ, J *ᵥ w = (b.equivFun.symm (A_η *ᵥ w) : ι → ℂ) := fun w => by
    rw [← Matrix.mulVec_mulVec, hM_apply]
  have hJ_ne : J ≠ 0 := by
    intro h0
    have : Nonempty (Bη σ.1 η) := ((hRη σ.1 hσO).2.1 η).1
    let w : Bη σ.1 η → ℂ := Pi.single (Classical.arbitrary (Bη σ.1 η)) 1
    have hw0 : w ≠ 0 := by
      intro h
      have := congr_fun h (Classical.arbitrary (Bη σ.1 η))
      simp [w] at this
    have hwJ := hJ_apply w
    rw [h0, Matrix.zero_mulVec] at hwJ
    apply hw0
    have hsub : b.equivFun.symm (A_η *ᵥ w) = 0 := Subtype.ext hwJ.symm
    have hAw0 := congrArg b.equivFun hsub
    rw [b.equivFun.apply_symm_apply, map_zero] at hAw0
    have hw1 : B_η *ᵥ (A_η *ᵥ w) = 0 := by rw [hAw0, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, hBAη, Matrix.one_mulVec] at hw1
    exact hw1
  have hJ_inter : ∀ k : K, J * Rη σ.1 η k = ρ (k : G) * J := fun k => by
    calc J * Rη σ.1 η k = M * (A_η * Rη σ.1 η k) := Matrix.mul_assoc _ _ _
      _ = M * (ρ_U k * A_η) := by rw [hAη_inter k (Set.mem_univ _)]
      _ = (M * ρ_U k) * A_η := (Matrix.mul_assoc _ _ _).symm
      _ = (ρ (k : G) * M) * A_η := by rw [hM_inter k]
      _ = ρ (k : G) * J := Matrix.mul_assoc _ _ _
  -- Step 5: Prove `IsSuccessor N RN σ.1 (Rη σ.1 η)` using Maschke projection for `ρ|_N` onto `U`
  have hU_Ninv : IsInvariantSubspace ρN U := fun n u hu =>
    hUinv ⟨n.1, mem_inertia_of_mem_normal N RN σ.1 (hRN.1 σ.1).1 n⟩ u hu
  let hcompl_N := repOrtho_isCompl hρN_mat U
  let π_U : (ι → ℂ) →ₗ[ℂ] U := U.projectionOnto (repOrtho ρN U) hcompl_N
  let Q_lin : (ι → ℂ) →ₗ[ℂ] (Bη σ.1 η → ℂ) := B_η.mulVecLin.comp (b.equivFun.toLinearMap.comp π_U)
  let Q : Matrix (Bη σ.1 η) ι ℂ := LinearMap.toMatrix' Q_lin
  have hQ_lin : Q.mulVecLin = Q_lin :=
    LinearMap.toMatrix'.injective (LinearMap.toMatrix'_toLin' Q)
  have hQ_apply : ∀ v : ι → ℂ, Q *ᵥ v = B_η *ᵥ b.equivFun (π_U v) := fun v => by
    change Q.mulVecLin v = Q_lin v
    rw [hQ_lin]
  have hQ_inter : ∀ n : N,
      Q * ρ (n : G) = Rη σ.1 η ⟨n.1, mem_inertia_of_mem_normal N RN σ.1 (hRN.1 σ.1).1 n⟩ * Q := by
    intro n
    let nK : K := ⟨n.1, mem_inertia_of_mem_normal N RN σ.1 (hRN.1 σ.1).1 n⟩
    rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
    intro v
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hQ_apply, hQ_apply]
    have hπ : (π_U (ρ (n : G) *ᵥ v) : ι → ℂ) = ρ (n : G) *ᵥ (π_U v : ι → ℂ) :=
      linearProj_invariant_eq hρN_mat hU_Ninv n v
    have hπU : π_U (ρ (n : G) *ᵥ v) = L_U nK (π_U v) := Subtype.ext hπ
    have hb : b.equivFun (L_U nK (π_U v)) = ρ_U nK *ᵥ b.equivFun (π_U v) := by
      have hthis := Matrix.toLin_apply b b (ρ_U nK) (π_U v)
      rw [Matrix.toLin_toMatrix, ← b.equivFun_symm_apply] at hthis
      have hthis' := congrArg b.equivFun hthis
      rw [b.equivFun.apply_symm_apply] at hthis'
      exact hthis'
    have hB_inter : B_η * ρ_U nK = Rη σ.1 η nK * B_η := by
      calc B_η * ρ_U nK = B_η * ρ_U nK * (A_η * B_η) := by rw [hABη, Matrix.mul_one]
        _ = B_η * (ρ_U nK * A_η) * B_η := by simp only [Matrix.mul_assoc]
        _ = B_η * (A_η * Rη σ.1 η nK) * B_η := by rw [hAη_inter nK (Set.mem_univ _)]
        _ = (B_η * A_η) * Rη σ.1 η nK * B_η := by simp only [Matrix.mul_assoc]
        _ = Rη σ.1 η nK * B_η := by rw [hBAη, Matrix.one_mul]
    rw [hπU, hb, Matrix.mulVec_mulVec, hB_inter, ← Matrix.mulVec_mulVec, sub_self]
  have hQ_J : ∀ w : Bη σ.1 η → ℂ, Q *ᵥ (J *ᵥ w) = w := fun w => by
    rw [hQ_apply, hJ_apply]
    have hπ : π_U (b.equivFun.symm (A_η *ᵥ w) : ι → ℂ) = b.equivFun.symm (A_η *ᵥ w) :=
      Submodule.projectionOnto_apply_left hcompl_N (b.equivFun.symm (A_η *ᵥ w))
    rw [hπ]
    simp only [LinearEquiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, hBAη, Matrix.one_mulVec]
  have hsucc_η : IsSuccessor N RN σ.1 (Rη σ.1 η) := by
    have : Nonempty (Bη σ.1 η) := ((hRη σ.1 hσO).2.1 η).1
    let w₀ : Bη σ.1 η → ℂ := Pi.single (Classical.arbitrary (Bη σ.1 η)) 1
    have hw₀ : w₀ ≠ 0 := by
      intro h
      have := congr_fun h (Classical.arbitrary (Bη σ.1 η))
      simp [w₀] at this
    have hJw₀_Wσ : J *ᵥ w₀ ∈ Wσ := by
      rw [hJ_apply]
      exact hUWσ (b.equivFun.symm (A_η *ᵥ w₀)).2
    have hnot_all_zero : ¬ (∀ v ∈ Wσ, Q *ᵥ v = 0) := by
      intro hall
      have := hall (J *ᵥ w₀) hJw₀_Wσ
      rw [hQ_J w₀] at this
      exact hw₀ this
    have hex_A : ∃ A : Matrix ι (BN σ.1) ℂ, (∀ n : N, A * RN σ.1 n = ρ (n : G) * A) ∧
        Q * A ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hnot_all_zero
      intro v hv
      refine Submodule.span_induction (p := fun v _ => Q *ᵥ v = 0) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨A, hA_inter, u, rfl⟩
        rw [Matrix.mulVec_mulVec, hnone A hA_inter, Matrix.zero_mulVec]
      · simp [Matrix.mulVec_zero]
      · intro a b _ _ ha hb; rw [Matrix.mulVec_add, ha, hb, add_zero]
      · intro c a _ ha; rw [Matrix.mulVec_smul, ha, smul_zero]
    obtain ⟨A, hA_inter, hQA_ne⟩ := hex_A
    refine ⟨Q * A, hQA_ne, fun x => ?_⟩
    let n : N := inertiaToN N RN σ.1 x
    have hn_eq : inNInertia N RN σ.1 x =
        ⟨n.1, mem_inertia_of_mem_normal N RN σ.1 (hRN.1 σ.1).1 n⟩ := by
      ext; rfl
    rw [hn_eq]
    calc (Q * A) * RN σ.1 n = Q * (A * RN σ.1 n) := Matrix.mul_assoc _ _ _
      _ = Q * (ρ (n : G) * A) := by rw [hA_inter n]
      _ = (Q * ρ (n : G)) * A := (Matrix.mul_assoc _ _ _).symm
      _ = (Rη σ.1 η ⟨n.1, mem_inertia_of_mem_normal N RN σ.1 (hRN.1 σ.1).1 n⟩ * Q) * A := by
          rw [hQ_inter n]
      _ = Rη σ.1 η ⟨n.1, mem_inertia_of_mem_normal N RN σ.1 (hRN.1 σ.1).1 n⟩ * (Q * A) :=
          Matrix.mul_assoc _ _ _
  -- Step 6: Build nonzero `G`-intertwiner `F : Matrix ι (T σ.1 × Bη σ.1 η) ℂ` and conclude
  let F : Matrix ι (T σ.1 × Bη σ.1 η) ℂ := Matrix.of fun i tj => (ρ (tj.1 : G) * J) i tj.2
  have hF_ne : F ≠ 0 := by
    intro h0
    apply hJ_ne
    ext i j
    have := congr_fun (congr_fun h0 i) (⟨1, (hT σ.1 hσO).2⟩, j)
    simpa [F, hρ_mat.1] using this
  have hF_inter : ∀ g : G,
      F * indRep (inertia N RN σ.1) (T σ.1) (Rη σ.1 η) g = ρ g * F := by
    intro g
    let e : T σ.1 × K ≃ G :=
      Equiv.ofBijective (fun x : T σ.1 × K => (x.1 : G) * (x.2 : G)) (hT σ.1 hσO).1
    ext i ⟨t, j⟩
    let sk := e.symm (g * (t : G))
    let s₀ := sk.1
    let k₀ := sk.2
    have hgt : g * (t : G) = (s₀ : G) * (k₀ : G) := (e.apply_symm_apply (g * (t : G))).symm
    have hm₀ : ((s₀ : G)⁻¹ * g * (t : G)) ∈ K := by
      rw [mul_assoc, hgt, ← mul_assoc, inv_mul_cancel, one_mul]
      exact k₀.2
    have hk₀ : (⟨(s₀ : G)⁻¹ * g * (t : G), hm₀⟩ : K) = k₀ := by
      ext; simp [mul_assoc, hgt]
    simp only [Matrix.mul_apply, F, Matrix.of_apply, indRep]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s₀]
    · have hm₀' : ((s₀ : G)⁻¹ * g * (t : G)) ∈ inertia N RN σ.1 := hm₀
      have hR_eq : ∀ (h : ((s₀ : G)⁻¹ * g * (t : G)) ∈ inertia N RN σ.1) (l : Bη σ.1 η),
          Rη σ.1 η ⟨(s₀ : G)⁻¹ * g * (t : G), h⟩ l j = Rη σ.1 η k₀ l j := fun h l => by
        have hsub : (⟨(s₀ : G)⁻¹ * g * (t : G), h⟩ : inertia N RN σ.1) = k₀ := by
          ext; simp [mul_assoc, hgt]
        rw [hsub]
      simp_rw [dif_pos hm₀', hR_eq]
      have hL : (∑ x : Bη σ.1 η, (∑ x_1, ρ (s₀ : G) i x_1 * J x_1 x) * Rη σ.1 η k₀ x j) =
          ((ρ (s₀ : G) * J) * Rη σ.1 η k₀) i j := by
        simp only [Matrix.mul_apply]
      have hR : (∑ x : ι, ρ g i x * ∑ x_1, ρ (t : G) x x_1 * J x_1 j) =
          (ρ g * (ρ (t : G) * J)) i j := by
        simp only [Matrix.mul_apply]
      rw [hL, hR, Matrix.mul_assoc, hJ_inter k₀, ← Matrix.mul_assoc, ← hρ_mat.2, ← hgt, hρ_mat.2,
        Matrix.mul_assoc]
    · intro s _ hs
      refine Finset.sum_eq_zero fun l _ => ?_
      have hnot : ((s : G)⁻¹ * g * (t : G)) ∉ K := by
        have hiff := complement_mul_mem_iff K (T σ.1) (hT σ.1 hσO).1 g s t
        change ((s : G)⁻¹ * g * (t : G)) ∈ K ↔ s = s₀ at hiff
        rw [hiff]
        exact hs
      rw [dif_neg hnot, mul_zero]
    · intro hs₀; exact False.elim (hs₀ (Finset.mem_univ _))
  have hΦ_irr : IsIrreducibleRep (indRep (inertia N RN σ.1) (T σ.1) (Rη σ.1 η)) :=
    (clause_1 N BN RN hRN O hO T hT Rη hRη hσO η hsucc_η).2
  have hequiv : RepEquiv (indRep (inertia N RN σ.1) (T σ.1) (Rη σ.1 η)) ρ := by
    by_contra hne
    exact hF_ne (schur_zero_of_not_repEquiv hΦ_irr hρ_irr hne hF_inter)
  exact ⟨⟨σ.1, η⟩, ⟨hσO, hsucc_η⟩, hequiv⟩

end GL2QFT.Supplement.Thm78Helpers

open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.Thm78Helpers

theorem solution {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (T : ΛN → Set G)
    (hT : ∀ σ ∈ O, Subgroup.IsComplement (T σ) (inertia N RN σ : Set G) ∧ (1 : G) ∈ T σ)
    (Λη : ΛN → Type) [∀ σ, Fintype (Λη σ)] (Bη : ∀ σ, Λη σ → Type) [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, inertia N RN σ → Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ)) :
    let L : Set (Σ σ : ΛN, Λη σ) := {p | p.1 ∈ O ∧ IsSuccessor N RN p.1 (Rη p.1 p.2)}
    let Φ : ∀ p : Σ σ : ΛN, Λη σ, G → Matrix (T p.1 × Bη p.1 p.2) (T p.1 × Bη p.1 p.2) ℂ :=
      fun p => indRep (inertia N RN p.1) (T p.1) (Rη p.1 p.2)
    (∀ p ∈ L, IsUnitaryRep (Φ p) ∧ IsIrreducibleRep (Φ p)) ∧
    (∀ p ∈ L, ∀ p' ∈ L, RepEquiv (Φ p) (Φ p') → p = p') ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : G → Matrix ι ι ℂ),
      IsMatRep ρ → IsIrreducibleRep ρ → ∃ p ∈ L, RepEquiv (Φ p) ρ) := by
  intro L Φ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact clause_1 N BN RN hRN O hO T hT Rη hRη hp.1 p.2 hp.2
  · intro p hp p' hp' heq
    exact clause_2 N BN RN hRN O hO T hT Rη hRη hp hp' heq
  · intro ι _ _ ρ hρ_mat hρ_irr
    exact clause_3 N BN RN hRN O hO T hT Λη Bη Rη hRη ρ hρ_mat hρ_irr
