-- Prove2me | solution 1 for BosonicLearn.isDensity_prod
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T05:37:57.566648+00:00
-- url     : https://prove2.me/submissions/6b67fcc5-a165-435a-859b-d9d0665dd679

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_OAI_Analysis_TensorLp

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal ComplexOrder

noncomputable section

/-! ### Basic facts on density operators -/

private lemma dens_diag {A : Type} {X : Matrix A A ℂ} (hX : IsDensity X) (i : A) :
    (X i i).im = 0 ∧ 0 ≤ (X i i).re := by
  classical
  have h := hX.2.1 {i} (Pi.single i 1)
  simpa using h

private lemma dens_herm {A : Type} {X : Matrix A A ℂ} (hX : IsDensity X) (i j : A) :
    X j i = star (X i j) := by
  classical
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (dens_diag hX i).1).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := (dens_diag hX i).1
    have hjj := (dens_diag hX j).1
    have h1 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)).1
    have h2 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)).1
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

/-- The block of a matrix on a finite set. -/
private def blk {A : Type} (X : Matrix A A ℂ) (s : Finset A) : Matrix s s ℂ := fun a b => X a b

/-- The block of a density operator on a finite set is a positive semidefinite matrix. -/
private lemma block_psd {A : Type} {X : Matrix A A ℂ} (hX : IsDensity X) (s : Finset A) :
    (blk X s).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, blk]
    exact (dens_herm hX b a).symm
  · let z : A → ℂ := fun i => if h : i ∈ s then x ⟨i, h⟩ else 0
    have h := hX.2.1 s z
    have e : star x ⬝ᵥ (blk X s).mulVec x =
        ∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j := by
      rw [← Finset.sum_coe_sort s]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [z, blk, mul_assoc]
    rw [e, Complex.nonneg_iff]
    exact ⟨h.2, h.1.symm⟩

/-- The quadratic form of `X ⊗ Y` on a product of finite sets is non-negative: the Kronecker product of two
positive semidefinite matrices is positive semidefinite. -/
private lemma kron_form {A B : Type} {X : Matrix A A ℂ} {Y : Matrix B B ℂ} (hX : IsDensity X)
    (hY : IsDensity Y) (s₁ : Finset A) (s₂ : Finset B) (z : A × B → ℂ) :
    0 ≤ ∑ p ∈ s₁ ×ˢ s₂, ∑ q ∈ s₁ ×ˢ s₂, star (z p) * (X p.1 q.1 * Y p.2 q.2) * z q := by
  have hK := (block_psd hX s₁).kronecker (block_psd hY s₂)
  have h := hK.dotProduct_mulVec_nonneg (fun p : s₁ × s₂ => z ((p.1 : A), (p.2 : B)))
  have e : star (fun p : s₁ × s₂ => z ((p.1 : A), (p.2 : B))) ⬝ᵥ
      (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (blk X s₁) (blk Y s₂)).mulVec
        (fun p : s₁ × s₂ => z ((p.1 : A), (p.2 : B))) =
      ∑ p ∈ s₁ ×ˢ s₂, ∑ q ∈ s₁ ×ˢ s₂, star (z p) * (X p.1 q.1 * Y p.2 q.2) * z q := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Finset.sum_product, blk]
    rw [← Finset.sum_coe_sort s₁]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort s₂]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_coe_sort s₁]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Finset.sum_coe_sort s₂]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  rwa [e] at h

/-! ### The statement -/

theorem solution {A B : Type} {X : Matrix A A ℂ} {Y : Matrix B B ℂ}
    (hX : IsDensity X) (hY : IsDensity Y) :
    IsDensity (fun p q : A × B => X p.1 q.1 * Y p.2 q.2) := by
  classical
  obtain ⟨ex⟩ := hX.1
  obtain ⟨ey⟩ := hY.1
  -- norm-summability of the entry series of the two expansions
  have hnx : ∀ a a' : A, Summable fun m => ‖ex.left m a * star (ex.right m a')‖ := by
    intro a a'
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) ex.summable
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ a)
      (lp.norm_apply_le_norm (by norm_num) _ a') (norm_nonneg _) (norm_nonneg _)
  have hny : ∀ b b' : B, Summable fun m => ‖ey.left m b * star (ey.right m b')‖ := by
    intro b b'
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) ey.summable
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ b)
      (lp.norm_apply_le_norm (by norm_num) _ b') (norm_nonneg _) (norm_nonneg _)
  refine ⟨⟨{
    left := fun k => OAI.TensorLp.tensor (ex.left (Nat.unpair k).1) (ey.left (Nat.unpair k).2)
    right := fun k => OAI.TensorLp.tensor (ex.right (Nat.unpair k).1) (ey.right (Nat.unpair k).2)
    summable := ?_
    coefficients := ?_ }⟩, ?_, ?_, ?_⟩
  · -- the weights are the products of the weights
    have h := ex.summable.mul_of_nonneg ey.summable
      (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have h' := (Equiv.summable_iff Nat.pairEquiv.symm).mpr h
    refine h'.congr fun k => ?_
    simp only [Function.comp_apply, OAI.TensorLp.tensor_norm]
    show ‖ex.left (Nat.unpair k).1‖ * ‖ex.right (Nat.unpair k).1‖ *
        (‖ey.left (Nat.unpair k).2‖ * ‖ey.right (Nat.unpair k).2‖) = _
    ring
  · intro p q
    obtain ⟨a, b⟩ := p
    obtain ⟨a', b'⟩ := q
    show X a a' * Y b b' = _
    rw [ex.coefficients a a', ey.coefficients b b', tsum_mul_tsum_of_summable_norm (hnx a a') (hny b b')]
    rw [← Equiv.tsum_eq Nat.pairEquiv.symm]
    refine tsum_congr fun k => ?_
    show ex.left (Nat.unpair k).1 a * star (ex.right (Nat.unpair k).1 a') *
        (ey.left (Nat.unpair k).2 b * star (ey.right (Nat.unpair k).2 b')) = _
    simp only [OAI.TensorLp.tensor_apply, star_mul']
    ring
  · -- quadratic forms: extend the finite set to a product of finite sets
    intro s z
    have hsub : s ⊆ s.image Prod.fst ×ˢ s.image Prod.snd := fun p hp =>
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    have h := kron_form hX hY (s.image Prod.fst) (s.image Prod.snd) (fun p => if p ∈ s then z p else 0)
    have e : ∑ p ∈ s.image Prod.fst ×ˢ s.image Prod.snd, ∑ q ∈ s.image Prod.fst ×ˢ s.image Prod.snd,
        star (if p ∈ s then z p else 0) * (X p.1 q.1 * Y p.2 q.2) * (if q ∈ s then z q else 0) =
        ∑ p ∈ s, ∑ q ∈ s, star (z p) * (X p.1 q.1 * Y p.2 q.2) * z q := by
      rw [← Finset.sum_subset hsub (fun p _ hp => by simp [hp])]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← Finset.sum_subset hsub (fun q _ hq => by simp [hq])]
      refine Finset.sum_congr rfl fun q hq => ?_
      simp [hp, hq]
    rw [e, Complex.nonneg_iff] at h
    exact ⟨h.2.symm, h.1⟩
  · -- the diagonal is the product of the diagonals
    have hre : ∀ p : A × B, (X p.1 p.1 * Y p.2 p.2).re = (X p.1 p.1).re * (Y p.2 p.2).re := by
      intro p
      rw [Complex.mul_re, (dens_diag hX p.1).1, (dens_diag hY p.2).1]
      ring
    have h := hX.2.2.1.mul_of_nonneg hY.2.2.1 (fun a => (dens_diag hX a).2) (fun b => (dens_diag hY b).2)
    exact h.congr fun p => (hre p).symm
  · have hre : ∀ p : A × B, (X p.1 p.1 * Y p.2 p.2).re = (X p.1 p.1).re * (Y p.2 p.2).re := by
      intro p
      rw [Complex.mul_re, (dens_diag hX p.1).1, (dens_diag hY p.2).1]
      ring
    rw [tsum_congr hre, ← tsum_mul_tsum_of_summable_norm hX.2.2.1.norm hY.2.2.1.norm, hX.2.2.2,
      hY.2.2.2, one_mul]
