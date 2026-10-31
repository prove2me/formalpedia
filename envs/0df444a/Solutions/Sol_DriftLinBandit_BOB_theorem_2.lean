-- Prove2me | solution 1 for DriftLinBandit.BOB.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:00:44.913024+00:00
-- url     : https://prove2.me/submissions/3085fdb8-e6e0-4294-af95-8c26b8842929
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model
import Theorems.Thm_DriftLinBandit_BOB_lemma_3
import Theorems.Thm_DriftLinBandit_BOB_lemma_4

open MeasureTheory Matrix DriftLinBandit.BOB

namespace BOBThm2Aux

lemma gram_transpose {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) :
    (gram lam X W)ᵀ = gram lam X W := by
  unfold DriftLinBandit.BOB.gram
  rw [transpose_add, transpose_smul, transpose_one, transpose_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  ext i j; simp [vecMulVec_apply, mul_comm]

lemma gram_quad {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) (y : Fin d → ℝ) :
    y ⬝ᵥ (gram lam X W *ᵥ y) = lam * (y ⬝ᵥ y) + ∑ s ∈ W, (X s ⬝ᵥ y) ^ 2 := by
  unfold DriftLinBandit.BOB.gram
  rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  rw [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vecMulVec_mulVec, dotProduct_smul]
  simp [dotProduct_comm y (X s), sq]

lemma gram_isUnit {d : ℕ} (lam : ℝ) (hlam : 0 < lam) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) :
    IsUnit (gram lam X W) := by
  rw [← mulVec_injective_iff_isUnit]
  intro a b hab
  have h : gram lam X W *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  have hq := gram_quad lam X W (a - b)
  rw [h, dotProduct_zero] at hq
  have hs : 0 ≤ ∑ s ∈ W, (X s ⬝ᵥ (a - b)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdd : 0 ≤ (a - b) ⬝ᵥ (a - b) := by
    rw [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hz : (a - b) ⬝ᵥ (a - b) = 0 := by nlinarith
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 hz)


lemma gram_mulVec {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) (y : Fin d → ℝ) :
    gram lam X W *ᵥ y = lam • y + ∑ s ∈ W, (X s ⬝ᵥ y) • X s := by
  unfold DriftLinBandit.BOB.gram
  rw [add_mulVec, smul_mulVec, one_mulVec, sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vecMulVec_mulVec]
  simp

lemma l2_eq {d : ℕ} (x : Fin d → ℝ) : l2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq, l2]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq]


lemma dot_le_l2 {d : ℕ} (x v : Fin d → ℝ) : |x ⬝ᵥ v| ≤ l2 x * l2 v := by
  rw [l2_eq, l2_eq]
  have h := abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
    (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))
  have he : inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
      (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) = x ⬝ᵥ v := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [he] at h
  exact h

lemma dot_mulVec_symm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : Mᵀ = M) (u v : Fin d → ℝ) :
    u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
  rw [dotProduct_mulVec, ← hM, vecMul_transpose, hM, dotProduct_comm]

lemma cs_form {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : Mᵀ = M)
    (hpsd : ∀ y, 0 ≤ y ⬝ᵥ (M *ᵥ y)) (x v : Fin d → ℝ) :
    |x ⬝ᵥ (M *ᵥ v)| ≤ Real.sqrt (x ⬝ᵥ (M *ᵥ x)) * Real.sqrt (v ⬝ᵥ (M *ᵥ v)) := by
  have hq : ∀ s : ℝ, 0 ≤ (v ⬝ᵥ (M *ᵥ v)) * (s * s) + (2 * (x ⬝ᵥ (M *ᵥ v))) * s +
      x ⬝ᵥ (M *ᵥ x) := by
    intro s
    have h := hpsd (x + s • v)
    rw [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul,
      dot_mulVec_symm M hM v x] at h
    simp only [smul_eq_mul] at h
    linarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  rw [← Real.sqrt_mul (hpsd x), ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith

lemma gram_inv_symm {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) :
    ((gram lam X W)⁻¹)ᵀ = (gram lam X W)⁻¹ := by
  rw [transpose_nonsing_inv, gram_transpose]

lemma gram_inv_psd {d : ℕ} (lam : ℝ) (hlam : 0 < lam) (X : ℕ → Fin d → ℝ) (W : Finset ℕ)
    (y : Fin d → ℝ) : 0 ≤ y ⬝ᵥ ((gram lam X W)⁻¹ *ᵥ y) := by
  set u := (gram lam X W)⁻¹ *ᵥ y
  have hy : y = gram lam X W *ᵥ u := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (gram_isUnit lam hlam X W)),
      one_mulVec]
  rw [hy, dotProduct_comm, gram_quad]
  have hs : 0 ≤ ∑ s ∈ W, (X s ⬝ᵥ u) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdd : 0 ≤ u ⬝ᵥ u := by
    rw [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  positivity

lemma decomp {d : ℕ} (lam : ℝ) (hlam : 0 < lam) (X : ℕ → Fin d → ℝ) (θ : ℕ → Fin d → ℝ)
    (e : ℕ → ℝ) (W : Finset ℕ) (θt : Fin d → ℝ) :
    est lam X (fun s => X s ⬝ᵥ θ s + e s) W - θt =
      (gram lam X W)⁻¹ *ᵥ (∑ s ∈ W, (X s ⬝ᵥ (θ s - θt)) • X s) +
        (gram lam X W)⁻¹ *ᵥ ((∑ s ∈ W, e s • X s) - lam • θt) := by
  have hθ : θt = (gram lam X W)⁻¹ *ᵥ (gram lam X W *ᵥ θt) := by
    rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (gram_isUnit lam hlam X W)),
      one_mulVec]
  unfold est
  conv_lhs => rw [hθ]
  rw [← mulVec_sub, ← mulVec_add, gram_mulVec]
  congr 1
  simp only [add_smul, Finset.sum_add_distrib, dotProduct_sub, sub_smul, Finset.sum_sub_distrib]
  abel

end BOBThm2Aux

open BOBThm2Aux in
theorem solution {d : ℕ} (hd : 2 ≤ d) (I : Instance d) (R L S lam : ℝ) (hR : 0 < R)
    (hL : 0 < L) (hS : 0 < S) (hlam : 0 < lam) (hst : I.Standing L S) (hA : Assumption1 I)
    (w : ℕ) (hw : 1 ≤ w)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : ℕ → Ω → ℝ) (hη : IsSubGNoise P η R)
    (X : ℕ → Ω → (Fin d → ℝ)) (hXD : ∀ s ∈ Finset.Icc 1 I.T, ∀ ω, X s ω ∈ I.D s)
    (hX : IsPredictable η X) (t : ℕ) (ht : t ∈ Finset.Icc 1 I.T) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    P {ω | ∃ x ∈ I.D t,
        L * ∑ s ∈ win 1 w t, l2 (I.θ s - I.θ (s + 1)) +
            beta R L S lam d w δ * wnorm (gram lam (fun s => X s ω) (win 1 w t)) x <
          |x ⬝ᵥ (est lam (fun s => X s ω) (fun s => X s ω ⬝ᵥ I.θ s + η s ω) (win 1 w t) -
            I.θ t)|} ≤ ENNReal.ofReal δ := by
  have h4 := lemma_4 hd I R L S lam hR hL hS hlam hst w hw P η hη X hXD hX t ht δ hδ0 hδ1
  refine le_trans (measure_mono ?_) h4
  intro ω hω
  obtain ⟨x, hx, hlt⟩ := hω
  simp only [Set.mem_setOf_eq]
  by_contra hle
  push Not at hle
  have hdec := decomp lam hlam (fun s => X s ω) I.θ (fun s => η s ω) (win 1 w t) (I.θ t)
  rw [hdec, dotProduct_add] at hlt
  have hXω : ∀ s ∈ Finset.Icc 1 I.T, X s ω ∈ I.D s := fun s hs => hXD s hs ω
  have h3 := lemma_3 I hA lam hlam w hw (fun s => X s ω) hXω t ht
  have hxL : l2 x ≤ L := ((hst t ht).2.1 x hx).1
  have hA1 := (dot_le_l2 x _).trans (mul_le_mul hxL h3 (Real.sqrt_nonneg _) hL.le)
  have hA2 := cs_form _ (gram_inv_symm lam (fun s => X s ω) (win 1 w t))
    (gram_inv_psd lam hlam (fun s => X s ω) (win 1 w t)) x
    ((∑ s ∈ win 1 w t, η s ω • X s ω) - lam • I.θ t)
  have hwx : 0 ≤ wnorm (gram lam (fun s => X s ω) (win 1 w t)) x := Real.sqrt_nonneg _
  have hA3 : wnorm (gram lam (fun s => X s ω) (win 1 w t)) x *
      wnorm (gram lam (fun s => X s ω) (win 1 w t))
        ((∑ s ∈ win 1 w t, η s ω • X s ω) - lam • I.θ t) ≤
      wnorm (gram lam (fun s => X s ω) (win 1 w t)) x * beta R L S lam d w δ :=
    mul_le_mul_of_nonneg_left hle hwx
  unfold wnorm at hA3 hlt
  have habs := abs_add_le
    (x ⬝ᵥ ((gram lam (fun s => X s ω) (win 1 w t))⁻¹ *ᵥ
      ∑ s ∈ win 1 w t, (X s ω ⬝ᵥ (I.θ s - I.θ t)) • X s ω))
    (x ⬝ᵥ ((gram lam (fun s => X s ω) (win 1 w t))⁻¹ *ᵥ
      ((∑ s ∈ win 1 w t, η s ω • X s ω) - lam • I.θ t)))
  nlinarith
