-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.minor_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:56.963808+00:00
-- url     : https://prove2.me/submissions/f07ba85d-eb8e-4467-806d-bc214a1bb0c7

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_sum_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_det_sub_mem
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution {n m : ℕ} (hmn : m < n) (x w y : Matrix (Fin n) (Fin n) K)
    (H : Matrix (Fin m) (Fin m) K) (t : K) (hx : IsLowUni x) (hy : IsUpUni y)
    (hw1 : ∀ (a b : Fin n) (ha : a.val < m),
      w a b = if hb : b.val < m then H ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0)
    (hw2 : ∀ a b : Fin n, a.val = m → w a b = if b.val + 1 = n then t else 0)
    (hI : IsInt R (x * w * y)) : H.det * t ∈ R := by
  obtain ⟨hxT, hxD⟩ := hx
  obtain ⟨hyT, hyD⟩ := hy
  have hn1 : n - 1 < n := by omega
  let r : Fin (m + 1) → Fin n := fun i => ⟨i.val, lt_of_le_of_lt (Nat.lt_succ_iff.mp i.isLt) hmn⟩
  let c : Fin (m + 1) → Fin n := fun j =>
    if hj : j.val < m then ⟨j.val, lt_trans hj hmn⟩ else ⟨n - 1, hn1⟩
  let e : Fin m → Fin n := fun k => ⟨k.val, lt_trans k.isLt hmn⟩
  have hr : Function.Injective r := fun a b hab => by
    have h0 := congrArg Fin.val hab
    exact Fin.ext h0
  have he : Function.Injective e := fun a b hab => by
    have h0 := congrArg Fin.val hab
    exact Fin.ext h0
  have hmem := det_sub_mem R hI r c
  suffices hdet : ((x * w * y).submatrix r c).det = H.det * t by
    rw [← hdet]
    exact hmem

  have hsplit : (x * w * y).submatrix r c = x.submatrix r r * (w * y).submatrix r c := by
    rw [Matrix.mul_assoc]
    ext i j
    show ∑ k, x (r i) k * (w * y) k (c j) = ∑ k, x (r i) (r k) * (w * y) (r k) (c j)
    refine sum_sub r hr (fun k => x (r i) k * (w * y) k (c j)) (fun k hk => ?_)
    have hkm : m < k.val := by
      by_contra hc
      push_neg at hc
      exact hk (Set.mem_range.2 ⟨⟨k.val, Nat.lt_succ_of_le hc⟩, Fin.ext rfl⟩)
    have hlt : r i < k := by
      show i.val < k.val
      have := i.isLt
      omega
    show x (r i) k * (w * y) k (c j) = 0
    rw [hxT hlt, zero_mul]
  have hX : (x.submatrix r r).det = 1 := by
    have hlow : (x.submatrix r r).BlockTriangular OrderDual.toDual := by
      intro i j hij
      exact hxT (show r i < r j from hij)
    rw [Matrix.det_of_lowerTriangular (h := hlow)]
    exact Finset.prod_eq_one (fun i _ => hxD (r i))

  have hrowsum : ∀ j : Fin (m + 1),
      ((w * y).submatrix r c) (Fin.last m) j = t * y ⟨n - 1, hn1⟩ (c j) := by
    intro j
    show ∑ k, w (r (Fin.last m)) k * y k (c j) = t * y ⟨n - 1, hn1⟩ (c j)
    rw [Finset.sum_eq_single ⟨n - 1, hn1⟩]
    · rw [hw2 (r (Fin.last m)) ⟨n - 1, hn1⟩ rfl]
      split_ifs with hc
      · rfl
      · exact absurd (Nat.sub_add_cancel (by omega : 1 ≤ n)) hc
    · intro k _ hk
      rw [hw2 (r (Fin.last m)) k rfl]
      split_ifs with hc
      · exact absurd (Fin.ext (show k.val = n - 1 by omega)) hk
      · rw [zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  have hcl : c (Fin.last m) = ⟨n - 1, hn1⟩ := by simp [c]
  have hB : ((w * y).submatrix r c).det =
      t * (((w * y).submatrix r c).submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
    have hz : ∀ j : Fin m, ((w * y).submatrix r c) (Fin.last m) (Fin.castSucc j) = 0 := by
      intro j
      rw [hrowsum]
      have hcj : c (Fin.castSucc j) = e j := by simp [c, e, j.isLt]
      rw [hcj, hyT (show e j < ⟨n - 1, hn1⟩ from Fin.mk_lt_mk.2 (by have := j.isLt; omega)),
        mul_zero]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [hrowsum (Fin.last m), hcl, hyD, mul_one, Fin.succAbove_last, Fin.val_last, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_mul]

  have hTL : ((w * y).submatrix r c).submatrix Fin.castSucc Fin.castSucc = H * y.submatrix e e := by
    ext i j
    have hcj : c (Fin.castSucc j) = e j := by simp [c, e, j.isLt]
    have hri : r (Fin.castSucc i) = e i := rfl
    show ∑ k, w (r (Fin.castSucc i)) k * y k (c (Fin.castSucc j)) = ∑ k, H i k * y (e k) (e j)
    rw [hcj, hri]
    have hrow : ∀ k, w (e i) k = if hk : k.val < m then H i ⟨k.val, hk⟩ else 0 :=
      fun k => hw1 (e i) k i.isLt
    rw [show (∑ k, w (e i) k * y k (e j)) = ∑ k, w (e i) (e k) * y (e k) (e j) from
      sum_sub e he (fun k => w (e i) k * y k (e j)) (fun k hk => by
        have hkm : ¬ k.val < m := fun hc => hk (Set.mem_range.2 ⟨⟨k.val, hc⟩, Fin.ext rfl⟩)
        show w (e i) k * y k (e j) = 0
        rw [hrow, dif_neg hkm, zero_mul])]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hrow]
    split_ifs with hk
    · rfl
    · exact absurd k.isLt hk
  have hYt : (y.submatrix e e).det = 1 := by
    have hup : (y.submatrix e e).BlockTriangular id := by
      intro i j hij
      exact hyT (show e j < e i from hij)
    rw [Matrix.det_of_upperTriangular (h := hup)]
    exact Finset.prod_eq_one (fun i _ => hyD (e i))
  rw [hsplit, Matrix.det_mul, hX, one_mul, hB, hTL, Matrix.det_mul, hYt, mul_one, mul_comm]
end Formalism.FourierDecayAlt.P.A5x7
