-- Prove2me | solution 1 for Bl.general_b_fact_ter.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:14.415415+00:00
-- url     : https://prove2.me/submissions/f584f6f6-9b0b-4261-9801-a8223d1a303e

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactTer_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_ter
namespace Bl.general_b_fact_ter
theorem _root_.solution :
  ∀ {r : Nat} {N N' B B' : Matrix.{0, 0, 0} (Fin r) (Fin r) Complex},
  (∀ (a c : Fin r), LT.lt.{0} a c → Eq.{1} (N a c) 0) →
    (∀ (a : Fin r), Eq.{1} (N a a) 1) →
      (∀ (a c : Fin r), LT.lt.{0} a c → Eq.{1} (N' a c) 0) →
        (∀ (a : Fin r), Eq.{1} (N' a a) 1) →
          (∀ (a c : Fin r), LT.lt.{0} c a → Eq.{1} (B a c) 0) →
            (∀ (a c : Fin r), LT.lt.{0} c a → Eq.{1} (B' a c) 0) →
              Ne.{1} (Matrix.det.{0, 0} B) 0 →
                Eq.{1} (HMul.hMul.{0, 0, 0} N B) (HMul.hMul.{0, 0, 0} N' B') → Eq.{1} N N'  := by
  intro r N N' B B' hN0 hN1 hN'0 hN'1 hB0 hB'0 hdet hEq
  have lN : N.BlockTriangular OrderDual.toDual := fun i j hij =>
    hN0 i j (OrderDual.toDual_lt_toDual.mp hij)
  have lN' : N'.BlockTriangular OrderDual.toDual := fun i j hij =>
    hN'0 i j (OrderDual.toDual_lt_toDual.mp hij)
  have uB : B.BlockTriangular id := fun i j hij => hB0 i j hij
  have uB' : B'.BlockTriangular id := fun i j hij => hB'0 i j hij
  have dN' : N'.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular N' lN']
    simp [hN'1]
  have uN' : IsUnit N'.det := by rw [dN']; exact isUnit_one
  have uBd : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have iN' : Invertible N' := Matrix.invertibleOfIsUnitDet N' uN'
  have iB : Invertible B := Matrix.invertibleOfIsUnitDet B uBd
  have hM2 : N'⁻¹ * N = B' * B⁻¹ := by
    calc N'⁻¹ * N = N'⁻¹ * N * B * B⁻¹ := by
          rw [Matrix.mul_assoc (N'⁻¹ * N), Matrix.mul_nonsing_inv B uBd, Matrix.mul_one]
      _ = N'⁻¹ * (N' * B') * B⁻¹ := by rw [Matrix.mul_assoc N'⁻¹ N B, hEq]
      _ = B' * B⁻¹ := by
          rw [← Matrix.mul_assoc N'⁻¹ N' B', Matrix.nonsing_inv_mul N' uN', Matrix.one_mul]
  obtain ⟨M, hM⟩ : ∃ M, M = N'⁻¹ * N := ⟨_, rfl⟩
  have lM : M.BlockTriangular OrderDual.toDual := by
    rw [hM]; exact (Matrix.blockTriangular_inv_of_blockTriangular lN').mul lN
  have uM : M.BlockTriangular id := by
    rw [hM, hM2]; exact uB'.mul (Matrix.blockTriangular_inv_of_blockTriangular uB)
  have hNM : N = N' * M := by
    rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' uN', Matrix.one_mul]
  have hoff : ∀ a c, a ≠ c → M a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact lM (OrderDual.toDual_lt_toDual.mpr h)
    · exact uM h
  have hdiag : ∀ a, M a a = 1 := by
    intro a
    have h := congrFun (congrFun hNM a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a (fun k _ hk => by rw [hoff k a hk, mul_zero])
      (fun h => absurd (Finset.mem_univ a) h), hN'1, one_mul, hN1] at h
    exact h.symm
  have hM1 : M = 1 := by
    ext a c
    by_cases h : a = c
    · subst h; rw [hdiag, Matrix.one_apply_eq]
    · rw [hoff a c h, Matrix.one_apply_ne h]
  rw [hNM, hM1, Matrix.mul_one]
end Bl.general_b_fact_ter
