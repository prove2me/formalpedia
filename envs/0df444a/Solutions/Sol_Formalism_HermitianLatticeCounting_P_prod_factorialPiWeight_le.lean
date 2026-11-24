-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prod_factorialPiWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:16.59314+00:00
-- url     : https://prove2.me/submissions/766da477-ae25-4a09-94dd-c47537b7a40f

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_factorialPiWeight_pos
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_mul_factorialPiWeight
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_factorialPiWeight_le_pi_pow_mul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_seventeen_mul_factorialPiWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (v : ℝ) (hv : 1 ≤ v) (k s : ℕ) (hs : 2 ≤ s) (hk : s + 2 ≤ k) :
    ∏ j ∈ Finset.Ioc 2 s, s5bA v j ≤
      (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
        ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) *
        ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j := by
  have hv0 : 0 < v := by linarith
  have hW : ∀ j, 0 < s5bA v j := factorialPiWeight_pos v hv0
  obtain ⟨t, ht⟩ : ∃ t, t = k - s - 2 := ⟨_, rfl⟩
  rw [← ht]
  have h1 : ∏ j ∈ Finset.Ioc 2 s, s5bA v j ≤
      Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc 2 s, s5bA v (j + t) := by
    calc ∏ j ∈ Finset.Ioc 2 s, s5bA v j
          ≤ ∏ j ∈ Finset.Ioc 2 s, (Real.pi ^ t * s5bA v (j + t)) :=
          Finset.prod_le_prod (fun j _ => (hW j).le)
            (fun j _ => factorialPiWeight_le_pi_pow_mul v hv j t)
      _ = Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc 2 s, s5bA v (j + t) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ioc, ← pow_mul]
  have h2 : ∏ j ∈ Finset.Ioc 2 s, s5bA v (j + t) =
      ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j := by
    rw [show k - s = 2 + t by omega, show k - 2 = s + t by omega, ← Finset.map_add_right_Ioc,
      Finset.prod_map]
    rfl
  have h3 : ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j =
      (∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) * s5bA v (k - 1) *
        s5bA v k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega,
      show m + 2 = m + 1 + 1 by ring,
      Finset.prod_Ioc_succ_top (show m + 1 + 1 - s ≤ m + 1 by omega),
      Finset.prod_Ioc_succ_top (show m + 1 + 1 - s ≤ m by omega)]
  have hA := one_le_seventeen_mul_factorialPiWeight v hv k (by omega)
  have hB := one_le_mul_factorialPiWeight v hv k (by omega)
  have hP0 : 0 ≤ ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j :=
    Finset.prod_nonneg (fun j _ => (hW j).le)
  have hX0 : 0 ≤ Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j :=
    mul_nonneg (pow_nonneg Real.pi_pos.le _) hP0
  rw [h3]
  calc ∏ j ∈ Finset.Ioc 2 s, s5bA v j
        ≤ Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j := by
        rw [← h2]; exact h1
    _ = (Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) * 1 * 1 := by
        ring
    _ ≤ (Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) *
          (17 * s5bA v (k - 1)) *
          ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) * s5bA v k) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA hX0) hB zero_le_one
          (mul_nonneg hX0 (by linarith))
    _ = (Real.pi ^ ((s - 2) * t) * 17 *
          ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) *
          ((∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) * s5bA v (k - 1) *
            s5bA v k) := by ring
end Formalism.HermitianLatticeCounting.P
