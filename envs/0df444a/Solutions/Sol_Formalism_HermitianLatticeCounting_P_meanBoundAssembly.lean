-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.meanBoundAssembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:32.216312+00:00
-- url     : https://prove2.me/submissions/eb15a909-0717-4b10-b43b-8d5053089e9d

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

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
theorem _root_.solution : MeanBoundAssembly := by
  intro k s de NT lf massk masss massks massFlagLatticeZero mean nM nS mM mS Gl hsk hk hde hNT hlf hmk hms hmks
    hmean hnM hnS hmM hmS hGl hP hmM' hmS' hnM' hnS' hGl' hL0
  have hde0 : 0 < de := by linarith
  have hNT0 : 0 < NT := by linarith
  have hX0 : 0 < de * NT := mul_pos hde0 hNT0
  have hM0 : 0 < massk * NT ^ (k - 1) := by positivity
  have h1 : mean ≤ nM * nS * mM * mS * Gl / (massk * NT ^ (k - 1)) := by
    rw [le_div_iff₀ hM0]
    calc mean * (massk * NT ^ (k - 1)) ≤ mean * massFlagLatticeZero := mul_le_mul_of_nonneg_left hL0 hmean
      _ ≤ _ := hP
  have h2 : nM * nS * mM * mS * Gl ≤ de ^ (1 + lf) * (de * NT) ^ (2 + lf) *
      (massks * de ^ (k - s) * de ^ (s + 1)) * (masss * (de * NT) ^ (2 * s)) *
      (de * NT) ^ (4 * (2 * s + 1)) := by
    gcongr
  have hde_le : de ^ (1 + lf) ≤ (de * NT) ^ (1 + lf) :=
    Real.rpow_le_rpow hde0.le (by nlinarith) (by linarith)
  have hsplit : (de * NT) ^ (((10 * s + 8 : ℕ) : ℝ) + 2 * lf) =
      (de * NT) ^ (1 + lf) * (de * NT) ^ (2 + lf) * (de * NT) ^ (10 * s + 5) := by
    rw [← Real.rpow_natCast (de * NT) (10 * s + 5), ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    congr 1; push_cast; try ring
  have e1 : de ^ (k - s) * de ^ (s + 1) = de ^ (k + 1) := by rw [← pow_add]; congr 1; omega
  have e2 : NT ^ k = NT ^ (k - 1) * NT := by rw [← pow_succ]; congr 1; omega
  have hpow : de ^ (k - s) * de ^ (s + 1) * (de * NT) ^ (2 * s) * (de * NT) ^ (4 * (2 * s + 1)) /
      NT ^ (k - 1) = (de / NT) ^ k * (de * NT) ^ (10 * s + 5) := by
    rw [e1, div_pow, e2, eq_comm, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  calc mean ≤ nM * nS * mM * mS * Gl / (massk * NT ^ (k - 1)) := h1
    _ ≤ (de ^ (1 + lf) * (de * NT) ^ (2 + lf) * (massks * de ^ (k - s) * de ^ (s + 1)) *
          (masss * (de * NT) ^ (2 * s)) * (de * NT) ^ (4 * (2 * s + 1))) /
          (massk * NT ^ (k - 1)) := div_le_div_of_nonneg_right h2 hM0.le
    _ = de ^ (1 + lf) * (de * NT) ^ (2 + lf) *
          (de ^ (k - s) * de ^ (s + 1) * (de * NT) ^ (2 * s) * (de * NT) ^ (4 * (2 * s + 1)) /
            NT ^ (k - 1)) * (masss * massks / massk) := by ring
    _ = de ^ (1 + lf) * (de * NT) ^ (2 + lf) * ((de / NT) ^ k * (de * NT) ^ (10 * s + 5)) *
          (masss * massks / massk) := by rw [hpow]
    _ ≤ (de * NT) ^ (1 + lf) * (de * NT) ^ (2 + lf) * ((de / NT) ^ k * (de * NT) ^ (10 * s + 5)) *
          (masss * massks / massk) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hde_le (by positivity)) (by positivity)) (by positivity)
    _ = (de / NT) ^ k * (de * NT) ^ (((10 * s + 8 : ℕ) : ℝ) + 2 * lf) * (masss * massks / massk) := by
        rw [hsplit]; ring
end Formalism.HermitianLatticeCounting.P
