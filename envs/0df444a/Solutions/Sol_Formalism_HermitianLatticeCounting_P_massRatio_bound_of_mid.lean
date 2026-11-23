-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.massRatio_bound_of_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:09.31856+00:00
-- url     : https://prove2.me/submissions/4aa13aa7-3818-49d7-a49c-0d0305d0772a

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pow_eq_exp_mul_log
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_heightParameter_rpow

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
theorem _root_.solution (C : ℝ) (hC : 1 ≤ C) (k m f s : ℕ) (b v NT : ℝ) (Xi : ℕ → ℝ) (hb : 0 < b)
    (hXi : XiHyp C k m f b v NT Xi) (hs2 : 2 ≤ s) (hsk : s + 2 ≤ k) :
    0 ≤ Xi s ∧ ((k : ℝ) * v) ^ (k * f) * Xi s ≤
      Real.exp (C * (m:ℝ) ^ 2 * f * Real.log b * C + (s:ℝ) * k * f * Real.log C) := by
  unfold XiHyp at hXi
  obtain ⟨h0, h1⟩ := hXi.1 s hs2 hsk
  refine ⟨h0, h1.trans (le_of_eq ?_)⟩
  rw [heightParameter_rpow C m f b C hb, pow_eq_exp_mul_log C (by linarith) (s * k * f), ← Real.exp_add,
    Nat.cast_mul, Nat.cast_mul]
end Formalism.HermitianLatticeCounting.P
