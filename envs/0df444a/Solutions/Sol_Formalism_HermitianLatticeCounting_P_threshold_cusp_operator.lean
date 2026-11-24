-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.threshold_cusp_operator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:01.05991+00:00
-- url     : https://prove2.me/submissions/ecb69185-f473-4a88-8345-a406d39947cc

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_rpow_three_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ThreshCuspOp := by
  intro n q h hq
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  rw [rpow_three_half _ (by linarith)]
  set s := Real.sqrt (q:ℝ) with hs'
  have s1 : 1 ≤ s := by rw [hs']; exact Real.one_le_sqrt.mpr hq'
  have s0 : 0 < s := by linarith
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ s0]
    constructor <;> intro hx <;> nlinarith
  · intro hqn hh
    have hqn' : (q:ℝ) ≤ n := by exact_mod_cast hqn
    have hn0 : (0:ℝ) < n := by linarith
    have a3 : 0 < (n:ℝ) ^ 2 * s := by positivity
    have a1 : (n:ℝ) * q * s ≤ (n:ℝ) ^ 2 * s := by
      have : (n:ℝ) * s * q ≤ (n:ℝ) * s * n := by gcongr
      nlinarith
    refine ⟨?_, by nlinarith⟩
    rw [lt_div_iff₀ s0]
    nlinarith
end Formalism.HermitianLatticeCounting.P
