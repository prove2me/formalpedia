-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.covering_radius_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:12.980445+00:00
-- url     : https://prove2.me/submissions/8dfe4123-10dd-4ab0-8632-74071b595edb

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_coverRadius_sq
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CoverRadius := by
  intro V _ _ _ M hMd hspan κ hκ hdual x
  obtain ⟨y, hy, hxy⟩ := coverRadius_sq V M hMd hspan κ hκ hdual x
  refine ⟨y, hy, hxy.trans ?_⟩
  have h23 : (Module.finrank ℝ V : ℝ) ^ 2 ≤ (Module.finrank ℝ V : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with h0 | hN
    · rw [h0]; simp
    · exact pow_le_pow_right₀ (by exact_mod_cast hN) (by norm_num)
  gcongr
end Formalism.HermitianLatticeCounting.P
