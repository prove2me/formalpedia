-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hsG_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:32:18.999104+00:00
-- url     : https://prove2.me/submissions/1f201bf5-95e8-4b42-9c13-091345f42826

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
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
open scoped Matrix.Norms.Frobenius
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) : hsG Y = ‖Y‖ := by
  rw [Matrix.frobenius_norm_def, hsG, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
end Formalism.HermitianLatticeCounting.P
