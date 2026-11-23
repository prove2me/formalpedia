-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.geo_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:11.191792+00:00
-- url     : https://prove2.me/submissions/b74eb0c2-0b69-4a83-81bd-14b1ee510e46

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (q : ℝ) (hq : 2 ≤ q) (j : ℕ) : ∑ i ∈ range (j + 1), q ^ i ≤ 2 * q ^ j - 1 := by
  induction j with
  | zero => simp; norm_num
  | succ j ih =>
    rw [Finset.sum_range_succ, pow_succ q j]
    have : 0 < q ^ j := by positivity
    nlinarith
end Formalism.HermitianLatticeCounting.P.S4aux
