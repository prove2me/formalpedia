-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.primitive_density_inert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:23.194803+00:00
-- url     : https://prove2.me/submissions/cc53ab89-a44c-4d25-962f-2783d98a2c6e

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_primitive_density_inert_form
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
theorem _root_.solution : PrimDensityInert := by
  intro K L _ _ _ _ _ h2 n m Gm hn hG
  have := primitive_density_inert_form K L h2 n m 1 Gm hn (by simp)
    (fun k l => by
      by_cases h : k = l
      · subst h; simp
      · simp [h, Ne.symm h, Fintype.card_pos.ne']) hG
  simpa [Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq] using this
end Formalism.HermitianLatticeCounting.P.S4aux
