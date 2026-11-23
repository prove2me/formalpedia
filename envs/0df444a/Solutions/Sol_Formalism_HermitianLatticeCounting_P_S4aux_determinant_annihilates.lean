-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.determinant_annihilates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:21.549955+00:00
-- url     : https://prove2.me/submissions/2cc70b1d-3b92-462e-83f8-7961e04af05f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_adj_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_gram_pair
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
theorem _root_.solution : DetKills := by
  intro E _ _ V _ _ h O m f c hG hp i
  set G : Matrix (Fin m) (Fin m) E := Matrix.of fun a b => h (f a) (f b) with hGd
  have hadj := adj_mem O m G hG
  have h1 : Matrix.vecMul (Matrix.vecMul c G) G.adjugate = G.det • c := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
  have h2 := congrFun h1 i
  rw [Pi.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  simp only [Matrix.vecMul, dotProduct]
  refine O.sum_mem fun j _ => O.mul_mem ?_ (hadj j i)
  have := hp j
  rw [gram_pair] at this
  exact this
end Formalism.HermitianLatticeCounting.P.S4aux
