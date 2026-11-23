-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hj_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:12.66917+00:00
-- url     : https://prove2.me/submissions/2d9470fa-3156-40ce-93e8-281aebc196c2

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
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
omit [StarRing E]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (t nn : F)
    (hω2 : ω * ω = algebraMap F E t * ω - algebraMap F E nn) (a b : F) :
    Algebra.norm F (algebraMap F E a + algebraMap F E b * ω) = a ^ 2 + a * b * t + b ^ 2 * nn := by
  rw [Algebra.norm_eq_matrix_det β, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, h0, h1, mul_one]
  have e1 : (algebraMap F E a + algebraMap F E b * ω) * ω
      = algebraMap F E (-(b * nn)) + algebraMap F E (a + b * t) * ω := by
    simp only [map_neg, map_mul, map_add]
    linear_combination (algebraMap F E b) * hω2
  rw [e1, (hj_repr β ω h0 h1 _ _).1, (hj_repr β ω h0 h1 _ _).2, (hj_repr β ω h0 h1 _ _).1,
    (hj_repr β ω h0 h1 _ _).2]
  ring
end Formalism.HermitianLatticeCounting.P.S4aux
