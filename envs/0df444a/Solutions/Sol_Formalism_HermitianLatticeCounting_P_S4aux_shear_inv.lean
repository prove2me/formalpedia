-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.shear_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:38.443502+00:00
-- url     : https://prove2.me/submissions/755ba838-03bd-422e-adc4-ebdcab3ca892

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_shear_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_shear_pair
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
variable {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  (h : V →ₗ[E] V →ₗ⋆[E] E) {r : ℕ} (e : Fin r → V)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (t : Fin r → V) (ht : ∀ j i, h (t j) (e i) = 0) (v : V) :
    shear h e (fun j => - t j) (shear h e t v) = v := by
  rw [shear_apply]
  simp only [shear_pair h e t ht]
  rw [shear_apply]
  simp
end Formalism.HermitianLatticeCounting.P.S4aux
