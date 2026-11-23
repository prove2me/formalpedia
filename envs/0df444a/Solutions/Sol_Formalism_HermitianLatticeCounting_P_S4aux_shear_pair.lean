-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.shear_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:17.821012+00:00
-- url     : https://prove2.me/submissions/efd132f2-3754-4635-ae2a-d7411bc8ca19

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_shear_apply
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
theorem _root_.solution (t : Fin r → V) (ht : ∀ j i, h (t j) (e i) = 0) (v : V) (i : Fin r) :
    h (shear h e t v) (e i) = h v (e i) := by
  simp [shear_apply, map_sum, LinearMap.sum_apply, ht]
end Formalism.HermitianLatticeCounting.P.S4aux
