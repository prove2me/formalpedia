-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.det_eq_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:29.660909+00:00
-- url     : https://prove2.me/submissions/35a8781d-401d-48b5-ae2d-86426c48da3e

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
theorem _root_.solution {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) (f g : V →ₗ[F] V) (hW : ∀ x ∈ W, g x ∈ W) (hfW : ∀ x ∈ W, f x = g x)
    (hfg : ∀ x, f x - g x ∈ W) : LinearMap.det f = LinearMap.det g := by
  have hg' : W ≤ W.comap g := fun x hx => hW x hx
  have hf' : W ≤ W.comap f := fun x hx => by
    rw [Submodule.mem_comap, hfW x hx]; exact hW x hx
  rw [LinearMap.det_eq_det_mul_det W f hf', LinearMap.det_eq_det_mul_det W g hg']
  congr 2
  · exact LinearMap.ext fun x => Subtype.ext (hfW x x.2)
  · apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact (Submodule.Quotient.eq W).2 (hfg x)
end Formalism.HermitianLatticeCounting.P.S4aux
