-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.move_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:01:29.322586+00:00
-- url     : https://prove2.me/submissions/fee653fe-c7e3-43b2-b4d5-467a0c6f683b

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_Final_eichMove
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
theorem _root_.solution : MoveCong := by
  intro E _ _ V _ _ h O abelian₂ th x x' u s hH hth hL hI hu hs hb hxx h1 h2 v hv hvx
  obtain ⟨w, hw, he⟩ := hb
  obtain ⟨d2, hd2, hk2⟩ := hxx
  have e1 : h v x = h v (x + x') := by simp [hvx]
  have e2 : h v x = th * h v w := by rw [e1, he, LinearMap.map_smulₛₗ, starRingEnd_apply, hth]; rfl
  have mv := Formalism.SL.Final.eichMove E V h x x' u s hH h1 h2 v hvx
  refine ⟨e1, ⟨_, hI v hv w hw, e2⟩, ⟨h v w + h v u * d2, O.add_mem (hI v hv w hw) (O.mul_mem (hI v hv u hu) hd2), ?_⟩, ?_⟩
  · rw [e2, hk2]; ring
  · refine ⟨h v u • w - (h v w + h v u * d2) • (u + s • x), abelian₂.sub_mem (hL _ (hI v hv u hu) _ hw) (hL _ (O.add_mem (hI v hv w hw) (O.mul_mem (hI v hv u hu) hd2)) _ (abelian₂.add_mem hu hs)), ?_⟩
    rw [mv, he, e2, hk2]; module
end Formalism.HermitianLatticeCounting.P.S4aux
