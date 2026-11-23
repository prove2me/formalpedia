-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.off_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:28.206774+00:00
-- url     : https://prove2.me/submissions/166c922f-a542-44b5-9940-ba6e5261a5ae

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_ss
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_sss
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xEx_insert
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fac_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) {l j : ℕ}
    (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    (kap P fun π => xEx P {l} π Y) * star (SS P l) * ((kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j) =
      star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π Y := by
  have hjl' : j ∈ Icc 1 (P.k - 1) \ {l} := Finset.mem_sdiff.2 ⟨hj, by simpa using hjl⟩
  have e : (fun π => xEx P {l} π Y * (Y + (rho P π j : ℂ))⁻¹) = fun π => xEx P {l, j} π Y := by
    funext π
    rw [xEx_insert P {l} j hjl' π Y, Finset.pair_comm, mul_comm, ← mul_assoc,
      inv_mul_cancel₀ (fac_ne P (hx π) hj), one_mul]
  rw [(kap_sss P l _ fun π π' h => xEx_up P l {l} (Finset.mem_singleton_self l) Y π π' h).eq, mul_assoc,
    ← mul_assoc (kap P _), ← kap_mul, e,
    (kap_ss P j _ fun π π' h => xEx_up P j {l, j} (by simp) Y π π' h).eq, ← mul_assoc]
end Formalism.FourierDecayAlt.P.Mx5
