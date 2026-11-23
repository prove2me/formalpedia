-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L3.comm_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:24.019695+00:00
-- url     : https://prove2.me/submissions/2c5b2c3e-3527-406d-bede-2b564e3958eb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_S_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L3
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.L3
theorem _root_.solution (j : ℕ) (f f' : Ty P → ℂ) (hs : ∀ π π', Up P j π π' → f' π' = f π) (c u v : ℂ)
    (hf : ∀ π, (u - v) * ((f π - f' π) * rr P j v π) = c * (f π * (rr P j u π - rr P j v π))) :
    (u - v) • (kap P f * lam P j v - lam P j v * kap P f) = c • (kap P f * (lam P j u - lam P j v)) := by
  unfold lam
  have e1 : kap P f * (kap P (rr P j v) * SS P j) = kap P (f * rr P j v) * SS P j := by
    rw [← mul_assoc, kap_mul]
  have e2 : (kap P (rr P j v) * SS P j) * kap P f = kap P (rr P j v * f') * SS P j := by
    rw [mul_assoc, ← S_shift P j f f' hs, ← mul_assoc, kap_mul]
  have e3 : kap P f * (kap P (rr P j u) * SS P j - kap P (rr P j v) * SS P j) =
      kap P (f * (rr P j u - rr P j v)) * SS P j := by
    rw [← sub_mul, ← map_sub, ← mul_assoc, kap_mul]
  rw [e1, e2, e3, ← sub_mul, ← map_sub, ← smul_mul_assoc, ← smul_mul_assoc, ← map_smul, ← map_smul]
  congr 2
  funext π
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  linear_combination hf π
end Formalism.FourierDecayAlt.P.Mx6.L3
