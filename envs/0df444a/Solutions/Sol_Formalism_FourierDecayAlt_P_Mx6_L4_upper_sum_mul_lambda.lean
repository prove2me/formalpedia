-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L4.upper_sum_mul_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:11.662806+00:00
-- url     : https://prove2.me/submissions/a54048cb-5094-40d6-8822-fb59af9da81a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Mx6_L4_kap_sum__1aec61f2ed62
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_T_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_T_eq

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L4
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.L4
theorem _root_.solution (hP : P.OK) {u : ℂ} (hu : Good P u) (hN : SSNorm) :
    S12 P u * abelian₂ P u = S4 P u + kap P fun π => ∑ l ∈ Icc 1 (P.k - 1),
      ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
  have e1 : S12 P u * abelian₂ P u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      (kap P fun π => xEx P {l} π u) * star (SS P l) * (kap P (rr P j u) * SS P j) :=
    Finset.sum_mul_sum _ _ _ _
  have e2 : ∀ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      (kap P fun π => xEx P {l} π u) * star (SS P l) * (kap P (rr P j u) * SS P j) =
      (∑ j ∈ (Icc 1 (P.k - 1)).erase l, star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π u) +
        kap P fun π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
    intro l hl
    rw [← Finset.sum_erase_add _ _ hl, T_eq P hP hN u hl]
    refine congrArg (· + _) ?_
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_erase.1 hj
    exact T_ne P hu hj'.2 hj'.1
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib,
    kap_sum' P _ (fun l π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1))]
  rfl
end Formalism.FourierDecayAlt.P.Mx6.L4
