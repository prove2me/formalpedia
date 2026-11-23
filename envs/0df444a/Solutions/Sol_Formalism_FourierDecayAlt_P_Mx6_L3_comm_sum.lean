-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L3.comm_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:23.469903+00:00
-- url     : https://prove2.me/submissions/ed78cbcf-f35e-4fa9-959d-10f5d0e2f29a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_comm_term

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
theorem _root_.solution (f : Ty P → ℂ) (f' : ℕ → Ty P → ℂ) (c u v : ℂ)
    (hs : ∀ j ∈ Icc 1 (P.k - 1), ∀ π π', Up P j π π' → f' j π' = f π)
    (hf : ∀ j ∈ Icc 1 (P.k - 1), ∀ π,
      (u - v) * ((f π - f' j π) * rr P j v π) = c * (f π * (rr P j u π - rr P j v π))) :
    (u - v) • (kap P f * abelian₂ P v - abelian₂ P v * kap P f) = c • (kap P f * (abelian₂ P u - abelian₂ P v)) := by
  unfold abelian₂
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j hj => comm_term P j f (f' j) (hs j hj) c u v (hf j hj)
end Formalism.FourierDecayAlt.P.Mx6.L3
