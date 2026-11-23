-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.IsPoly.dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:38.552815+00:00
-- url     : https://prove2.me/submissions/574c0542-dcde-424e-8a0a-8112a18b9729

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_ev_apply

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.PC
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
noncomputable section
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6.PC
namespace IsPoly
theorem _root_.solution {f : ℂ → B} (hf : IsPoly f) (φ : Module.Dual ℂ B) : IsPolyS fun y => φ (f y) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨∑ n ∈ p.support, monomial n (φ (p.coeff n)), fun y => ?_⟩
  show φ (f y) = _
  rw [hp, ev_apply]
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def, RingHom.id_apply,
    map_sum, eval_finsetSum, eval_monomial]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
end IsPoly
end Formalism.FourierDecayAlt.P.Mx6.PC
