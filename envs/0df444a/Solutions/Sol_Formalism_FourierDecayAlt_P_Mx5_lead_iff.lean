-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.lead_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:28.173549+00:00
-- url     : https://prove2.me/submissions/aafc2c01-a5a8-469c-98b2-75e639af4a45

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_mon_eval

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
variable {R : Type*} [Ring R] [Algebra ℂ R]
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (n : ℕ) (c : R) (f : ℂ → R) : Lead n c f ↔
    ∃ p : R[X], p.natDegree ≤ n ∧ p.coeff n = c ∧ ∀ Y, f Y = p.eval (algebraMap ℂ R Y) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨monomial n c + ∑ i ∈ range n, monomial i (a i), ?_, ?_, fun Y => ?_⟩
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le (Polynomial.natDegree_monomial_le _) ?_)
      exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
        (Polynomial.natDegree_monomial_le _).trans (Finset.mem_range.1 hi).le
    · rw [Polynomial.coeff_add, Polynomial.coeff_monomial, if_pos rfl, Polynomial.finset_sum_coeff,
        Finset.sum_eq_zero fun i hi => ?_, add_zero]
      rw [Polynomial.coeff_monomial, if_neg (Finset.mem_range.1 hi).ne]
    · rw [ha, Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.eval_finset_sum, mon_eval]
      simp only [Polynomial.eval_monomial, mon_eval]
  · rintro ⟨p, hp1, hp2, hp3⟩
    refine ⟨fun i => p.coeff i, fun Y => ?_⟩
    rw [hp3, Polynomial.eval_eq_sum_range' (show p.natDegree < n + 1 by omega), Finset.sum_range_succ, hp2,
      mon_eval, add_comm]
    simp only [mon_eval]
end Formalism.FourierDecayAlt.P.Mx5
