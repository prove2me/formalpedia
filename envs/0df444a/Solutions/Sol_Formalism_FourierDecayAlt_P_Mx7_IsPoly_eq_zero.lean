-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.IsPoly.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:37.76551+00:00
-- url     : https://prove2.me/submissions/46268471-cada-43ba-b001-010848fc6944

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_ev_eq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
variable {B : Type} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx7
namespace IsPoly
theorem _root_.solution {F : ℂ → B} (hF : IsPoly F) {S : Set ℂ} (hS : S.Finite) (h : ∀ Y, Y ∉ S → F Y = 0)
    (Y : ℂ) : F Y = 0 := by
  obtain ⟨p, hp⟩ := hF
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hev : ∀ Z, φ (F Z) = (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]).eval Z := by
    intro Z
    rw [hp, ev_eq_sum, map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, eval_monomial, smul_eq_mul, mul_comm]
  have h0 : (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]) = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine hS.infinite_compl.mono ?_
    intro Z hZ
    show eval Z _ = 0
    rw [← hev, h Z hZ, map_zero]
  rw [hev, h0, eval_zero]
end IsPoly
end Formalism.FourierDecayAlt.P.Mx7
