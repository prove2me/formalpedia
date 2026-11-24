-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BorderedDeterminants.subRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:30.967801+00:00
-- url     : https://prove2.me/submissions/e9ccdfed-08f4-43c2-9edf-f7a3ac8bc9cd

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BorderedDeterminants
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.BorderedDeterminants
theorem _root_.solution : SubRel := by
  intro A _ n E hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold GlRel
    intro a b c d
    simpa [subA, Fin.castSucc_inj] using hE a.castSucc b.castSucc c.castSucc d.castSucc
  · unfold IsCov
    intro a b c
    have h := hE a.castSucc b.castSucc c.castSucc (Fin.last n)
    rw [if_neg (Fin.castSucc_lt_last a).ne', sub_zero] at h
    simp only [subA, etaK]
    rw [h]
    by_cases hbc : b = c
    · subst hbc; simp
    · rw [if_neg (fun e => hbc (Fin.castSucc_injective _ e)), if_neg hbc]
  · unfold IsVec
    intro a b c
    have h := hE a.castSucc b.castSucc (Fin.last n) c.castSucc
    rw [if_neg (Fin.castSucc_lt_last b).ne, zero_sub] at h
    simp only [subA, yK]
    rw [h]
    by_cases hac : a = c
    · subst hac; simp
    · rw [if_neg (fun e => hac (Fin.castSucc_injective _ e).symm), if_neg hac, neg_zero]
  · intro a b
    have h := hE a.castSucc (Fin.last n) b.castSucc (Fin.last n)
    rw [if_neg (Fin.castSucc_lt_last b).ne', if_neg (Fin.castSucc_lt_last a).ne', sub_zero] at h
    exact sub_eq_zero.mp h
  · intro a b
    have h := hE (Fin.last n) a.castSucc (Fin.last n) b.castSucc
    rw [if_neg (Fin.castSucc_lt_last a).ne, if_neg (Fin.castSucc_lt_last b).ne, sub_zero] at h
    exact sub_eq_zero.mp h
  · intro a b
    have h := hE (Fin.last n) (Fin.last n) a.castSucc b.castSucc
    rw [if_neg (Fin.castSucc_lt_last a).ne', if_neg (Fin.castSucc_lt_last b).ne, sub_zero] at h
    exact sub_eq_zero.mp h
end Formalism.FourierDecayAlt.P.BorderedDeterminants
