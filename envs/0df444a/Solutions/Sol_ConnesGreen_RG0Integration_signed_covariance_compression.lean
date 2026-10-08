-- Prove2me | solution 1 for ConnesGreen.RG0Integration.signed_covariance_compression
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:39:18.297826+00:00
-- url     : https://prove2.me/submissions/d4a369d1-3481-48df-b643-3312202a8262

import Definitions.Def_ConnesGreen_RG0_original_actors
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section


theorem solution (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hsource : ∀ ρ : CriticalZeros,
      U.toContinuousLinearMap.adjoint (sourceEmbed T (actualGreenSource ρ)) =
        sourceEmbed t (actualGreenSource ρ)) :
    U.toContinuousLinearMap.adjoint ∘L
      (canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
        (canonicalSelectedSynthesis T hT S).adjoint) ∘L U.toContinuousLinearMap =
      canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L
        (canonicalSelectedSynthesis t ht S).adjoint := by
  have hp : U.toContinuousLinearMap.adjoint ∘L canonicalPositiveSynthesis T hT =
      canonicalPositiveSynthesis t ht := by
    apply canonicalPositiveSynthesis_unique t ht
    intro ρ
    simp only [ContinuousLinearMap.comp_apply, canonicalPositiveSynthesis_single]
    simp [positiveGreenColumn, weightedGreenColumn, hsource] <;> rfl
  have hm : U.toContinuousLinearMap.adjoint ∘L canonicalSelectedSynthesis T hT S =
      canonicalSelectedSynthesis t ht S := by
    apply canonicalSelectedSynthesis_unique t ht S
    intro ρ
    simp only [ContinuousLinearMap.comp_apply, canonicalSelectedSynthesis_single]
    simp [negativeGreenColumn, weightedGreenColumn, hsource] <;> rfl
  have hp' := congrArg (fun P => P ∘L P.adjoint) hp
  have hm' := congrArg (fun M => M ∘L M.adjoint) hm
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc] at hp' hm'
  unfold canonicalPositiveCovariance
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_assoc]
  rw [hp', hm']
