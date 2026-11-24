-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_minor_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:09.110183+00:00
-- url     : https://prove2.me/submissions/c8c2a6c1-a820-4639-80ee-508802913da7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_det_col
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_CC
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_shiftGen
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_shiftGen_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_minorAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {K σ κ : Type} [Field K] [DecidableEq σ] [Fintype κ]
variable {r0 r1 l : ℕ} (s : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) (pos : κ → σ)
  (ξ : κ → Fin r0 → K) (col : κ → Fin r1)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hI : Function.Injective I) (S : Finset κ) (J : Finset (Fin r1))
    (hS : ∀ k ∈ S, pos k = s → col k ∈ J) :
    degLE S ((univ.image I) ∩ J).card
      (shiftPoly (fun k => colDir (pos k) (ξ k) (col k)) (minorAt s T I)) := by
  classical
  rw [shiftPoly_minorAt]
  have hcard : ((univ.image I) ∩ J).card = ∑ c : Fin l, if I c ∈ J then 1 else 0 := by
    rw [← Finset.card_filter, ← Finset.card_image_of_injective _ hI]
    congr 1
    ext y
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨⟨c, rfl⟩, hc⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, rfl⟩, hc⟩
  rw [hcard]
  refine degLE_det_col _ _ fun i c => ?_
  simp only [Matrix.of_apply]
  refine degLE_sum _ _ fun a _ => ?_
  by_cases hc : I c ∈ J
  · rw [if_pos hc]
    simpa using degLE_mul (degLE_CC S (T i a)) (degLE_shiftGen S _ (s, a, I c))
  · rw [if_neg hc]
    have := degLE_mul (degLE_CC S (T i a)) (degLE_shiftGen_zero S
      (fun k => colDir (pos k) (ξ k) (col k)) (s, a, I c) fun k hk => by
        unfold colDir
        rw [if_neg]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        exact hc (h2 ▸ hS k hk h1.symm))
    simpa using this
end Formalism.InvariantFactorPaths.G7
