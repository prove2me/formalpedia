-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.typedModel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:39.652373+00:00
-- url     : https://prove2.me/submissions/0ccd79d8-3df4-4c9f-a551-207fc68c0e51

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_localisation_scaled_ideal_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (h1 : LocTw) (h2 : LocTyped) : TypedModel := by
  intro E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ t
  have hgK : (g : K) ≠ 0 := by
    have : σ (g : E) ≠ 0 := by
      rw [Ne, map_eq_zero]; exact_mod_cast hg.ne'
    simpa using this
  unfold perLat
  rw [h1 E _ _ s P hP t, h2 E g 1 ν hg hpd P hP hgP, h2 E g 2 ν hg hpd P hP hgP,
    localisation_scaled_ideal_mem_iff E g 1 hg, localisation_scaled_ideal_mem_iff E g 2 hg, hσ, hσ]
  simp only [map_div₀, map_sub, map_mul, map_pow, map_neg, map_one, map_zpow₀, map_natCast,
    complexConj_apply_apply, zpow_one]
  have e2 : ((g : K) ^ (2 : ℤ)) = (g : K) * g := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]; ring
  rw [e2]
  unfold Formalism.FourierDecayAlt.I.orderR
  simp only [Set.mem_ofPred_eq]
  set a := σ t / (g : K) with ha
  set b := σ (complexConj E t) / (g : K) with hb
  rcases neg_one_pow_eq_or K s with h | h <;> rw [h]
  · constructor
    · rintro ⟨⟨x1, x2⟩, x3, _⟩
      refine ⟨x1, by simpa [one_mul] using x2, _, x3, ?_⟩
      rw [ha]; field_simp
    · rintro ⟨x1, x2, u, hu, hh⟩
      have x2' : b ∈ o := by simpa [one_mul] using x2
      have e : (σ t - 1 * σ (complexConj E t)) / ((g : K) * g) = u := by
        rw [ha] at hh; field_simp at hh ⊢; linear_combination hh
      have e' : (σ (complexConj E t) - 1 * σ t) / ((g : K) * g) = -u := by
        rw [ha] at hh; field_simp at hh ⊢; linear_combination -hh
      exact ⟨⟨x1, x2'⟩, e ▸ hu, e' ▸ o.neg_mem hu⟩
  · constructor
    · rintro ⟨⟨x1, x2⟩, x3, _⟩
      refine ⟨x1, ?_, _, x3, ?_⟩
      · have : -1 * σ (complexConj E t) / (g : K) = -b := by rw [hb]; ring
        rw [this]; exact o.neg_mem x2
      · rw [ha]; field_simp
    · rintro ⟨x1, x2, u, hu, hh⟩
      have x2' : b ∈ o := by
        have : b = -(-1 * σ (complexConj E t) / (g : K)) := by rw [hb]; ring
        rw [this]; exact o.neg_mem x2
      have e : (σ t - -1 * σ (complexConj E t)) / ((g : K) * g) = u := by
        rw [ha] at hh; field_simp at hh ⊢; linear_combination hh
      have e' : (σ (complexConj E t) - -1 * σ t) / ((g : K) * g) = u := by
        rw [ha] at hh; field_simp at hh ⊢; linear_combination hh
      exact ⟨⟨x1, x2'⟩, e ▸ hu, e' ▸ hu⟩
end Formalism.FourierDecayAlt.P.S6x2
