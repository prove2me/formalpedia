-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.relevant_trivial_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:09.75011+00:00
-- url     : https://prove2.me/submissions/47dac936-5b4f-451d-828e-4390b1e7afa3

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.RelevantTriv := by
  intro m w d c hd hc a b hab hw
  have key : ∀ κ : ℂ, (∀ x : ℂ, C2.psiC c (κ * x) = 1) ↔ κ = 0 := by
    intro κ
    constructor
    · intro h
      by_contra hκ
      have h1 := h (1 / (c * κ))
      have hcx : c * (κ * (1 / (c * κ))) = 1 := by field_simp
      simp only [C2.psiC, hcx, Complex.one_re, Complex.ofReal_one, mul_one] at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hre : (1 : ℝ) = n * (2 * Real.pi) := by
        have := congrArg Complex.im hn
        simp at this
        linarith
      have hpi := Real.pi_gt_three
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn0
        nlinarith
      · subst hn0
        simp at hre
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
        nlinarith
    · rintro rfl x
      simp [C2.psiC]
  have hA : ∀ x : ℂ, ((if b.val = a.val + 1 then x else 0) -
      (if (w a).val = (w b).val + 1 then x * d a / d b else 0)) =
      ((if b.val = a.val + 1 then (1 : ℂ) else 0) - (if (w a).val = (w b).val + 1 then d a / d b else 0)) * x := by
    intro x
    split_ifs <;> ring
  simp only [hA, key]
  have hda := hd a
  have hdb := hd b
  by_cases hP : b.val = a.val + 1 <;> by_cases hQ : (w a).val = (w b).val + 1
  · simp only [hP, hQ, if_true, iff_self, true_and, forall_const]
    rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hdb]
  all_goals simp [hP, hQ, hda, hdb]
end Formalism.FourierDecayAlt.P
