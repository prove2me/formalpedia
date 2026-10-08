-- Prove2me | solution 1 for CompOT.W1.proposition_6_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T10:24:35.690865+00:00
-- url     : https://prove2.me/submissions/fa9b1d7f-eccb-486b-9877-ff7e905746f0

import Theorems.Thm_CompOT_W1_prop_6_1_lipschitz_of_cTransform
import Theorems.Thm_CompOT_W1_prop_6_1_cTransform_neg
import Theorems.Thm_CompOT_W1_prop_6_1_cTransform_self

open CompOT.W1

theorem solution {X : Type*} [MetricSpace X] (f : X → ℝ) :
    ((∃ g : X → ℝ, Continuous g ∧ ∀ y, (f y : EReal) = cTransform g y) ↔
        LipschitzWith 1 f) ∧
      (LipschitzWith 1 f → ∀ y, cTransform f y = ((-f y : ℝ) : EReal)) := by
  constructor
  · constructor
    · rintro ⟨g, _, hfg⟩
      exact prop_6_1_lipschitz_of_cTransform f g hfg
    · intro hf
      refine ⟨fun x => -f x, hf.continuous.neg, ?_⟩
      intro y
      exact (prop_6_1_cTransform_neg f hf y).symm
  · exact prop_6_1_cTransform_self f

#print axioms solution
