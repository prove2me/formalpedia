-- Prove2me | solution 1 for Freiman.middle_initial_contacts_lower
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:48:43.551351+00:00
-- url     : https://prove2.me/submissions/54500a47-9626-44d7-a876-76021764db28

import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
open Freiman
set_option autoImplicit false
private lemma contact (a b : Fin 15) (ha : middleRootCertificate a)
    (hb : middleRootCertificate b)
    (h1 : middleInnerLeft a < middleInnerRight a)
    (h2 : middleInnerLeft b ≤ middleInnerLeft a)
    (h3 : middleInnerLeft a < middleInnerRight b) :
    (middleCover (middleRoot a) ∩ middleCover (middleRoot b)).Nonempty := by
  exact ⟨middleInnerLeft a,
    ⟨ha.2.2.1.le, (h1.trans ha.2.2.2).le⟩,
    ⟨(hb.2.2.1.trans_le h2).le, (h3.trans hb.2.2.2).le⟩⟩

theorem solution :
    (∀ i : Fin 15, middleRootCertificate i) →
    ∀ (i : ℕ) (hi : i<7), (middleCover (middleRoot ⟨i,by omega⟩) ∩ middleCover (middleRoot ⟨i+1,by omega⟩)).Nonempty := by
  intro hc i hi
  apply contact _ _ (hc _) (hc _)
  all_goals interval_cases i <;> norm_num [middleInnerLeft, middleInnerRight]
#print axioms solution
