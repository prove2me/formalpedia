-- Prove2me | solution 1 for CatalyticTreeEval.Main.lemma_B_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T01:47:04.781599+00:00
-- url     : https://prove2.me/submissions/391d2fa5-e4d5-47f2-bc26-84a6b427a4a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CatalyticTreeEval_Main_weight_detector_properties
import Theorems.Thm_CatalyticTreeEval_Main_weight_detector_print

set_option autoImplicit false

open CatalyticTreeEval.Main

theorem solution :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (p e w H : ℕ), Nat.Prime p → 1 ≤ H →
      ∃ f : Poly p H, Symmetric f ∧ Multilinear f ∧ f.totalDegree ≤ p ^ e - 1 ∧
        (∀ x : Fin H → Bool, MvPolynomial.eval (boolPoint x) f =
          if weight x % (p ^ e) = w % (p ^ e) then 0 else 1) ∧
        PolyPrint M (natsCode [p,e,w,H]) f
          (C * ((p ^ e : ℕ) * log₂ (H + 1) + log₂ p)) := by
  obtain ⟨M, C, hC, hprint⟩ := weight_detector_print
  refine ⟨M, C, hC, ?_⟩
  intro p e w H hp hH
  have h := weight_detector_properties p e w H hp
  exact ⟨weightDetector p e w H, h.1, h.2.1, h.2.2.1, h.2.2.2, hprint p e w H hp hH⟩
