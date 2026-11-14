-- Prove2me | solution 1 for CatalyticTreeEval.Main.corollary_B_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T02:05:44.941235+00:00
-- url     : https://prove2.me/submissions/b048bd53-d45d-4193-9bd0-8cb24e9a078b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CatalyticTreeEval_Main_composite_weight_detector_properties
import Theorems.Thm_CatalyticTreeEval_Main_composite_weight_detector_print

set_option autoImplicit false

open CatalyticTreeEval.Main

theorem solution :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (t : ℕ) (p e : Fin t → ℕ) (w H : ℕ),
      PrimeData p → 1 ≤ w → w ≤ H → w < ∏ i, p i ^ e i →
      ∃ f : Poly (modulus p) H,
        Multilinear f ∧ f.totalDegree ≤ delta p e - 1 ∧
        (∀ x : Fin H → Bool, weight x ≤ w →
          (weight x = w → MvPolynomial.eval (boolPoint x) f = 0) ∧
          (weight x < w → MvPolynomial.eval (boolPoint x) f ∈ canonical p (modulus p) ∧
            MvPolynomial.eval (boolPoint x) f ≠ 0)) ∧
        PolyPrint M (primeCode p ++ natsCode ((List.finRange t).map e ++ [w,H])) f
          (C * (delta p e * log₂ H + log₂ (modulus p))) := by
  obtain ⟨M, C, hC, hprint⟩ := composite_weight_detector_print
  refine ⟨M, C, hC, ?_⟩
  intro t p e w H hp hw hH hprod
  have h := composite_weight_detector_properties p e hp w H hprod
  exact ⟨compositeWeightDetector p e hp w H, h.1, h.2.1, h.2.2,
    hprint t p e w H hp hw hH hprod⟩
