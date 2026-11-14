-- Prove2me | solution 1 for CatalyticTreeEval.Main.lemma_B_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T05:12:00.546376+00:00
-- url     : https://prove2.me/submissions/a53479b7-131f-4fe7-b229-5867c39b0349
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CatalyticTreeEval_Main_canonical_indexing_matching
import Theorems.Thm_CatalyticTreeEval_Main_canonical_coordinate_access

set_option autoImplicit false

open CatalyticTreeEval.Main

theorem solution :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (t : ℕ) (p e : Fin t → ℕ) (w H : ℕ),
      PrimeData p → 1 ≤ w → w ≤ H → w < ∏ i, p i ^ e i →
      ∃ U V : Fin (H.choose w) → Vec (modulus p) (binomialDimension H (delta p e)),
        SMatching (canonical p (modulus p)) U V ∧
        VectorAccess M (primeCode p ++ natsCode ((List.finRange t).map e ++ [w,H])) U V
          (C * (1 + log₂ (H.choose w) + delta p e * log₂ H + log₂ (modulus p))) := by
  obtain ⟨M, C, hC, haccess⟩ := canonical_coordinate_access
  refine ⟨M, C, hC, ?_⟩
  intro t p e w H hp hw hH hprod
  obtain ⟨I, hI⟩ := haccess t p e w H hp hw hH hprod
  exact ⟨canonicalCoefficientVectors p e hp w H I, canonicalEvaluationVectors p e w H I,
    canonical_indexing_matching p e hp w H hprod I, hI⟩
