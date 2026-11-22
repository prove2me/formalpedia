-- Prove2me | solution 2 for CatalyticTreeEval.Main.theorem_3_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T22:42:08.919834+00:00
-- url     : https://prove2.me/submissions/1de6044d-6ec7-42d1-acc6-c6db42028dd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CatalyticTreeEval_Main_Polynomials
import Theorems.Thm_CatalyticTreeEval_Main_balanced_coordinate_access
import Theorems.Thm_CatalyticTreeEval_Main_balanced_parameter_bounds
import Theorems.Thm_CatalyticTreeEval_Main_canonical_indexing_matching

set_option autoImplicit false

open CatalyticTreeEval.Main

theorem solution :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (t : ℕ) (p : Fin t → ℕ) (w H : ℕ),
      PrimeData p → 1 ≤ w → w ≤ H →
      ∃ (d : ℕ) (U V : Fin (H.choose w) → Vec (modulus p) d),
        d ≤ binomialDimension H (⌊((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ))⌋₊ + 1) ∧
        SMatching (canonical p (modulus p)) U V ∧
        VectorAccess M (primeCode p ++ natsCode [w,H]) U V
          (C * (1 + log₂ (H.choose w) +
            ((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ)) * log₂ (H + 1) + log₂ (modulus p))) := by
  obtain ⟨M, C, hC, haccess⟩ := balanced_coordinate_access
  refine ⟨M, C, hC, ?_⟩
  intro t p w H hp hw hwH
  obtain ⟨I, hI⟩ := haccess t p w H hp hw hwH
  obtain ⟨hwprod, -, hdim⟩ :=
    balanced_parameter_bounds p hp w H (by omega)
  refine ⟨binomialDimension H (delta p (balancedExponents p w)),
    canonicalCoefficientVectors p (balancedExponents p w) hp w H I,
    canonicalEvaluationVectors p (balancedExponents p w) w H I,
    hdim, canonical_indexing_matching p (balancedExponents p w) hp w H hwprod I, hI⟩
