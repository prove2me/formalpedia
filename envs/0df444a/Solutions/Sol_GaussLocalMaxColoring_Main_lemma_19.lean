-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_19
-- status  : ACCEPTED   (disprove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:52:57.265174+00:00
-- url     : https://prove2.me/submissions/258925e6-1098-4d29-a520-05100f302a35

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Iterative
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main GaussLocalMaxColoring.Main
open Classical

theorem solution : ¬ (∀ {n d R : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ)
    (hδ : 0 < δ) (T : ℕ) (hR : 1 ≤ R) (ω : Fin (numLevels n) × Fin R → Space d),
    (∀ j, 1 ≤ j → j ≤ numLevels n → (∀ i, (sampleSet G v δ ω j i).card < T) →
      ((cores G v δ ω (j - 1) \ cores G v δ ω j).card : ℝ) < 2 * T / δ) ∧
    ((∀ j, 1 ≤ j → j ≤ numLevels n → ∀ i, (sampleSet G v δ ω j i).card < T) →
      (∑ j ∈ Finset.Icc 1 (numLevels n),
          ((cores G v δ ω (j - 1) \ cores G v δ ω j).card : ℝ)) <
        2 * (numLevels n : ℝ) * T / δ)) := by
  intro h
  have hn : numLevels 1=0 := by norm_num [numLevels]
  have ht := h (n:=1) (d:=0) (R:=1) (⊥ : SimpleGraph (Fin 1))
    (fun _ => (0 : Space 0)) 1 (by norm_num) 1 (by norm_num) (fun _ => (0 : Space 0))
  have ha : ∀ j, 1 ≤ j → j ≤ numLevels 1 →
      ∀ i : Fin 1, (sampleSet (⊥ : SimpleGraph (Fin 1)) (fun _ => (0 : Space 0)) 1
        (fun _ => (0 : Space 0)) j i).card < 1 := by
    intro j hj hj'
    rw [hn] at hj'
    omega
  have hf := ht.2 ha
  simpa [hn] using hf
#print axioms solution
