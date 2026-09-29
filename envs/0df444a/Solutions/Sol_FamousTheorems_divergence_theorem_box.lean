-- Prove2me | solution 1 for FamousTheorems.divergence_theorem_box
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:15:31.015215+00:00
-- url     : https://prove2.me/submissions/c8a74312-034f-4ef8-982a-388c426faba7

import Mathlib

open MeasureTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → E)
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → E)
    (s : Set (Fin (n + 1) → ℝ)) (hs : s.Countable) (Hc : ContinuousOn f (Set.Icc a b))
    (Hd : ∀ x ∈ (Set.univ.pi fun i => Set.Ioo (a i) (b i)) \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (Pi.single i 1) i) (Set.Icc a b)) :
    ∫ x in Set.Icc a b, ∑ i, f' x (Pi.single i 1) i =
      ∑ i : Fin (n + 1),
        ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f (i.insertNth (b i) x) i) -
          ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f (i.insertNth (a i) x) i) :=
  MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable a b hle f f' s hs Hc Hd Hi
