-- Prove2me | solution 1 for FoundationsRL.Bandits.optimism_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:30:17.454818+00:00
-- url     : https://prove2.me/submissions/643569dd-f606-4760-ae6b-c72f5723f771

import Mathlib



namespace FoundationsRL.Bandits

theorem opt_main {A : ℕ} (fStar : Fin A → ℝ) (piStar : Fin A)
    (fLo fHi : Fin A → ℝ) (hCI : ∀ a : Fin A, fStar a ∈ Set.Icc (fLo a) (fHi a))
    (pit : Fin A) (hOpt : ∀ a : Fin A, fHi a ≤ fHi pit) :
    fStar piStar - fStar pit ≤ fHi pit - fLo pit := by
  have h1 := (hCI piStar).2
  have h2 := hOpt piStar
  have h3 := (hCI pit).1
  linarith

end FoundationsRL.Bandits

open FoundationsRL.Bandits

theorem solution {A : ℕ} (fStar : Fin A → ℝ) (piStar : Fin A)
    (hStar : ∀ a : Fin A, fStar a ≤ fStar piStar)
    (fLo fHi : Fin A → ℝ) (hCI : ∀ a : Fin A, fStar a ∈ Set.Icc (fLo a) (fHi a))
    (pit : Fin A) (hOpt : ∀ a : Fin A, fHi a ≤ fHi pit) :
    fStar piStar - fStar pit ≤ fHi pit - fLo pit := by
  exact opt_main fStar piStar fLo fHi hCI pit hOpt
