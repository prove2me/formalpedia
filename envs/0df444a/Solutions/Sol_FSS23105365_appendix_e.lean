-- Prove2me | solution 1 for FSS23105365.appendix_e
-- status  : ACCEPTED   (prove)
-- author  : @YY
-- created : 2026-10-09T16:08:58.919735+00:00
-- url     : https://prove2.me/submissions/90d1b91e-d947-4881-bc1a-68636aa2bbcb

import Theorems.Thm_FSS23105365_pair_sampling
import Theorems.Thm_FSS23105365_word_sampling
import Theorems.Thm_FSS23105365_chain_to_dfa
import Theorems.Thm_FSS23105365_dyadic_lift
import Theorems.Thm_FSS23105365_exact_markov_complete
import Theorems.Thm_FSS23105365_conditioned_markov
set_option autoImplicit false
open FSS23105365
local notation "Path" => FSS23105365.Path
theorem solution :
    (∀ (q : ℕ) (A : BinaryDFA q),
      ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Option (Fin n)),
        S.randomBits = n ∧ S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
        ExactLaw S pairOutcomeEncode (pairLaw A)) ∧
    (∀ (q : ℕ) (A : BinaryDFA q),
      ∃ D C k : ℕ, ∀ n : ℕ, (acceptedWords A n).Nonempty →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ S : Circuit (Fin n),
          S.depth ≤ D ∧
          (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
          (S.randomBits : ℝ) ≤ (n : ℝ) + (C : ℝ) * logInv ε ∧
          SupportPreserving S (fun x : Bits n => x) (wordLaw A) ∧
          tv (mass S (fun x : Bits n => x)) (wordLaw A) ≤ ε) ∧
    (∀ {q : ℕ} (M : MarkovChain q), TransitionDyadic M →
      ∃ r : ℕ, ∃ B : BinaryDFA r, ∃ v s : ℕ, 0 < v ∧ 0 < s ∧
        ∃ φ : Fin r → Fin q, ∀ n : ℕ, ∀ γ : Path q n,
          (Fintype.card {x : Bits (v + n * s) // B.sampledPath φ v s x = γ} : ℝ) /
            2 ^ (v + n * s) = pathLaw M γ) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), PathDyadic M →
      ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
        TransitionDyadic N ∧
        ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), ExactPathAC0 M ↔ PathDyadic M) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), PathDyadic M →
      ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin q),
        S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
        S.randomBits ≤ C * (n + 1) ∧ ExactLaw S pathEncode (pathLaw M)) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q),
      ∃ D C k : ℕ, ∀ F : Finset (Fin q), ∀ n : ℕ,
        0 < acceptanceProbability M F n →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ∃ S : Circuit (Fin (n + 1) × Fin q),
          S.depth ≤ D ∧
          (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
          (S.randomBits : ℝ) ≤ (C : ℝ) * ((n : ℝ) + logInv ε) ∧
          SupportPreserving S pathEncode (conditionedPathLaw M F) ∧
          tv (mass S pathEncode) (conditionedPathLaw M F) ≤ ε) := ⟨@FSS23105365.pair_sampling, @FSS23105365.word_sampling, @FSS23105365.chain_to_dfa, @FSS23105365.dyadic_lift, FSS23105365.exact_markov_complete.1, FSS23105365.exact_markov_complete.2, @FSS23105365.conditioned_markov⟩
