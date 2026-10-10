-- Prove2me | solution 1 for FSS23105365.exact_markov_complete
-- status  : ACCEPTED   (prove)
-- author  : @YY
-- created : 2026-10-09T16:07:46.857977+00:00
-- url     : https://prove2.me/submissions/fa7965b2-5e33-43dc-b997-21922bdfe3c4

import Theorems.Thm_FSS23105365_exact_markov
import Theorems.Thm_FSS23105365_exact_markov_seed
set_option autoImplicit false
open FSS23105365
theorem solution :
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), ExactPathAC0 M ↔ PathDyadic M) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), PathDyadic M →
      ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin q),
        S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
        S.randomBits ≤ C * (n + 1) ∧ ExactLaw S pathEncode (pathLaw M)) := ⟨@FSS23105365.exact_markov, @FSS23105365.exact_markov_seed⟩
