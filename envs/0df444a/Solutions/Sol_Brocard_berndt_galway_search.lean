-- Prove2me | solution 1 for Brocard.berndt_galway_search
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-01T02:00:21.061913+00:00
-- url     : https://prove2.me/submissions/e87e2196-322f-4de4-8225-8c0fd54eefc9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Brocard_berndt_galway_block_0
import Theorems.Thm_Brocard_berndt_galway_block_1
import Theorems.Thm_Brocard_berndt_galway_block_2
import Theorems.Thm_Brocard_berndt_galway_block_3
import Theorems.Thm_Brocard_berndt_galway_block_4
import Theorems.Thm_Brocard_berndt_galway_block_5
import Theorems.Thm_Brocard_berndt_galway_block_6
import Theorems.Thm_Brocard_berndt_galway_block_7
import Theorems.Thm_Brocard_berndt_galway_block_8
import Theorems.Thm_Brocard_berndt_galway_block_9

theorem solution (n m : ℕ) (hn : n < 10 ^ 9)
    (h : Nat.factorial n + 1 = m ^ 2) : n = 4 ∨ n = 5 ∨ n = 7 := by
  by_cases h0 : n < 10 ^ 8
  · exact Brocard.berndt_galway_block_0 n m h0 h
  · exfalso
    have : (1 * 10 ^ 8 ≤ n ∧ n < 2 * 10 ^ 8) ∨ (2 * 10 ^ 8 ≤ n ∧ n < 3 * 10 ^ 8) ∨
        (3 * 10 ^ 8 ≤ n ∧ n < 4 * 10 ^ 8) ∨ (4 * 10 ^ 8 ≤ n ∧ n < 5 * 10 ^ 8) ∨
        (5 * 10 ^ 8 ≤ n ∧ n < 6 * 10 ^ 8) ∨ (6 * 10 ^ 8 ≤ n ∧ n < 7 * 10 ^ 8) ∨
        (7 * 10 ^ 8 ≤ n ∧ n < 8 * 10 ^ 8) ∨ (8 * 10 ^ 8 ≤ n ∧ n < 9 * 10 ^ 8) ∨
        (9 * 10 ^ 8 ≤ n ∧ n < 10 * 10 ^ 8) := by omega
    rcases this with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Brocard.berndt_galway_block_1 n m a b h
    · exact Brocard.berndt_galway_block_2 n m a b h
    · exact Brocard.berndt_galway_block_3 n m a b h
    · exact Brocard.berndt_galway_block_4 n m a b h
    · exact Brocard.berndt_galway_block_5 n m a b h
    · exact Brocard.berndt_galway_block_6 n m a b h
    · exact Brocard.berndt_galway_block_7 n m a b h
    · exact Brocard.berndt_galway_block_8 n m a b h
    · exact Brocard.berndt_galway_block_9 n m a b h
