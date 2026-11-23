-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.terminals_rooted_expansion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T06:24:46.797665+00:00
-- url     : https://prove2.me/submissions/7208b72a-10d9-4906-90a2-5efc6562886b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications
import Theorems.Thm_ChenCapacityTerminals_Exact_legal_construction_exists
import Theorems.Thm_ChenCapacityTerminals_Exact_terminal_cardinality
import Theorems.Thm_ChenCapacityTerminals_Exact_terminal_expansion
import Theorems.Thm_ChenCapacityTerminals_Exact_terminal_machine_realization

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution :
    ∃ C : ℝ, ∃ P : List TrulySubcubicAPSP.Instr, 0 < C ∧ TerminalTime P ∧
      ∀ (G : IntegerInput) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ),
        TerminalParameters G r d L b t →
        (∃ c, LegalConstruction G.network r d L b t c) ∧
        ∀ c, LegalConstruction G.network r d L b t c → TerminalShape C G.network r d L b t c := by
  obtain ⟨P, hP⟩ := terminal_machine_realization
  obtain ⟨C, hC, hcard⟩ := terminal_cardinality
  refine ⟨C, P, hC, hP, ?_⟩
  intro G r d L b t hparams
  rcases hparams with ⟨hvalid, hprepared, hd, hdn, hL, ht, hmass⟩
  have hn : G.network.vertices.card = G.n := by simp [IntegerInput.network]
  have hn' : d ≤ G.network.vertices.card := by simpa [hn] using hdn
  constructor
  · exact legal_construction_exists G.network r d L b t hprepared hd hn' hL ht
  · intro c hc
    obtain ⟨hsub, hcardinal⟩ := hcard G.network r d L b t c hprepared hd hn' hL ht hc
    obtain ⟨hexpand, hunit⟩ := terminal_expansion G.network r d L b t c
      hprepared hd hn' hL ht hc
    exact ⟨hsub, hcardinal, hexpand, hunit⟩
