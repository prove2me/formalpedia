-- Prove2me | solution 1 for ErdosRubinTaylor.exists_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:15.48761+00:00
-- url     : https://prove2.me/submissions/06f7b026-0554-4369-937d-5a3a72d13ca3

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
namespace ErdosRubinTaylor
theorem _root_.solution (G : SimpleGraph V) (W Tgt : Set V)
    (h : ∀ v ∈ W, ∃ n, near G W Tgt n v) :
    ∃ r : V → ℕ, ∀ v ∈ W, v ∉ Tgt → ∃ u ∈ W, G.Adj v u ∧ r u < r v := by
  classical
  refine ⟨fun v => if hv : ∃ n, near G W Tgt n v then Nat.find hv else 0, ?_⟩
  intro v hvW hvT
  have hex := h v hvW
  have hspec := Nat.find_spec hex
  simp only [hex, ↓reduceDIte]
  rcases hm : Nat.find hex with _ | j
  · rw [hm] at hspec; exact absurd hspec hvT
  · rw [hm] at hspec
    obtain ⟨u, huW, hvu, hu⟩ := hspec
    have hexu : ∃ n, near G W Tgt n u := ⟨j, hu⟩
    refine ⟨u, huW, hvu, ?_⟩
    simp only [hexu, ↓reduceDIte]
    have := Nat.find_min' hexu hu
    omega
end ErdosRubinTaylor
