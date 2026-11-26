-- Prove2me | solution 1 for Falmagne.flow_zero_of_source_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:35.793636+00:00
-- url     : https://prove2.me/submissions/f2ca950a-957c-4ddf-b3aa-a96848b59352

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
public import Theorems.Thm_Falmagne_flow_edge_le_outflow
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_nil
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil



set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}
namespace Falmagne
theorem _root_.solution (h : IsFlow q 0) : ∀ A x, x ∈ A → q x A = 0 := by
  intro A
  induction hn : (Finset.univ \ A).card using Nat.strong_induction_on generalizing A with
  | h n ih =>
      intro x hx
      by_cases hU : A = Finset.univ
      · subst A
        have he := flow_edge_le_outflow h hx
        have hz := h.source
        have hnn := h.nonneg x Finset.univ hx
        linarith
      · have hA : A.Nonempty := ⟨x, hx⟩
        have hi : inflow q A = 0 := by
          unfold inflow
          apply Finset.sum_eq_zero
          intro y hy
          have hyA : y ∉ A := (Finset.mem_sdiff.mp hy).2
          have hlt : (Finset.univ \ insert y A).card < n := by
            rw [← hn]
            apply Finset.card_lt_card
            constructor
            · intro z hz
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
                not_or] at hz ⊢
              exact hz.2
            · intro heq
              have hymem : y ∈ Finset.univ \ A := by simp [hyA]
              have := heq hymem
              simp at this
          exact ih _ hlt (insert y A) rfl y (Finset.mem_insert_self _ _)
        have hout : outflow q A = 0 := (h.conserve A hA hU).trans hi
        have he := flow_edge_le_outflow h hx
        have hnn := h.nonneg x A hx
        linarith
end Falmagne
