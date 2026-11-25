-- Prove2me | solution 1 for CliqueMinors.exists_low_deg_K3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:55.251638+00:00
-- url     : https://prove2.me/submissions/54269d5e-ded1-4049-ad67-e26df84b0a9a

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_k3_aux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty)
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) :
    ∃ v ∈ S, G.degree v < 2 := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  exact h (k3_aux _ G S rfl hS hsupp hc)
end CliqueMinors
