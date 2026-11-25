-- Prove2me | solution 1 for CliqueMinors.exists_low_deg_K4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:50.585666+00:00
-- url     : https://prove2.me/submissions/c47b68c9-ce9b-41ab-bfae-e4e72750129d

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_dirac_aux

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
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    ∃ v ∈ S, G.degree v < 3 := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  exact h (dirac_aux _ G S rfl hS hsupp hc)
end CliqueMinors
