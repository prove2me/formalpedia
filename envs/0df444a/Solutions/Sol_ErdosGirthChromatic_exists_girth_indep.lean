-- Prove2me | solution 1 for ErdosGirthChromatic.exists_girth_indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:39:59.988954+00:00
-- url     : https://prove2.me/submissions/d8fbc031-19e3-41f6-942c-6db07199fae9

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirth
public import Definitions.Def_Mycielski_Family
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Definitions.Def_ErdosGirthChromatic_Solution
public import Theorems.Thm_ErdosGirth_exists_girth_indep


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirthChromatic
namespace ErdosGirthChromatic
theorem _root_.solution (g : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧
      ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) < ε * n :=
  ErdosGirth.exists_girth_indep g hε
end ErdosGirthChromatic
