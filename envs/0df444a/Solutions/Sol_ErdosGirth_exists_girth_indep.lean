-- Prove2me | solution 1 for ErdosGirth.exists_girth_indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:37:53.571886+00:00
-- url     : https://prove2.me/submissions/5e65c4c7-0194-431a-9a98-37e28d187be9

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Definitions.Def_GirthLib_ErdosGirth
public import Theorems.Thm_ErdosGirth_exists_good_graph
public import Theorems.Thm_ErdosGirth_exists_of_deletion
public import Theorems.Thm_ErdosGirth_exists_params


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (g : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧
      ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) < ε * n := by
  obtain ⟨N, hN0, hN⟩ := exists_params g hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨p, t, hp0, hp1, ht, hineq⟩ := hN n hn
  obtain ⟨G, D, hD, hcyc, hind⟩ := exists_good_graph (2 * n) g t hp0 hp1 (by omega) hineq
  obtain ⟨H, hH, hHind⟩ := exists_of_deletion n g t G D hD hcyc hind
  refine ⟨H, hH, fun s hs => ?_⟩
  calc (s.card : ℝ) < t := by exact_mod_cast hHind s hs
    _ ≤ ε * n := ht
end ErdosGirth
