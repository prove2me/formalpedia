-- Prove2me | solution 1 for CliqueMinors.exists_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:57.830842+00:00
-- url     : https://prove2.me/submissions/85d3ceda-4c1f-49fc-b087-36f99e60efd2

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_exists_low_deg_K4

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
namespace CliqueMinors
theorem _root_.solution [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : ∃ v, G.degree v ≤ 2 := by
  classical
  obtain ⟨v, -, hv⟩ := exists_low_deg_K4 G Finset.univ Finset.univ_nonempty
    (fun _ _ _ => Finset.mem_univ _) h
  refine ⟨v, ?_⟩
  convert Nat.le_of_lt_succ hv using 1
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  congr 1; ext; simp
end CliqueMinors
