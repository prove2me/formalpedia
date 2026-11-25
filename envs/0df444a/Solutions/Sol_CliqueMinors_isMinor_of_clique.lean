-- Prove2me | solution 1 for CliqueMinors.isMinor_of_clique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:42.742991+00:00
-- url     : https://prove2.me/submissions/4cccdcaa-d469-426b-8e6e-aa58deb9cd7c

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_singleton_connected

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {r : ℕ} (f : Fin r → V)
    (hf : ∀ i j, i ≠ j → G.Adj (f i) (f j)) : IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  refine ⟨⟨fun i => {f i}, fun i => Finset.singleton_nonempty _,
    fun i => singleton_connected G (f i), fun i j hij => ?_, fun i j hij => ?_⟩⟩
  · rw [Finset.disjoint_singleton]; exact (hf i j hij).ne
  · exact ⟨f i, Finset.mem_singleton_self _, f j, Finset.mem_singleton_self _,
      hf i j (by simpa using hij)⟩
end CliqueMinors
