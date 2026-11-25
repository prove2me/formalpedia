-- Prove2me | solution 1 for CliqueMinors.isMinor_K5_of_card_edgeFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:18.870528+00:00
-- url     : https://prove2.me/submissions/fa3d9627-cc8f-4de6-aa52-e81ea7100aab

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Theorems.Thm_CliqueMinors_mader_five_aux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (h : 3 * Fintype.card V ≤ G.edgeFinset.card + 5) : IsMinor (⊤ : SimpleGraph (Fin 5)) G :=
  mader_five_aux _ G Finset.univ rfl (fun _ _ _ => Finset.mem_univ _)
    (by rwa [Finset.card_univ]) (by rwa [Finset.card_univ])
end CliqueMinors
