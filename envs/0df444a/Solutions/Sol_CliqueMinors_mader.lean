-- Prove2me | solution 1 for CliqueMinors.mader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:21.44523+00:00
-- url     : https://prove2.me/submissions/187c2ea8-4dfc-4392-82e8-5c9a034b9fde

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_mader_aux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
namespace CliqueMinors
theorem _root_.solution [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : 2 ^ r * Fintype.card V ≤ 8 * G.edgeFinset.card) :
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  classical
  refine mader_aux r G Finset.univ Finset.univ_nonempty (fun _ _ _ => Finset.mem_univ _) ?_
  convert h using 3
  · exact Finset.card_univ
  · ext e; simp
end CliqueMinors
