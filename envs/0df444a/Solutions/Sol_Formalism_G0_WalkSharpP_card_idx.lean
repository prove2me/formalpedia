-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.card_idx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:28.147136+00:00
-- url     : https://prove2.me/submissions/ffe5fa32-b3da-4801-a77c-3df97a22db24

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
namespace Formalism.G0.WalkSharpP
theorem _root_.solution {V : ℕ} (m : ℕ) (B : Finset (Fin V)) : (idx m B).card = m ^ B.card := by

  unfold idx
  rw [Fintype.card_piFinset]
  calc ∏ u, (if u ∈ B then Finset.range m else {0}).card = ∏ u, (if u ∈ B then m else 1) := by
        refine Finset.prod_congr rfl fun u _ => ?_
        split_ifs <;> simp
    _ = ∏ u ∈ B, (if u ∈ B then m else 1) :=
        (Finset.prod_subset (Finset.subset_univ B) fun u _ hu => if_neg hu).symm
    _ = ∏ u ∈ B, m := Finset.prod_congr rfl fun u hu => if_pos hu
    _ = m ^ B.card := Finset.prod_const m
end Formalism.G0.WalkSharpP
