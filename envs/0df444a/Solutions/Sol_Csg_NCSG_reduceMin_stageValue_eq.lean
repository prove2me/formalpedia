-- Prove2me | solution 1 for Csg.NCSG.reduceMin_stageValue_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:04:56.226593+00:00
-- url     : https://prove2.me/submissions/f3957d99-3f50-4242-9bb7-608238017206

import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_CoalitionComplement
import Theorems.Thm_Csg_NCSG_combine_compl
import Theorems.Thm_Csg_MatrixGame_value_relabelRow


set_option autoImplicit true
open Csg
open Csg.NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players)
variable (G : NCSG S Players A)
namespace Csg.NCSG
theorem _root_.solution (s : S) (v : S → ℝ) :
    (G.reduceMax Cᶜ).stageValue s v = (G.reduceMin C).stageValue s v := by
  have hA : ((G.reduceMax Cᶜ).stageGame s v).A =
      (((G.reduceMin C).stageGame s v).relabelRow (complCoalitionEquiv C)).A := by
    funext x y
    change G.r s (combine Cᶜ y x) +
        ∑ s', (G.K s (combine Cᶜ y x) s').toReal * v s' =
      G.r s (combine C (complCoalitionEquiv C x) y) +
        ∑ s', (G.K s (combine C (complCoalitionEquiv C x) y) s').toReal * v s'
    rw [combine_compl C y x]
  have hgame : (G.reduceMax Cᶜ).stageGame s v =
      ((G.reduceMin C).stageGame s v).relabelRow (complCoalitionEquiv C) :=
    congrArg MatrixGame.mk hA
  unfold CSG.stageValue
  rw [hgame, MatrixGame.value_relabelRow]
end Csg.NCSG
