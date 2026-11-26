-- Prove2me | solution 1 for FD1D.CoherentTreeLabel.levelSum_eq_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:23.895525+00:00
-- url     : https://prove2.me/submissions/be89ef7d-ff67-454f-9927-b9c728487a8a

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_levelSum_succ

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
namespace CoherentTreeLabel
theorem _root_.solution
    {L : ℕ} {A : Type*} [AddCommMonoid A]
    (f : CoherentTreeLabel L A) {d : ℕ} (hdL : d ≤ L) :
    levelSum f.value d = f.value 0 dyadicRoot := by
  induction d with
  | zero =>
      exact Fin.sum_univ_one (f.value 0)
  | succ d ih =>
      rw [levelSum_succ]
      simp_rw [← f.children d (by omega)]
      exact ih (by omega)
end CoherentTreeLabel
end FD1D
