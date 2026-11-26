-- Prove2me | solution 1 for FD1D.DyadicMass.branch_root_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:27.35954+00:00
-- url     : https://prove2.me/submissions/89c487e6-0972-4e99-a895-4bb972ddda0b

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (l r : DyadicMass L) (z : ℝ) :
    (∑ y : Fin (2 ^ (0 : Fin (L + 1)).val),
      (branch l r).nodeCoefficient ⟨(0 : Fin (L + 1)), y⟩ *
        dyadicTent (haarNodeLeft ⟨(0 : Fin (L + 1)), y⟩)
          (haarNodeWidth ⟨(0 : Fin (L + 1)), y⟩) z) =
      (l.total - r.total) * dyadicTent 0 1 z := by
  classical
  let e : Fin 1 ≃ Fin (2 ^ (0 : Fin (L + 1)).val) :=
    finCongr (by norm_num)
  rw [← e.sum_comp, Fin.sum_univ_one]
  have he : e 0 = 0 := by
    apply Fin.ext
    norm_num [e]
  rw [he]
  let root : CompleteHaarNode (L + 1) :=
    ⟨⟨0, Nat.zero_lt_succ L⟩, (0 : Fin 1)⟩
  have hv :
      (⟨(0 : Fin (L + 1)),
        (0 : Fin (2 ^ (0 : Fin (L + 1)).val))⟩ :
          CompleteHaarNode (L + 1)) = root := by
    rfl
  rw [hv]
  norm_num [root, nodeCoefficient, nodeChildMasses, haarNodeLeft, haarNodeWidth]
end FD1D.DyadicMass
