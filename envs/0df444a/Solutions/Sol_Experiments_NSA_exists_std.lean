-- Prove2me | solution 1 for Experiments.NSA.exists_std
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:22:12.10823+00:00
-- url     : https://prove2.me/submissions/b28fd159-aaa4-42ef-8b3e-ea12a441e331

import Mathlib
import Definitions.Def_Experiments_Ultrapower
import Theorems.Thm_Experiments_NSA_approx_std_coe

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Experiments.NSA
theorem _root_.solution [ProperSpace E] {x : Hyp E} {C : ℝ} (hx : ext norm x ≤ std C) :
    ∃ a, ‖a‖ ≤ C ∧ x ≈ₕ std a := by
  induction x using Germ.inductionOn with
  | h u =>
    obtain ⟨a, ha, hu⟩ := (isCompact_closedBall (0 : E) C).ultrafilter_le_nhds
      (.map u (hyperfilter ℕ)) (le_principal_iff.mpr
        ((Germ.coe_le.mp hx).mono fun n hn => mem_closedBall_zero_iff.mpr hn))
    exact ⟨a, mem_closedBall_zero_iff.mp ha, approx_std_coe.mpr hu⟩
end Experiments.NSA
