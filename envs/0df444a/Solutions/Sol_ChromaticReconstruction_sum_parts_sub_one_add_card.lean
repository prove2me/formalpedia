-- Prove2me | solution 1 for ChromaticReconstruction.sum_parts_sub_one_add_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:00.294687+00:00
-- url     : https://prove2.me/submissions/636dc180-86d6-4f38-a4af-018cace92caf

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_CountingUpper
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {k : ℕ} (μ : Nat.Partition k) :
    (μ.parts.map fun a => a - 1).sum + Multiset.card μ.parts = k := by
  have : μ.parts.map (fun a => a - 1 + 1) = μ.parts.map id :=
    Multiset.map_congr rfl fun a ha => by have := μ.parts_pos ha; simp; omega
  have h2 := congrArg Multiset.sum this
  rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one,
    Multiset.map_id, μ.parts_sum] at h2
  exact h2
end ChromaticReconstruction
