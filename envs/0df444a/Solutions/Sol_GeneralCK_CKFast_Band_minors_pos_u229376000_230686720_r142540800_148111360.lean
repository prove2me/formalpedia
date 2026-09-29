-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u229376000_230686720_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:59:25.100117+00:00
-- url     : https://prove2.me/submissions/ac06de41-c3eb-44ff-84b5-a95a44288398

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [35/128, 11/40]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
correction-band checker; each cell is kernel-checked in its own declaration. -/

theorem leaf_ok {U0 U1 R0 R1 : ℤ} {h : Hint} (hc : cellOK U0 U1 R0 R1 h = true) :
    treeOK U0 U1 R0 R1 (.leaf h) = true := by
  simpa only [treeOK] using hc

theorem join_su {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (U0 ≤ m) && decide (m ≤ U1)) = true)
    (hl : treeOK U0 m R0 R1 l = true) (hr : treeOK m U1 R0 R1 r = true) :
    treeOK U0 U1 R0 R1 (.su m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

theorem join_sr {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (R0 ≤ m) && decide (m ≤ R1)) = true)
    (hl : treeOK U0 U1 R0 m l = true) (hr : treeOK U0 U1 m R1 r = true) :
    treeOK U0 U1 R0 R1 (.sr m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

set_option maxRecDepth 100000 in
theorem cell0 : cellOK 229376000 229703680 142540800 143933440 ⟨⟨48712424933, 48712424938⟩, ⟨47857420106, 49570670663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 229703680 230031360 142540800 143933440 ⟨⟨48603062600, 48603062606⟩, ⟨47749156219, 49460203094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 229376000 229703680 143933440 145326080 ⟨⟨49172646705, 49172646712⟩, ⟨48316648462, 50031887010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 229703680 230031360 143933440 145326080 ⟨⟨49062306955, 49062306961⟩, ⟨48207408678, 49920440512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230031360 230359040 142540800 143933440 ⟨⟨48493863537, 48493863540⟩, ⟨47641053022, 49349901396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230359040 230686720 142540800 143933440 ⟨⟨48384827116, 48384827121⟩, ⟨47533109891, 49239764942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 230031360 230359040 143933440 145326080 ⟨⟨48952131589, 48952131591⟩, ⟨48098330694, 49809161001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230359040 230686720 143933440 145326080 ⟨⟨48842119975, 48842119980⟩, ⟨47989413887, 49698047845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 229376000 229703680 145326080 146718720 ⟨⟨49632632334, 49632632340⟩, ⟨48775641193, 50492866691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 229703680 230031360 145326080 146718720 ⟨⟨49521316641, 49521316646⟩, ⟨48665426979, 50380442743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 229703680 146718720 148111360 ⟨⟨50092382400, 50092382407⟩, ⟨49234398878, 50953610289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229703680 230031360 146718720 148111360 ⟨⟨49980092236, 49980092241⟩, ⟨49123211699, 50840210371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 230031360 230359040 145326080 146718720 ⟨⟨49410166440, 49410166441⟩, ⟨48555375671, 50268186894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 230359040 230686720 145326080 146718720 ⟨⟨49299181094, 49299181099⟩, ⟨48445486643, 50156098503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 230031360 230359040 146718720 148111360 ⟨⟨49867968662, 49867968665⟩, ⟨49012188525, 50726979651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230359040 230686720 146718720 148111360 ⟨⟨49756011039, 49756011045⟩, ⟨48901328723, 50613917487⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 229376000 230686720 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 230031360) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 229703680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 229703680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 230359040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 230359040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 230031360) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 229703680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 229703680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 230359040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 230359040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (35/128 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((229376000 : ℤ) : ℝ) / (D : ℝ)) = (35/128 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
