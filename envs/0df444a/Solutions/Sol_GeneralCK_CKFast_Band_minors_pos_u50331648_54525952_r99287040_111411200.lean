-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_54525952_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:00:09.821448+00:00
-- url     : https://prove2.me/submissions/942465ff-6517-4642-bf0b-71f7084a0b46

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 13/200]`, `ρ ∈ [303/2560, 17/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 51380224 99287040 102318080 ⟨⟨136662265640, 136662265656⟩, ⟨129228118919, 144297744084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 51380224 102318080 105349120 ⟨⟨139913403569, 139913403581⟩, ⟨132475903467, 147549775063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 51380224 52428800 99287040 102318080 ⟨⟨134996945032, 134996945044⟩, ⟨127667038731, 142523318534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 51380224 52428800 102318080 105349120 ⟨⟨138223533933, 138223533945⟩, ⟨130889630004, 145751559218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 51380224 105349120 108380160 ⟨⟨143129236144, 143129236160⟩, ⟨135688944308, 150765974899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 50331648 51380224 108380160 111411200 ⟨⟨146310626382, 146310626394⟩, ⟨138868076417, 153947234187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 51380224 52428800 105349120 108380160 ⟨⟨141415651892, 141415651905⟩, ⟨134078302859, 148944809556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 51380224 52428800 108380160 111411200 ⟨⟨144574129353, 144574129368⟩, ⟨137233860824, 152103926518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 52428800 53477376 99287040 102318080 ⟨⟨133370646741, 133370646753⟩, ⟨126141904121, 140791177042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 52428800 53477376 102318080 105349120 ⟨⟨136572856107, 136572856119⟩, ⟨129339515773, 143995746347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 53477376 54525952 99287040 102318080 ⟨⟨131781896406, 131781896421⟩, ⟨124651375425, 139099701142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 53477376 54525952 102318080 105349120 ⟨⟨134959902596, 134959902608⟩, ⟨127824224923, 142280728310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 52428800 53477376 105349120 108380160 ⟨⟨139741405677, 139741405689⟩, ⟨132504010765, 147166143308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 52428800 53477376 108380160 111411200 ⟨⟨142877094748, 142877094763⟩, ⟨135636162576, 150303192721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 53477376 54525952 105349120 108380160 ⟨⟨138105037560, 138105037575⟩, ⟨130964736762, 145428378969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 53477376 54525952 108380160 111411200 ⟨⟨141218070825, 141218070840⟩, ⟨134073655684, 148543447136⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 54525952 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 52428800) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 51380224) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 102318080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 51380224) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 108380160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 105349120) (by decide) (join_su (m := 53477376) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 102318080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 53477376) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 108380160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (13/200 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
