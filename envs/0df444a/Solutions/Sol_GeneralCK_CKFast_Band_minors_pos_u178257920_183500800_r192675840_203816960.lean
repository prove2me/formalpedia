-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:19:22.870634+00:00
-- url     : https://prove2.me/submissions/3258298a-aab1-4b4b-b7a0-124943294dd6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 192675840 195461120 ⟨⟨90569957177, 90569957185⟩, ⟨86936931873, 94252145831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 179568640 195461120 198246400 ⟨⟨91783350195, 91783350203⟩, ⟨88141831881, 95474024111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 179568640 180879360 192675840 195461120 ⟨⟨89827684144, 89827684147⟩, ⟨86214260430, 93489850454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 195461120 198246400 ⟨⟨91032387079, 91032387082⟩, ⟨87410501260, 94703009765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 179568640 198246400 201031680 ⟨⟨92994669356, 92994669363⟩, ⟨89344680615, 96693805504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 179568640 201031680 203816960 ⟨⟨94203928193, 94203928200⟩, ⟨90545491432, 97911503721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180879360 198246400 201031680 ⟨⟨92235060307, 92235060310⟩, ⟨88604734287, 95914117024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 179568640 180879360 201031680 203816960 ⟨⟨93435716971, 93435716974⟩, ⟨89796972491, 97123185539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180879360 182190080 192675840 195461120 ⟨⟨89091147955, 89091147961⟩, ⟨85497092643, 92733531584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 182190080 195461120 198246400 ⟨⟨90287200996, 90287201004⟩, ⟨86684714795, 93938011745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 182190080 183500800 192675840 195461120 ⟨⟨88360254364, 88360254372⟩, ⟨84785338424, 91983090675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 182190080 183500800 195461120 198246400 ⟨⟨89547697326, 89547697333⟩, ⟨85964382006, 93178931145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 198246400 201031680 ⟨⟨91481267640, 91481267646⟩, ⟨87870371793, 95140483828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 180879360 182190080 201031680 203816960 ⟨⟨92673360648, 92673360656⟩, ⟨89054076242, 96340960759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182190080 183500800 198246400 201031680 ⟨⟨90733196371, 90733196378⟩, ⟨87141502271, 94372806674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182190080 183500800 201031680 203816960 ⟨⟨91916763898, 91916763904⟩, ⟨88316711460, 95564729812⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 192675840 203816960 t = true :=
  ⟨_, (join_su (m := 180879360) (by decide) (join_sr (m := 198246400) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 195461120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 195461120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 179568640) (by decide) (join_sr (m := 201031680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 201031680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 198246400) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 195461120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 195461120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 182190080) (by decide) (join_sr (m := 201031680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 201031680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
