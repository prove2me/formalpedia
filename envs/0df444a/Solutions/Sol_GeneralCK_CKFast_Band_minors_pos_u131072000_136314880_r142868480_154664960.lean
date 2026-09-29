-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_136314880_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:26:43.248282+00:00
-- url     : https://prove2.me/submissions/883ba0e0-a56e-474f-be40-15d3abc97df6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 13/80]`, `ρ ∈ [109/640, 59/320]` by 19 cells of the computing
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
theorem cell0 : cellOK 131072000 132382720 142868480 145817600 ⟨⟨93545277830, 93545277838⟩, ⟨89116111950, 98049283880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 131072000 132382720 145817600 148766720 ⟨⟨95283324606, 95283324615⟩, ⟨90843131702, 99798207155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 132382720 133038080 142868480 145817600 ⟨⟨92920184893, 92920184898⟩, ⟨90135727947, 95734219307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 133038080 133693440 142868480 145817600 ⟨⟨92506541985, 92506541993⟩, ⟨89733198691, 95309263532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 132382720 133693440 145817600 148766720 ⟨⟨94438213557, 94438213566⟩, ⟨90030430180, 98919761212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 131072000 132382720 148766720 151715840 ⟨⟨97015581468, 97015581477⟩, ⟨92564445721, 101541255640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131072000 132382720 151715840 154664960 ⟨⟨98742104841, 98742104849⟩, ⟨94280109281, 103278486931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 132382720 133693440 148766720 151715840 ⟨⟨96157706075, 96157706083⟩, ⟨91739006819, 100650025568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 132382720 133693440 151715840 154664960 ⟨⟨97871589314, 97871589321⟩, ⟨93442055019, 102374599117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 133693440 134348800 142868480 145817600 ⟨⟨92095336386, 92095336395⟩, ⟨89333018859, 94886835069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 134348800 135004160 142868480 145817600 ⟨⟨91686541731, 91686541740⟩, ⟨88935163162, 94466906446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 133693440 135004160 145817600 148766720 ⟨⟨93603000582, 93603000585⟩, ⟨89227104367, 98051755154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 135004160 135659520 142868480 145817600 ⟨⟨91280132036, 91280132044⟩, ⟨88539606671, 94049450596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 135659520 136314880 142868480 145817600 ⟨⟨90876081689, 90876081695⟩, ⟨88146324814, 93634440837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 135004160 136314880 145817600 148766720 ⟨⟨92777473619, 92777473628⟩, ⟨88432954855, 97193963728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 135004160 148766720 151715840 ⟨⟨95309821100, 95309821105⟩, ⟨90923037394, 99769326045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 133693440 135004160 151715840 154664960 ⟨⟨97011153817, 97011153819⟩, ⟨92613561318, 101481329737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 135004160 136314880 148766720 151715840 ⟨⟨94471713442, 94471713449⟩, ⟨90116336910, 98898930871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 135004160 136314880 151715840 154664960 ⟨⟨96160584268, 96160584275⟩, ⟨91794426578, 100598451703⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 136314880 142868480 154664960 t = true :=
  ⟨_, (join_su (m := 133693440) (by decide) (join_sr (m := 148766720) (by decide) (join_su (m := 132382720) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 145817600) (by decide) (join_su (m := 133038080) (by decide) (leaf_ok cell2) (leaf_ok cell3)) (leaf_ok cell4))) (join_su (m := 132382720) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 151715840) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_sr (m := 148766720) (by decide) (join_su (m := 135004160) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 134348800) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (leaf_ok cell11)) (join_sr (m := 145817600) (by decide) (join_su (m := 135659520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (leaf_ok cell14))) (join_su (m := 135004160) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_sr (m := 151715840) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
