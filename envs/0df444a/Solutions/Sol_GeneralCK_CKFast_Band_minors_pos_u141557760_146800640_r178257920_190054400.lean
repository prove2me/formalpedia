-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_146800640_r178257920_190054400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:34:38.974249+00:00
-- url     : https://prove2.me/submissions/c2abc1ca-fb73-4cf8-9013-149b96394852

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 7/40]`, `ρ ∈ [17/80, 29/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142868480 178257920 181207040 ⟨⟨106489763215, 106489763224⟩, ⟨102180839458, 110865345555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 141557760 142868480 181207040 184156160 ⟨⟨108071794528, 108071794535⟩, ⟨103752871724, 112457268087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 142868480 144179200 178257920 181207040 ⟨⟨105591133568, 105591133577⟩, ⟨101311076891, 109937123697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142868480 144179200 181207040 184156160 ⟨⟨107162185281, 107162185289⟩, ⟨102872147563, 111518053974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 142868480 184156160 187105280 ⟨⟨109649463510, 109649463517⟩, ⟨105320600194, 114044769156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 141557760 142868480 187105280 190054400 ⟨⟨111222808477, 111222808484⟩, ⟨106884062482, 115627887778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 142868480 144179200 184156160 187105280 ⟨⟨108728965144, 108728965153⟩, ⟨104429003434, 113094654744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 142868480 144179200 187105280 190054400 ⟨⟨110291510340, 110291510347⟩, ⟨105981681019, 114666963863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 144179200 145489920 178257920 181207040 ⟨⟨104701671271, 104701671279⟩, ⟨100450061599, 109018502798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 144179200 145489920 181207040 184156160 ⟨⟨106261805037, 106261805044⟩, ⟨102000233593, 110588501032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 145489920 146800640 178257920 181207040 ⟨⟨103821198557, 103821198566⟩, ⟨99597624981, 108109295583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 145489920 146800640 181207040 184156160 ⟨⟨105370475538, 105370475545⟩, ⟨101136960665, 109668421561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 144179200 145489920 184156160 187105280 ⟨⟨107817755618, 107817755625⟩, ⟨103546277999, 112154259868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 144179200 145489920 187105280 190054400 ⟨⟨109369559097, 109369559106⟩, ⟨105088230259, 113715816044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 145489920 146800640 184156160 187105280 ⟨⟨106915656221, 106915656230⟩, ⟨102672254224, 111223396451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 145489920 146800640 187105280 190054400 ⟨⟨108456775631, 108456775638⟩, ⟨104203540064, 112774255900⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 146800640 178257920 190054400 t = true :=
  ⟨_, (join_su (m := 144179200) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 142868480) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 181207040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 142868480) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 187105280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184156160) (by decide) (join_su (m := 145489920) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 181207040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 145489920) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 187105280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (29/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
