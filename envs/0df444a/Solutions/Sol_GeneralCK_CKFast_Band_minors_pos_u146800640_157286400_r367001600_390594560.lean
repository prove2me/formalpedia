-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r367001600_390594560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:03:40.901924+00:00
-- url     : https://prove2.me/submissions/8fd0c654-dc75-458c-ab6e-7dc5918ff296

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [7/16, 149/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 367001600 372899840 ⟨⟨194511321027, 194511321037⟩, ⟨185097694356, 204152940175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 149422080 372899840 378798080 ⟨⟨197176405963, 197176405972⟩, ⟨187732713556, 206847180859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 149422080 152043520 367001600 372899840 ⟨⟨191691931736, 191691931741⟩, ⟨182383097602, 201225727974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 372899840 378798080 ⟨⟨194329371796, 194329371801⟩, ⟨184990247705, 203892613704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 149422080 378798080 384696320 ⟨⟨199832177655, 199832177665⟩, ⟨190358626315, 209531896399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 149422080 384696320 390594560 ⟨⟨202478783261, 202478783270⟩, ⟨192975575624, 212207238182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 152043520 378798080 384696320 ⟨⟨196957810949, 196957810952⟩, ⟨187588596339, 206550293687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 149422080 152043520 384696320 390594560 ⟨⟨199577389659, 199577389664⟩, ⟨190178280040, 209198912381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 154664960 367001600 372899840 ⟨⟨188911291409, 188911291419⟩, ⟨179705029064, 198339551942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 152043520 154664960 372899840 378798080 ⟨⟨191521056322, 191521056330⟩, ⟨182284305730, 200979023571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 157286400 367001600 372899840 ⟨⟨186168244814, 186168244824⟩, ⟨177062404989, 195493183582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 154664960 157286400 372899840 378798080 ⟨⟨188750312044, 188750312053⟩, ⟨179613810211, 198105191246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152043520 154664960 378798080 384696320 ⟨⟨194122124566, 194122124575⟩, ⟨184855077838, 203609600765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 152043520 154664960 384696320 390594560 ⟨⟨196714630200, 196714630208⟩, ⟨187417475738, 206231421347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 157286400 378798080 384696320 ⟨⟨191323978884, 191323978892⟩, ⟨182156999874, 200708607817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 154664960 157286400 384696320 390594560 ⟨⟨193889373249, 193889373259⟩, ⟨184692098402, 203303564759⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 367001600 390594560 t = true :=
  ⟨_, (join_su (m := 152043520) (by decide) (join_sr (m := 378798080) (by decide) (join_su (m := 149422080) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 372899840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 149422080) (by decide) (join_sr (m := 384696320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 384696320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 378798080) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 372899840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 154664960) (by decide) (join_sr (m := 384696320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 384696320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (7/16 : ℝ) (149/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  have e3 : (((390594560 : ℤ) : ℝ) / (D : ℝ)) = (149/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
