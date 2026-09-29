-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r461373440_508559360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:52:43.475898+00:00
-- url     : https://prove2.me/submissions/a3470772-59ab-4e47-920c-1f52c154d4d9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [11/20, 97/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 461373440 473169920 ⟨⟨250733748969, 250733748974⟩, ⟨238144975404, 263652774358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 138936320 141557760 461373440 473169920 ⟨⟨247333893146, 247333893155⟩, ⟨234892205507, 260102158802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 138936320 473169920 484966400 ⟨⟨255966512366, 255966512371⟩, ⟨243325456132, 268933451255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 473169920 484966400 ⟨⟨252521631161, 252521631171⟩, ⟨240026513282, 265339184798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 144179200 461373440 473169920 ⟨⟨243975868562, 243975868572⟩, ⟨231678607770, 256596073157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 144179200 146800640 461373440 473169920 ⟨⟨240658496734, 240658496745⟩, ⟨228503079786, 253133263315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 141557760 144179200 473169920 484966400 ⟨⟨249118229869, 249118229879⟩, ⟨236766471413, 261789008237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 144179200 146800640 473169920 484966400 ⟨⟨245755151993, 245755152004⟩, ⟨233544246459, 258281693419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 138936320 484966400 496762880 ⟨⟨261167519842, 261167519847⟩, ⟨248474963890, 274181592814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 138936320 141557760 484966400 496762880 ⟨⟨257678538847, 257678538858⟩, ⟨245130758120, 270544612794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 138936320 496762880 508559360 ⟨⟨266337827531, 266337827537⟩, ⟨253594518640, 279398290998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 138936320 141557760 496762880 508559360 ⟨⟨262805630929, 262805630939⟩, ⟨250205920090, 275719491919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 141557760 144179200 484966400 496762880 ⟨⟨254230669561, 254230669571⟩, ⟨241825164298, 266951267117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 144179200 146800640 484966400 496762880 ⟨⟨250822777342, 250822777353⟩, ⟨238557116695, 263400353292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 141557760 144179200 496762880 508559360 ⟨⟨259314162330, 259314162340⟩, ⟨246855627949, 272083857476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 144179200 146800640 496762880 508559360 ⟨⟨255862308791, 255862308802⟩, ⟨243542594789, 268490210538⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 461373440 508559360 t = true :=
  ⟨_, (join_sr (m := 484966400) (by decide) (join_su (m := 141557760) (by decide) (join_sr (m := 473169920) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 138936320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 473169920) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 144179200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 141557760) (by decide) (join_sr (m := 496762880) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 138936320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 496762880) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 144179200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (11/20 : ℝ) (97/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  have e3 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
