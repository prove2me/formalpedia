-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_149422080_r113377280_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:08:39.967979+00:00
-- url     : https://prove2.me/submissions/a9f02fc3-3970-4661-890b-63e08d35d475

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 57/320]`, `ρ ∈ [173/1280, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 147456000 113377280 114851840 ⟨⟨67755926981, 67755926988⟩, ⟨65764316121, 69763987985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 147456000 114851840 116326400 ⟨⟨68576820330, 68576820337⟩, ⟨66582389199, 70587692601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 147456000 148111360 113377280 114851840 ⟨⟨67454113352, 67454113360⟩, ⟨65469183729, 69455395011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 147456000 148111360 114851840 116326400 ⟨⟨68271765171, 68271765179⟩, ⟨66284022695, 70275850970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 147456000 116326400 117800960 ⟨⟨69396484000, 69396484008⟩, ⟨67399241281, 71410158799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 147456000 117800960 119275520 ⟨⟨70214923480, 70214923488⟩, ⟨68214877806, 72231392121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 147456000 148111360 116326400 117800960 ⟨⟨69088201305, 69088201311⟩, ⟨67097654532, 71095082634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 147456000 148111360 117800960 119275520 ⟨⟨69903427153, 69903427159⟩, ⟨67910084587, 71913095455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 148111360 148766720 113377280 114851840 ⟨⟨67153989437, 67153989443⟩, ⟨65175689854, 69148543956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 148111360 148766720 114851840 116326400 ⟨⟨67968413196, 67968413204⟩, ⟨65987308190, 69965764713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 148766720 149422080 113377280 114851840 ⟨⟨66855537557, 66855537562⟩, ⟨64883817407, 68843416534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 148766720 149422080 114851840 116326400 ⟨⟨67666746625, 67666746630⟩, ⟨65692228494, 69657415439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 148111360 148766720 116326400 117800960 ⟨⟨68781635102, 68781635109⟩, ⟨66797733102, 70781775133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 148111360 148766720 117800960 119275520 ⟨⟨69593660465, 69593660472⟩, ⟨67606969852, 71596580580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 148766720 149422080 116326400 117800960 ⟨⟨68476767509, 68476767514⟩, ⟨66499459703, 70470217806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 148766720 149422080 117800960 119275520 ⟨⟨69285605437, 69285605442⟩, ⟨67305516209, 71281828908⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 149422080 113377280 119275520 t = true :=
  ⟨_, (join_su (m := 148111360) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 147456000) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114851840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 147456000) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 117800960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 116326400) (by decide) (join_su (m := 148766720) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114851840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 148766720) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 117800960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (57/320 : ℝ) →
    rho ∈ Set.Icc (173/1280 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e2 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
