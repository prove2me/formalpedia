-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_62914560_r111411200_123535360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:10:22.499253+00:00
-- url     : https://prove2.me/submissions/b421f509-1ddd-4794-9983-4d7cc2e33691

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 3/40]`, `ρ ∈ [17/128, 377/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 58720256 59768832 111411200 114442240 ⟨⟨136421108756, 136421108768⟩, ⟨129714890562, 143287739387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 58720256 59768832 114442240 117473280 ⟨⟨139367705198, 139367705209⟩, ⟨132655881270, 146238315081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 59768832 60817408 111411200 114442240 ⟨⟨134942304911, 134942304923⟩, ⟨128317574231, 141724115673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 59768832 60817408 114442240 117473280 ⟨⟨137868386996, 137868387007⟩, ⟨131237651542, 144654643969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 58720256 59768832 117473280 120504320 ⟨⟨142287500894, 142287500905⟩, ⟨135570480190, 149161699709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 58720256 59768832 120504320 123535360 ⟨⟨145181061988, 145181061999⟩, ⟨138459236658, 152058476074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 59768832 60817408 117473280 120504320 ⟨⟨140768249192, 140768249204⟩, ⟨134131911010, 147558567629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 59768832 60817408 120504320 123535360 ⟨⟨143642438231, 143642438242⟩, ⟨137000883188, 150436449440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 60817408 61865984 111411200 114442240 ⟨⟨133493296522, 133493296533⟩, ⟨126947967014, 140192483397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 60817408 61865984 114442240 117473280 ⟨⟨136398999520, 136398999532⟩, ⟨129847291619, 143103070796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 61865984 62914560 111411200 114442240 ⟨⟨132073104128, 132073104139⟩, ⟨125605168886, 138691778819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 61865984 62914560 114442240 117473280 ⟨⟨134958566690, 134958566703⟩, ⟨128483903300, 141582536951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 60817408 61865984 117473280 120504320 ⟨⟨139279048911, 139279048923⟩, ⟨132721357681, 145987625581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 60817408 61865984 120504320 123535360 ⟨⟨142133972778, 142133972789⟩, ⟨135570677712, 148846691302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 61865984 62914560 117473280 120504320 ⟨⟨137818927752, 137818927763⟩, ⟨131337924259, 144447820449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 61865984 62914560 120504320 123535360 ⟨⟨140654697478, 140654697492⟩, ⟨134167726935, 147288154381⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 62914560 111411200 123535360 t = true :=
  ⟨_, (join_su (m := 60817408) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 59768832) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114442240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 59768832) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 120504320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 117473280) (by decide) (join_su (m := 61865984) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114442240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 61865984) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 120504320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (3/40 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (377/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
