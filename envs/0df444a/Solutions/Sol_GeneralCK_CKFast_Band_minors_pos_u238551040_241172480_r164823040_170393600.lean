-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r164823040_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:15:37.51524+00:00
-- url     : https://prove2.me/submissions/0185a832-20fc-40a3-b8e6-73f4a91dc8d7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [503/2560, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 164823040 166215680 ⟨⟨52558736563, 52558736568⟩, ⟨51127398968, 53998706134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238551040 239206400 166215680 167608320 ⟨⟨52988429864, 52988429870⟩, ⟨51555346622, 54430150696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239206400 239861760 164823040 166215680 ⟨⟨52319005303, 52319005308⟩, ⟨50890617913, 53755996113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 166215680 167608320 ⟨⟨52746845246, 52746845253⟩, ⟨51316716820, 54185582735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239206400 167608320 169000960 ⟨⟨53417933471, 53417933476⟩, ⟨51983104991, 54861405145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238551040 239206400 169000960 170393600 ⟨⟨53847247832, 53847247837⟩, ⟨52410674521, 55292469927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239861760 167608320 169000960 ⟨⟨53174497912, 53174497917⟩, ⟨51742628842, 54614981674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239206400 239861760 169000960 170393600 ⟨⟨53601963738, 53601963743⟩, ⟨52168354417, 55044193371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240517120 164823040 166215680 ⟨⟨52079919542, 52079919549⟩, ⟨50654468238, 53513945893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239861760 240517120 166215680 167608320 ⟨⟨52505909770, 52505909777⟩, ⟨51078722034, 53941678225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 240517120 241172480 164823040 166215680 ⟨⟨51841474505, 51841474507⟩, ⟨50418945267, 53272550596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240517120 241172480 166215680 167608320 ⟨⟨52265618638, 52265618639⟩, ⟨50841357562, 53698432263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239861760 240517120 167608320 169000960 ⟨⟨52931715110, 52931715117⟩, ⟨51502791318, 54369225279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 240517120 169000960 170393600 ⟨⟨53357335995, 53357336001⟩, ⟨51926676524, 54796587490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 241172480 167608320 169000960 ⟨⟨52689580247, 52689580250⟩, ⟨51263587698, 54124131034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240517120 241172480 169000960 170393600 ⟨⟨53113359761, 53113359764⟩, ⟨51685636100, 54549647336⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 164823040 170393600 t = true :=
  ⟨_, (join_su (m := 239861760) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 166215680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 239206400) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 169000960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 167608320) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 166215680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 240517120) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 169000960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (503/2560 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
