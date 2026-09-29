-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_157286400_r201850880_213647360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:49:06.341091+00:00
-- url     : https://prove2.me/submissions/9b361275-8048-4ef0-8b38-1e4a12dc81da

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 3/16]`, `ρ ∈ [77/320, 163/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 152043520 153354240 201850880 204800000 ⟨⟨111413337659, 111413337668⟩, ⟨107246802485, 115640516977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 152043520 153354240 204800000 207749120 ⟨⟨112880561665, 112880561674⟩, ⟨108704569675, 117117123397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 153354240 154664960 201850880 204800000 ⟨⟨110501417451, 110501417455⟩, ⟨106360809455, 114702076640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 153354240 154664960 204800000 207749120 ⟨⟨111958732991, 111958732994⟩, ⟨107808685197, 116168761684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152043520 153354240 207749120 210698240 ⟨⟨114344331809, 114344331818⟩, ⟨110158926618, 118590231773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 152043520 153354240 210698240 213647360 ⟨⟨115804676012, 115804676019⟩, ⟨111609900775, 120059870486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 153354240 154664960 207749120 210698240 ⟨⟨113412664918, 113412664922⟩, ⟨109253219837, 117632020041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 153354240 154664960 210698240 213647360 ⟨⟨114863240361, 114863240363⟩, ⟨110694440058, 119091879282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 154664960 155975680 201850880 204800000 ⟨⟨109597780997, 109597781004⟩, ⟨105482753954, 113772276339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 154664960 155975680 204800000 207749120 ⟨⟨111045234168, 111045234175⟩, ⟨106920785378, 115229084953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 155975680 157286400 201850880 204800000 ⟨⟨108702279661, 108702279669⟩, ⟨104612494278, 112850960271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 155975680 157286400 204800000 207749120 ⟨⟨110139916278, 110139916286⟩, ⟨106040728180, 114297937166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154664960 155975680 207749120 210698240 ⟨⟨112489372650, 112489372659⟩, ⟨108355543535, 116682536890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154664960 155975680 210698240 213647360 ⟨⟨113930222799, 113930222806⟩, ⟨109787054357, 118132658927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 155975680 157286400 207749120 210698240 ⟨⟨111574305829, 111574305836⟩, ⟨107465755369, 115741626067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 155975680 157286400 210698240 213647360 ⟨⟨113005473915, 113005473922⟩, ⟨108887601046, 117182052992⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 157286400 201850880 213647360 t = true :=
  ⟨_, (join_su (m := 154664960) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 153354240) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 204800000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 153354240) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 210698240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 207749120) (by decide) (join_su (m := 155975680) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 204800000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 155975680) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 210698240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (163/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
