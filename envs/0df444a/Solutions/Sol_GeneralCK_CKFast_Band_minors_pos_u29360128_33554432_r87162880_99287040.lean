-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u29360128_33554432_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:23:16.97851+00:00
-- url     : https://prove2.me/submissions/c6c0c82d-79fd-430b-8b5f-733772e4a1d2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/200, 1/25]`, `ρ ∈ [133/1280, 303/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 29360128 30408704 87162880 90193920 ⟨⟨165782676121, 165782676143⟩, ⟨155203438297, 176753469299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 29360128 30408704 90193920 93224960 ⟨⟨169787808592, 169787808614⟩, ⟨159233012671, 180725993910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 30408704 31457280 87162880 90193920 ⟨⟨162951636605, 162951636623⟩, ⟨152598307635, 173682437472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 30408704 31457280 90193920 93224960 ⟨⟨166926665625, 166926665642⟩, ⟨156594797634, 177628359317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 29360128 30408704 93224960 96256000 ⟨⟨173726041925, 173726041942⟩, ⟨163196448413, 184631087384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 29360128 30408704 96256000 99287040 ⟨⟨177599779441, 177599779463⟩, ⟨167096066899, 188471227322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 30408704 31457280 93224960 96256000 ⟨⟨170836636009, 170836636031⟩, ⟨160527015539, 181508642782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 30408704 31457280 96256000 99287040 ⟨⟨174683839764, 174683839782⟩, ⟨164397174244, 185325652334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 31457280 32505856 87162880 90193920 ⟨⟨160219980653, 160219980674⟩, ⟨150082606565, 170721524688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 31457280 32505856 90193920 93224960 ⟨⟨164164588174, 164164588194⟩, ⟨154045941512, 174640237097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 32505856 33554432 87162880 90193920 ⟨⟨157582179823, 157582179839⟩, ⟨147651452176, 167864499587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 32505856 33554432 90193920 93224960 ⟨⟨161496130716, 161496130732⟩, ⟨151581621304, 171755505771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 31457280 32505856 93224960 96256000 ⟨⟨168045924024, 168045924041⟩, ⟨157946810832, 178495059179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 31457280 32505856 96256000 99287040 ⟨⟨171866174741, 171866174762⟩, ⟨161787324832, 182288247962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 32505856 33554432 93224960 96256000 ⟨⟨165348543868, 165348543889⟩, ⟨155451072646, 175584324282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 32505856 33554432 96256000 99287040 ⟨⟨169141505931, 169141505947⟩, ⟨159261819509, 179353110131⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 29360128 33554432 87162880 99287040 t = true :=
  ⟨_, (join_su (m := 31457280) (by decide) (join_sr (m := 93224960) (by decide) (join_su (m := 30408704) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 90193920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 30408704) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 96256000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 93224960) (by decide) (join_su (m := 32505856) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 90193920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 32505856) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 96256000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/200 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
