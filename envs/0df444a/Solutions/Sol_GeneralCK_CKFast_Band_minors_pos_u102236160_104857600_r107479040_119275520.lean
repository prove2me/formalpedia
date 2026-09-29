-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u102236160_104857600_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:39:02.40698+00:00
-- url     : https://prove2.me/submissions/f7122f85-9932-47e8-b569-8a3b834357cf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/320, 1/8]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 102236160 102891520 107479040 110428160 ⟨⟨89729720135, 89729720143⟩, ⟨86396689620, 93106863385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 102891520 103546880 107479040 110428160 ⟨⟨89267992798, 89267992800⟩, ⟨85951776663, 92627929111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 102236160 102891520 110428160 113377280 ⟨⟨91905347285, 91905347295⟩, ⟨88564934477, 95289670264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 102891520 103546880 110428160 113377280 ⟨⟨91434511489, 91434511493⟩, ⟨88110913507, 94801631389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 103546880 104202240 107479040 110428160 ⟨⟨88810020344, 88810020352⟩, ⟨85510444022, 92152929806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104202240 104857600 107479040 110428160 ⟨⟨88355750320, 88355750328⟩, ⟨85072642007, 91681810128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 103546880 104202240 110428160 113377280 ⟨⟨90967478885, 90967478893⟩, ⟨87660521888, 94317574968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 104202240 104857600 110428160 113377280 ⟨⟨90504196639, 90504196649⟩, ⟨87213709532, 93837445307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 102236160 102891520 113377280 116326400 ⟨⟨94069905507, 94069905516⟩, ⟨90722236423, 97461282627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 102891520 103546880 113377280 116326400 ⟨⟨93590095309, 93590095315⟩, ⟨90259239705, 96964274973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 102236160 102891520 116326400 119275520 ⟨⟨96223538886, 96223538897⟩, ⟨92868736880, 99621847244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 102891520 103546880 116326400 119275520 ⟨⟨95734885730, 95734885736⟩, ⟨92396894123, 99116003954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 103546880 104202240 113377280 116326400 ⟨⟨93114134795, 93114134806⟩, ⟨89799919584, 96471295415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 104202240 104857600 113377280 116326400 ⟨⟨92641970786, 92641970796⟩, ⟨89344225596, 95982287941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 103546880 104202240 116326400 119275520 ⟨⟨95250126983, 95250126993⟩, ⟨91928773465, 98614232615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 104202240 104857600 116326400 119275520 ⟨⟨94769209150, 94769209161⟩, ⟨91464324104, 98116476930⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 102236160 104857600 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 103546880) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 102891520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 102891520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 104202240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 104202240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 103546880) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 102891520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 102891520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 104202240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 104202240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/320 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((102236160 : ℤ) : ℝ) / (D : ℝ)) = (39/320 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
