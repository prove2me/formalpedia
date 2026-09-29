-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u245104640_246415360_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:58.056398+00:00
-- url     : https://prove2.me/submissions/0761cfa4-6793-4a7c-b0e1-53957a04546f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [187/640, 47/160]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 245104640 245432320 159252480 160645120 ⟨⟨48599588184, 48599588189⟩, ⟨47783506940, 49418625924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 245432320 245760000 159252480 160645120 ⟨⟨48486344445, 48486344450⟩, ⟨47671265064, 49304374586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 245104640 245432320 160645120 162037760 ⟨⟨49012036795, 49012036800⟩, ⟨48195036270, 49831995234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 245432320 245760000 160645120 162037760 ⟨⟨48897878834, 48897878840⟩, ⟨48081881560, 49716828294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245760000 246087680 159252480 160645120 ⟨⟨48373247887, 48373247892⟩, ⟨47559168194, 49190272624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246087680 246415360 159252480 160645120 ⟨⟨48260297964, 48260297969⟩, ⟨47447215791, 49076319483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245760000 246087680 160645120 162037760 ⟨⟨48783868938, 48783868943⟩, ⟨47968872736, 49601811615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 246087680 246415360 160645120 162037760 ⟨⟨48670006559, 48670006564⟩, ⟨47856009259, 49486944640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245432320 162037760 163430400 ⟨⟨49424316680, 49424316685⟩, ⟨48606397128, 50245195562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245432320 245760000 162037760 163430400 ⟨⟨49309245603, 49309245609⟩, ⟨48492330683, 50129114131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 245432320 163430400 164823040 ⟨⟨49836428223, 49836428230⟩, ⟨49017589897, 50658227297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245432320 245760000 163430400 164823040 ⟨⟨49720445134, 49720445140⟩, ⟨48902612816, 50541232481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245760000 246087680 162037760 163430400 ⟨⟨49194323469, 49194323475⟩, ⟨48378411001, 50013183839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 246087680 246415360 162037760 163430400 ⟨⟨49079549727, 49079549732⟩, ⟨48264637540, 49897404128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246087680 163430400 164823040 ⟨⟨49604611859, 49604611865⟩, ⟨48787783368, 50424389677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 246087680 246415360 163430400 164823040 ⟨⟨49488927846, 49488927851⟩, ⟨48673101010, 50307698325⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 245104640 246415360 159252480 164823040 t = true :=
  ⟨_, (join_sr (m := 162037760) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 160645120) (by decide) (join_su (m := 245432320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 245432320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 160645120) (by decide) (join_su (m := 246087680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 246087680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 245760000) (by decide) (join_sr (m := 163430400) (by decide) (join_su (m := 245432320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 245432320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163430400) (by decide) (join_su (m := 246087680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 246087680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (187/640 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
