-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_245104640_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:58.114532+00:00
-- url     : https://prove2.me/submissions/036504b1-72c1-42cf-81c3-3d95ea913e3c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 187/640]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244121600 159252480 160645120 ⟨⟨49054045921, 49054045926⟩, ⟨48233935321, 49877136135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244121600 244449280 159252480 160645120 ⟨⟨48940207967, 48940207972⟩, ⟨48121108007, 49762281731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244121600 160645120 162037760 ⟨⟨49470160313, 49470160318⟩, ⟨48649124877, 50294176760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244121600 244449280 160645120 162037760 ⟨⟨49355404573, 49355404579⟩, ⟨48535381169, 50178403187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 244449280 244776960 159252480 160645120 ⟨⟨48826519394, 48826519399⟩, ⟨48008427868, 49647578938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 244776960 245104640 159252480 160645120 ⟨⟨48712979652, 48712979654⟩, ⟨47895894362, 49533027186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 244776960 160645120 162037760 ⟨⟨49240799111, 49240799116⟩, ⟨48421785530, 50062782119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244776960 245104640 160645120 162037760 ⟨⟨49126343371, 49126343374⟩, ⟨48308337414, 49947312987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244121600 162037760 163430400 ⟨⟨49886101496, 49886101502⟩, ⟨49064141495, 50711043904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244121600 244449280 162037760 163430400 ⟨⟨49770429101, 49770429107⟩, ⟨48949482518, 50594352295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244121600 163430400 164823040 ⟨⟨50301869870, 50301869875⟩, ⟨49478985573, 51127737968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244121600 244449280 163430400 164823040 ⟨⟨50185281945, 50185281952⟩, ⟨49363412449, 51010129451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 244449280 244776960 162037760 163430400 ⟨⟨49654907872, 49654907878⟩, ⟨48834972498, 50477814081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 244776960 245104640 162037760 163430400 ⟨⟨49539537253, 49539537255⟩, ⟨48720610886, 50361428690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 244449280 244776960 163430400 164823040 ⟨⟨50068846071, 50068846076⟩, ⟨49247989163, 50892675216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 244776960 245104640 163430400 164823040 ⟨⟨49952561685, 49952561687⟩, ⟨49132715165, 50775374684⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 245104640 159252480 164823040 t = true :=
  ⟨_, (join_sr (m := 162037760) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 160645120) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244121600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 160645120) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 244776960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 244449280) (by decide) (join_sr (m := 163430400) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244121600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163430400) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 244776960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (187/640 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
