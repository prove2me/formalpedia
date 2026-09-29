-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_54525952_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:59:56.255462+00:00
-- url     : https://prove2.me/submissions/af04de6b-6eb7-4612-be86-186fcb859683

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 13/200]`, `ρ ∈ [133/1280, 303/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 51380224 87162880 90193920 ⟨⟨123286302011, 123286302024⟩, ⟨115871801832, 130912342115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 51380224 90193920 93224960 ⟨⟨126687923423, 126687923439⟩, ⟨119267510709, 134317268194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 51380224 52428800 87162880 90193920 ⟨⟨121728231127, 121728231140⟩, ⟨114420431157, 129242219876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 51380224 52428800 90193920 93224960 ⟨⟨125101606666, 125101606681⟩, ⟨117787299640, 132619620688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 51380224 93224960 96256000 ⟨⟨130050467733, 130050467748⟩, ⟨122624832631, 137682464482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 50331648 51380224 96256000 99287040 ⟨⟨133374928846, 133374928858⟩, ⟨125944726723, 141008959304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 51380224 52428800 93224960 96256000 ⟨⟨128436886796, 128436886809⟩, ⟨121116748241, 135958285028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 51380224 52428800 96256000 99287040 ⟨⟨131735025845, 131735025860⟩, ⟨124409698041, 139259200178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 52428800 53477376 87162880 90193920 ⟨⟨120208239797, 120208239809⟩, ⟨113003885264, 127613645023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 52428800 53477376 90193920 93224960 ⟨⟨123553648348, 123553648364⟩, ⟨116342236841, 130963747471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 53477376 54525952 87162880 90193920 ⟨⟨118724834945, 118724834957⟩, ⟨111620818441, 126024965741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 53477376 54525952 90193920 93224960 ⟨⟨122042558586, 122042558598⟩, ⟨114930976537, 129348003692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 52428800 53477376 93224960 96256000 ⟨⟨126861913171, 126861913186⟩, ⟨119644105574, 134276077021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 52428800 53477376 96256000 99287040 ⟨⟨130133950874, 130133950887⟩, ⟨122910376294, 137551581823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 53477376 54525952 93224960 96256000 ⟨⟨125324061221, 125324061234⟩, ⟨118205559914, 132634203552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 53477376 54525952 96256000 99287040 ⟨⟨128570223494, 128570223509⟩, ⟨121445418831, 135884476159⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 54525952 87162880 99287040 t = true :=
  ⟨_, (join_su (m := 52428800) (by decide) (join_sr (m := 93224960) (by decide) (join_su (m := 51380224) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 90193920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 51380224) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 96256000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 93224960) (by decide) (join_su (m := 53477376) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 90193920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 53477376) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 96256000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (13/200 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
