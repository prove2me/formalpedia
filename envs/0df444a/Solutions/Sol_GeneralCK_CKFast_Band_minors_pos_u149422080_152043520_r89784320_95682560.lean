-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u149422080_152043520_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:00:02.88925+00:00
-- url     : https://prove2.me/submissions/b48acd4a-adb8-42fb-babc-9a3cd14fbcef

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [57/320, 29/160]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 149422080 150077440 89784320 91258880 ⟨⟨53466553972, 53466553978⟩, ⟨51547164453, 55402125512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149422080 150077440 91258880 92733440 ⟨⟨54294079602, 54294079608⟩, ⟨52371761906, 56232572352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 150077440 150732800 89784320 91258880 ⟨⟨53224293723, 53224293730⟩, ⟨51311247371, 55153423615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 150077440 150732800 91258880 92733440 ⟨⟨54048405462, 54048405469⟩, ⟨52132440492, 55980447275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 149422080 150077440 92733440 94208000 ⟨⟨55120344254, 55120344260⟩, ⟨53195107371, 57061749168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 149422080 150077440 94208000 95682560 ⟨⟨55945353556, 55945353564⟩, ⟨54017206425, 57889661638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 150077440 150732800 92733440 94208000 ⟨⟨54871271011, 54871271017⟩, ⟨52952396272, 56806215835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 150077440 150732800 94208000 95682560 ⟨⟨55692895900, 55692895906⟩, ⟨53771120192, 57630734879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 150732800 151388160 89784320 91258880 ⟨⟨52983422816, 52983422823⟩, ⟨51076670875, 54906160851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 150732800 151388160 91258880 92733440 ⟨⟨53804136393, 53804136399⟩, ⟨51894475369, 55729777073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 151388160 152043520 89784320 91258880 ⟨⟨52743926426, 52743926432⟩, ⟨50843420710, 54660321806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 151388160 152043520 91258880 92733440 ⟨⟨53561257430, 53561257436⟩, ⟨51657852145, 55480546199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 150732800 151388160 92733440 94208000 ⟨⟨54623618384, 54623618392⟩, ⟨52711056991, 56552152940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 150732800 151388160 94208000 95682560 ⟨⟨55441874231, 55441874239⟩, ⟨53526421130, 57373293943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 151388160 152043520 92733440 94208000 ⟨⟨54377371280, 54377371288⟩, ⟨52471075005, 56299544804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 151388160 152043520 94208000 95682560 ⟨⟨55192273323, 55192273331⟩, ⟨53283094583, 57117323018⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 149422080 152043520 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 150732800) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 150077440) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 91258880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 150077440) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 94208000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 92733440) (by decide) (join_su (m := 151388160) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 91258880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 151388160) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 94208000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (57/320 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
