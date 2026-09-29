-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_250347520_r125829120_128614400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:46:14.030558+00:00
-- url     : https://prove2.me/submissions/490f0882-cdba-4e45-aa4a-ff2d010efd16

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 191/640]`, `ρ ∈ [3/20, 157/1024]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249364480 125829120 126525440 ⟨⟨37464358947, 37464358952⟩, ⟨36793811396, 38136913986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249036800 249364480 126525440 127221760 ⟨⟨37667091306, 37667091310⟩, ⟨36996123488, 38340067388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249364480 249692160 125829120 126525440 ⟨⟨37375088326, 37375088333⟩, ⟨36705194934, 38046985906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249364480 249692160 126525440 127221760 ⟨⟨37577355621, 37577355626⟩, ⟨36907042568, 38249673638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 249364480 127221760 127918080 ⟨⟨37869782488, 37869782493⟩, ⟨37198394431, 38543179589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 249036800 249364480 127918080 128614400 ⟨⟨38072432541, 38072432547⟩, ⟨37400624270, 38746250633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249364480 249692160 127221760 127918080 ⟨⟨37779582017, 37779582022⟩, ⟨37108849330, 38452320447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249364480 249692160 127918080 128614400 ⟨⟨37981767561, 37981767565⟩, ⟨37310615266, 38654926378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249692160 250019840 125829120 126525440 ⟨⟨37285936088, 37285936091⟩, ⟨36616695302, 37957177767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249692160 250019840 126525440 127221760 ⟨⟨37487738815, 37487738816⟩, ⟨36818078975, 38159400326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250019840 250347520 125829120 126525440 ⟨⟨37196901779, 37196901784⟩, ⟨36528312052, 37867489120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250019840 250347520 126525440 127221760 ⟨⟨37398240432, 37398240437⟩, ⟨36729232258, 38069247003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249692160 250019840 127221760 127918080 ⟨⟨37689500919, 37689500921⟩, ⟨37019422050, 38361582239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 249692160 250019840 127918080 128614400 ⟨⟨37891222446, 37891222449⟩, ⟨37220724575, 38563723550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250019840 250347520 127221760 127918080 ⟨⟨37599538740, 37599538745⟩, ⟨36930112140, 38270964514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250019840 250347520 127918080 128614400 ⟨⟨37800796744, 37800796749⟩, ⟨37130951745, 38472641700⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 250347520 125829120 128614400 t = true :=
  ⟨_, (join_su (m := 249692160) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 249364480) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126525440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 249364480) (by decide) (join_sr (m := 127918080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 127918080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 127221760) (by decide) (join_su (m := 250019840) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126525440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 250019840) (by decide) (join_sr (m := 127918080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 127918080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (191/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (157/1024 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((128614400 : ℤ) : ℝ) / (D : ℝ)) = (157/1024 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
