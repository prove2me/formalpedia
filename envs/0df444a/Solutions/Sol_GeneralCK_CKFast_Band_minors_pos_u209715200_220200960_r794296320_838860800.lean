-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r794296320_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:14:43.438243+00:00
-- url     : https://prove2.me/submissions/3314852b-47f0-4533-94f6-b44bb9679489

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [303/320, 1]` by 17 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 794296320 805437440 ⟨⟨274241677384, 274241677394⟩, ⟨263420795757, 285276798618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212336640 214958080 794296320 805437440 ⟨⟨270422718404, 270422718414⟩, ⟨259692285101, 281367148930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 212336640 805437440 816578560 ⟨⟨277694228804, 277694228813⟩, ⟨266818107169, 288783563213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 805437440 816578560 ⟨⟨273836904922, 273836904932⟩, ⟨263051079745, 284835780436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 217579520 794296320 805437440 ⟨⟨266619421721, 266619421725⟩, ⟨255978886051, 277473674364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 217579520 220200960 794296320 799866880 ⟨⟨261996650687, 261996650696⟩, ⟨252785654606, 271367101224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 217579520 220200960 799866880 805437440 ⟨⟨263666031779, 263666031789⟩, ⟨254428516873, 273062795092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214958080 217579520 805437440 816578560 ⟨⟨269995010559, 269995010562⟩, ⟨259298956315, 280903912924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 220200960 805437440 816578560 ⟨⟨266168231968, 266168231978⟩, ⟨255561428050, 276987643255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 209715200 212336640 816578560 827719680 ⟨⟨281142460035, 281142460044⟩, ⟨270211157721, 292285922642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 212336640 214958080 816578560 827719680 ⟨⟨277246919694, 277246919705⟩, ⟨266405756231, 288300161371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 209715200 212336640 827719680 838860800 ⟨⟨284586554392, 284586554403⟩, ⟨273600126346, 295784064321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 212336640 214958080 827719680 838860800 ⟨⟨280652939010, 280652939020⟩, ⟨269756486668, 291760471933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214958080 217579520 816578560 827719680 ⟨⟨273366573305, 273366573310⟩, ⟨262615048339, 284330052746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 220200960 816578560 827719680 ⟨⟨269501112977, 269501112988⟩, ⟨258838730500, 280375285779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214958080 217579520 827719680 838860800 ⟨⟨276734279408, 276734279413⟩, ⟨265927327579, 287752266996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 217579520 220200960 827719680 838860800 ⟨⟨272830273517, 272830273526⟩, ⟨262112350808, 283759144910⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 794296320 838860800 t = true :=
  ⟨_, (join_sr (m := 816578560) (by decide) (join_su (m := 214958080) (by decide) (join_sr (m := 805437440) (by decide) (join_su (m := 212336640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 212336640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 805437440) (by decide) (join_su (m := 217579520) (by decide) (leaf_ok cell4) (join_sr (m := 799866880) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 217579520) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 214958080) (by decide) (join_sr (m := 827719680) (by decide) (join_su (m := 212336640) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 212336640) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 827719680) (by decide) (join_su (m := 217579520) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 217579520) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (303/320 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
