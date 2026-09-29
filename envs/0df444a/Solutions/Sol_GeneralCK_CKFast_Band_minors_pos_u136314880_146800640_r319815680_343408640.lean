-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r319815680_343408640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:44:45.352984+00:00
-- url     : https://prove2.me/submissions/48bb501e-2a3e-49cd-9d17-55ea755d0cf0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [61/160, 131/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 319815680 325713920 ⟨⟨183594119334, 183594119337⟩, ⟨173977766613, 193460802080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 138936320 325713920 331612160 ⟨⟨186461236219, 186461236224⟩, ⟨176813911838, 196357714592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 138936320 141557760 319815680 325713920 ⟨⟨180840153792, 180840153801⟩, ⟨171340710301, 190585960457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 325713920 331612160 ⟨⟨183676757959, 183676757969⟩, ⟨174146068621, 193452717849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 138936320 331612160 337510400 ⟨⟨189316171697, 189316171702⟩, ⟨179638158500, 199242158861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 138936320 337510400 343408640 ⟨⟨192159130122, 192159130126⟩, ⟨182450704599, 202114345704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 138936320 141557760 331612160 337510400 ⟨⟨186501598029, 186501598039⟩, ⟨176939935774, 196307433677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 138936320 141557760 337510400 343408640 ⟨⟨189314868606, 189314868616⟩, ⟨179722500386, 199150308639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 144179200 319815680 325713920 ⟨⟨178130240908, 178130240916⟩, ⟨168744905435, 187758077979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 141557760 144179200 325713920 331612160 ⟨⟨180936346753, 180936346763⟩, ⟨171519523669, 190594658060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 144179200 146800640 319815680 325713920 ⟨⟨175462944758, 175462944766⟩, ⟨166189016921, 184975614310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 144179200 146800640 325713920 331612160 ⟨⟨178238575663, 178238575673⟩, ⟨168932948888, 187782006087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 141557760 144179200 331612160 337510400 ⟨⟨183731094097, 183731094106⟩, ⟨174283046482, 193419611555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 141557760 144179200 337510400 343408640 ⟨⟨186514668239, 186514668249⟩, ⟨177035653546, 196233129499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 144179200 146800640 331612160 337510400 ⟨⟨181003242191, 181003242200⟩, ⟨171666169793, 190577174763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 144179200 146800640 337510400 343408640 ⟨⟨183757120763, 183757120771⟩, ⟨174388850765, 193361302164⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 319815680 343408640 t = true :=
  ⟨_, (join_su (m := 141557760) (by decide) (join_sr (m := 331612160) (by decide) (join_su (m := 138936320) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 325713920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 138936320) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 337510400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 331612160) (by decide) (join_su (m := 144179200) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 325713920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 144179200) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 337510400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (61/160 : ℝ) (131/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  have e3 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
