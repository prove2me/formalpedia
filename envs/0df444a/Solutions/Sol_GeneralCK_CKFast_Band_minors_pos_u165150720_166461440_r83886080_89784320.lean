-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_166461440_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:18:46.25971+00:00
-- url     : https://prove2.me/submissions/d17ac095-e9d0-4422-b445-83921edc0075

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 127/640]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 165150720 165478400 83886080 85360640 ⟨⟨45049773494, 45049773500⟩, ⟨43946603343, 46158490589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165478400 165806080 83886080 85360640 ⟨⟨44949401417, 44949401424⟩, ⟨43848093174, 46056239581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165150720 165478400 85360640 86835200 ⟨⟨45804067916, 45804067922⟩, ⟨44699340413, 46914339931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165478400 165806080 85360640 86835200 ⟨⟨45702134316, 45702134322⟩, ⟨44599271602, 46810524557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165806080 166133760 83886080 85360640 ⟨⟨44849289219, 44849289225⟩, ⟨43749836560, 45954254857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 166133760 166461440 83886080 85360640 ⟨⟨44749435602, 44749435605⟩, ⟨43651832240, 45852535078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165806080 166133760 85360640 86835200 ⟨⟨45600463952, 45600463958⟩, ⟨44499459699, 46706978833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 166133760 166461440 85360640 86835200 ⟨⟨45499055514, 45499055517⟩, ⟨44399903430, 46603701404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 165150720 165478400 86835200 88309760 ⟨⟨46557393419, 46557393427⟩, ⟨45451112813, 47669216094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165478400 165806080 86835200 88309760 ⟨⟨46453904008, 46453904015⟩, ⟨45349491037, 47563842103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 165478400 88309760 89784320 ⟨⟨47309753859, 47309753866⟩, ⟨46201924370, 48423122953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 165478400 165806080 88309760 89784320 ⟨⟨47204714319, 47204714325⟩, ⟨46098755280, 48316196060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165806080 166133760 86835200 88309760 ⟨⟨46350681160, 46350681166⟩, ⟨45248129492, 47458741091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166133760 166461440 86835200 88309760 ⟨⟨46247723548, 46247723551⟩, ⟨45147026888, 47353911690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165806080 166133760 88309760 89784320 ⟨⟨47099944632, 47099944640⟩, ⟨45995849708, 48209545442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166133760 166461440 88309760 89784320 ⟨⟨46995443462, 46995443465⟩, ⟨45893206350, 48103169716⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 166461440 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 165806080) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 165478400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 165478400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 166133760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 166133760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 165806080) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 165478400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 165478400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 88309760) (by decide) (join_su (m := 166133760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 166133760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (127/640 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
