-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_212336640_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:13:34.766401+00:00
-- url     : https://prove2.me/submissions/5c019578-eb8c-484e-839d-da5c5930ac94

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 81/320]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 210370560 142540800 143933440 ⟨⟨55538092643, 55538092650⟩, ⟨53992683528, 57093537272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 210370560 143933440 145326080 ⟨⟨56058615073, 56058615079⟩, ⟨54511229476, 57616040252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 210370560 211025920 142540800 143933440 ⟨⟨55297674842, 55297674848⟩, ⟨53755873816, 56849471947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 210370560 211025920 143933440 145326080 ⟨⟨55816097460, 55816097465⟩, ⟨54272325256, 57369869865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 210370560 145326080 146718720 ⟨⟨56578798163, 56578798168⟩, ⟨55029437477, 58138202478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 210370560 146718720 148111360 ⟨⟨57098642843, 57098642849⟩, ⟨55547308462, 58660024887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 210370560 211025920 145326080 146718720 ⟨⟨56334184748, 56334184753⟩, ⟨54788442734, 57889931069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 210370560 211025920 146718720 148111360 ⟨⟨56851937625, 56851937630⟩, ⟨55304227162, 58409656482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 211025920 211681280 142540800 143933440 ⟨⟨55058077826, 55058077829⟩, ⟨53519865202, 56606247385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 211025920 211681280 143933440 145326080 ⟨⟨55574406007, 55574406010⟩, ⟨54034227502, 57124545622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 211681280 212336640 142540800 143933440 ⟨⟨54819295070, 54819295076⟩, ⟨53284651326, 56363856895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 211681280 212336640 143933440 145326080 ⟨⟨55333534154, 55333534161⟩, ⟨53796929817, 56880060801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 211025920 211681280 145326080 146718720 ⟨⟨56090402828, 56090402830⟩, ⟨54548259780, 57642511145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 211025920 211681280 146718720 148111360 ⟨⟨56606069193, 56606069196⟩, ⟨55061962936, 58160144859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 211681280 212336640 145326080 146718720 ⟨⟨55847445808, 55847445814⟩, ⟨54308882187, 57395935951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 211681280 212336640 146718720 148111360 ⟨⟨56361030920, 56361030926⟩, ⟨54820509322, 57911483235⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 212336640 142540800 148111360 t = true :=
  ⟨_, (join_su (m := 211025920) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 210370560) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 143933440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 210370560) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 146718720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 145326080) (by decide) (join_su (m := 211681280) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 143933440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 211681280) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 146718720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (81/320 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
