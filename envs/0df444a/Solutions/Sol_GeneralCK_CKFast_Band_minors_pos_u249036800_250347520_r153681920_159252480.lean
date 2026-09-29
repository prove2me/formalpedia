-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_250347520_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:26:54.788742+00:00
-- url     : https://prove2.me/submissions/0580e144-8373-42eb-9838-e6e8e202ffee

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 191/640]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249364480 153681920 155074560 ⟨⟨45642550250, 45642550256⟩, ⟨44841962522, 46446020892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249364480 249692160 153681920 155074560 ⟨⟨45534662783, 45534662788⟩, ⟨44735045809, 46337157127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249364480 155074560 156467200 ⟨⟨46044712793, 46044712800⟩, ⟨45243221511, 46849088478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249364480 249692160 155074560 156467200 ⟨⟨45935917353, 45935917358⟩, ⟨45135398211, 46739315360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249692160 250019840 153681920 155074560 ⟨⟨45426912634, 45426912637⟩, ⟨44628264340, 46228432773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250019840 250347520 153681920 155074560 ⟨⟨45319299292, 45319299297⟩, ⟨44521617607, 46119847317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250019840 155074560 156467200 ⟨⟨45827260106, 45827260108⟩, ⟨45027711028, 46629682527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250019840 250347520 155074560 156467200 ⟨⟨45718740537, 45718740542⟩, ⟨44920159450, 46520189465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249364480 156467200 157859840 ⟨⟨46446718095, 46446718100⟩, ⟨45644323463, 47251998617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249364480 249692160 156467200 157859840 ⟨⟨46337015731, 46337015736⟩, ⟨45535594622, 47141317198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249364480 157859840 159252480 ⟨⟨46848566508, 46848566513⟩, ⟨46045268730, 47654751660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249364480 249692160 157859840 159252480 ⟨⟨46737958266, 46737958271⟩, ⟨45935635389, 47543162990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249692160 250019840 156467200 157859840 ⟨⟨46227452429, 46227452431⟩, ⟨45427002763, 47030776934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250019840 250347520 156467200 157859840 ⟨⟨46118027668, 46118027675⟩, ⟨45318547375, 46920377308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249692160 250019840 157859840 159252480 ⟨⟨46627489948, 46627489951⟩, ⟨45826139892, 47431716339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250019840 250347520 157859840 159252480 ⟨⟨46517161034, 46517161039⟩, ⟨45716781723, 47320411189⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 250347520 153681920 159252480 t = true :=
  ⟨_, (join_sr (m := 156467200) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 155074560) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249364480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 155074560) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250019840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249692160) (by decide) (join_sr (m := 157859840) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249364480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 157859840) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250019840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (191/640 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
