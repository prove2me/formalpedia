-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_241172480_r816578560_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:18:49.75422+00:00
-- url     : https://prove2.me/submissions/3f50086a-cc88-468a-a68b-09f170117ca2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 23/80]`, `ρ ∈ [623/640, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 233308160 816578560 822149120 ⟨⟨249602974668, 249602974677⟩, ⟨240606958490, 258758101792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 233308160 822149120 827719680 ⟨⟨251170305255, 251170305264⟩, ⟨242147691604, 260351932500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 235929600 816578560 822149120 ⟨⟨245830662559, 245830662568⟩, ⟨236897926652, 254922542005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233308160 235929600 822149120 827719680 ⟨⟨247378051164, 247378051174⟩, ⟨238418725357, 256496447375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 233308160 827719680 833290240 ⟨⟨252736874095, 252736874105⟩, ⟨243687661925, 261944997815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 233308160 833290240 838860800 ⟨⟨254302697588, 254302697599⟩, ⟨245226885560, 263537314403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 235929600 827719680 833290240 ⟨⟨248924707656, 248924707666⟩, ⟨239938789710, 258069618300⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 233308160 235929600 833290240 838860800 ⟨⟨250470647738, 250470647749⟩, ⟨241458135140, 259642070736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 238551040 816578560 822149120 ⟨⟨242071286835, 242071286844⟩, ⟨233201532120, 251100195795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 235929600 238551040 822149120 827719680 ⟨⟨243598636510, 243598636520⟩, ⟨234702308441, 252654069347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 241172480 816578560 822149120 ⟨⟨238324580995, 238324581006⟩, ⟨229517511966, 247290793643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 238551040 241172480 822149120 827719680 ⟨⟨239831797204, 239831797213⟩, ⟨230998180167, 248824531493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 235929600 238551040 827719680 833290240 ⟨⟨245125283026, 245125283035⟩, ⟨236202378195, 254207238708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235929600 238551040 833290240 838860800 ⟨⟨246651241413, 246651241422⟩, ⟨237701756151, 255759719143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 238551040 241172480 827719680 833290240 ⟨⟨241338338530, 241338338539⟩, ⟨232478168932, 250357594703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 238551040 241172480 833290240 838860800 ⟨⟨242844219349, 242844219358⟩, ⟨233957492386, 251889997872⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 241172480 816578560 838860800 t = true :=
  ⟨_, (join_su (m := 235929600) (by decide) (join_sr (m := 827719680) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 822149120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 822149120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 233308160) (by decide) (join_sr (m := 833290240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 833290240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 827719680) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 822149120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 822149120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 238551040) (by decide) (join_sr (m := 833290240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 833290240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (623/640 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((816578560 : ℤ) : ℝ) / (D : ℝ)) = (623/640 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
