-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u186122240_188743680_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:28:41.645224+00:00
-- url     : https://prove2.me/submissions/2307368e-859d-4518-aa52-b97993663735

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [71/320, 9/40]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 186122240 186777600 131399680 132792320 ⟨⟨59981733140, 59981733147⟩, ⟨58309268878, 61665860461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 186122240 186777600 132792320 134184960 ⟨⟨60585917972, 60585917978⟩, ⟨58911259201, 62272241398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 186777600 187432960 131399680 132792320 ⟨⟨59725580884, 59725580891⟩, ⟨58057512708, 61405259248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 186777600 187432960 132792320 134184960 ⟨⟨60327400073, 60327400080⟩, ⟨58657143297, 62009268732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 186122240 186777600 134184960 135577600 ⟨⟨61189574322, 61189574329⟩, ⟨59512723843, 62878091027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 186122240 186777600 135577600 136970240 ⟨⟨61792703872, 61792703878⟩, ⟨60113664472, 63483411038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 186777600 187432960 134184960 135577600 ⟨⟨60928696812, 60928696818⟩, ⟨59256254185, 62612752984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 186777600 187432960 135577600 136970240 ⟨⟨61529472751, 61529472757⟩, ⟨59854847017, 63215713669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 187432960 188088320 131399680 132792320 ⟨⟨59470477194, 59470477202⟩, ⟨57806778198, 61145733944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 187432960 188088320 132792320 134184960 ⟨⟨60069938010, 60069938016⟩, ⟨58404056312, 61747379249⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188088320 188743680 131399680 132792320 ⟨⟨59216413030, 59216413031⟩, ⟨57557056550, 60887275252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 188088320 188743680 132792320 134184960 ⟨⟨59813522689, 59813522692⟩, ⟨58151989401, 61486563601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 187432960 188088320 134184960 135577600 ⟨⟨60668882340, 60668882345⟩, ⟨59000820645, 62348505334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 187432960 188088320 135577600 136970240 ⟨⟨61267311808, 61267311814⟩, ⟨59597072813, 62949113837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 188088320 188743680 134184960 135577600 ⟨⟨60410121763, 60410121766⟩, ⟨58746414325, 62085338680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 188088320 188743680 135577600 136970240 ⟨⟨61006211856, 61006211859⟩, ⟨59340332916, 62683602098⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 186122240 188743680 131399680 136970240 t = true :=
  ⟨_, (join_su (m := 187432960) (by decide) (join_sr (m := 134184960) (by decide) (join_su (m := 186777600) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 132792320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 186777600) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 135577600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 134184960) (by decide) (join_su (m := 188088320) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 132792320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 188088320) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 135577600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (71/320 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
