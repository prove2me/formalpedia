-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u117964800_120586240_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:12:39.435599+00:00
-- url     : https://prove2.me/submissions/fc41bf2b-6407-47e8-b00e-3049c9b66c7b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/64, 23/160]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 117964800 118620160 89784320 91258880 ⟨⟨67083837250, 67083837257⟩, ⟨64788642659, 69401530745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 117964800 118620160 91258880 92733440 ⟨⟨68096808197, 68096808204⟩, ⟨65798219315, 70417867399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 118620160 119275520 89784320 91258880 ⟨⟨66752145161, 66752145168⟩, ⟨64466538169, 69060078445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 118620160 119275520 91258880 92733440 ⟨⟨67760753644, 67760753653⟩, ⟨65471761659, 70072044045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 117964800 118620160 92733440 94208000 ⟨⟨69107536604, 69107536613⟩, ⟨66805572329, 71431942554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 117964800 118620160 94208000 95682560 ⟨⟨70116035518, 70116035527⟩, ⟨67810714581, 72443769418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 118620160 119275520 92733440 94208000 ⟨⟨68767146957, 68767146966⟩, ⟨66474788585, 71081775801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 118620160 119275520 94208000 95682560 ⟨⟨69771337906, 69771337915⟩, ⟨67475631594, 72089286681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 119275520 119930880 89784320 91258880 ⟨⟨66422900943, 66422900944⟩, ⟨64146790042, 68721167743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 119275520 119930880 91258880 92733440 ⟨⟨67427171343, 67427171349⟩, ⟨65147684798, 69728786599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 119930880 120586240 89784320 91258880 ⟨⟨66096072993, 66096073001⟩, ⟨63829368009, 68384765679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 119930880 120586240 91258880 92733440 ⟨⟨67096029461, 67096029470⟩, ⟨64825958230, 69388061878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 119275520 119930880 92733440 94208000 ⟨⟨68429253572, 68429253575⟩, ⟨66146409703, 70734198896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 119275520 119930880 94208000 95682560 ⟨⟨69429160203, 69429160206⟩, ⟨67142977177, 71737417361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 119930880 120586240 92733440 94208000 ⟨⟨68093824390, 68093824397⟩, ⟨65820404952, 70389178429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 119930880 120586240 94208000 95682560 ⟨⟨69089470129, 69089470136⟩, ⟨66812720373, 71388127836⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 117964800 120586240 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 119275520) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 118620160) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 91258880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 118620160) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 94208000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 92733440) (by decide) (join_su (m := 119930880) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 91258880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 119930880) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 94208000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/64 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((117964800 : ℤ) : ℝ) / (D : ℝ)) = (9/64 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
