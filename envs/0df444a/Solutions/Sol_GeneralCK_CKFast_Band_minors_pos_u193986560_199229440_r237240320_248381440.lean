-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:25:49.417209+00:00
-- url     : https://prove2.me/submissions/9196a30d-4b23-4381-9627-d23904c12dc3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 237240320 240025600 ⟨⟨99622094547, 99622094555⟩, ⟨96081873459, 103206991477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 193986560 195297280 240025600 242810880 ⟨⟨100709347244, 100709347250⟩, ⟨97161254931, 104302122484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 195297280 196608000 237240320 240025600 ⟨⟨98815182673, 98815182680⟩, ⟨95292497720, 102382215495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 240025600 242810880 ⟨⟨99894731730, 99894731737⟩, ⟨96364201386, 103469618536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 195297280 242810880 245596160 ⟨⟨101795149227, 101795149233⟩, ⟨98239199494, 105395788618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193986560 195297280 245596160 248381440 ⟨⟨102879509132, 102879509139⟩, ⟨99315715694, 106487998605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 196608000 242810880 245596160 ⟨⟨100972860967, 100972860975⟩, ⟨97434498583, 104555588053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195297280 196608000 245596160 248381440 ⟨⟨102049578780, 102049578786⟩, ⟨98503397620, 105640132531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197918720 237240320 240025600 ⟨⟨98013490379, 98013490385⟩, ⟨94508156013, 101562849050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 196608000 197918720 240025600 242810880 ⟨⟨99085361719, 99085361725⟩, ⟨95572208100, 102642549697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 197918720 199229440 237240320 240025600 ⟨⟨97216939322, 97216939328⟩, ⟨93728772957, 100748810758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197918720 199229440 240025600 242810880 ⟨⟨98281158681, 98281158689⟩, ⟨94785199495, 101820834417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 242810880 245596160 ⟨⟨100155843576, 100155843582⟩, ⟨96634883613, 103720847607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 197918720 245596160 248381440 ⟨⟨101224944110, 101224944116⟩, ⟨97696190628, 104797751027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 199229440 242810880 245596160 ⟨⟨99344018349, 99344018357⟩, ⟨95840278816, 102891485570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 245596160 248381440 ⟨⟨100405526257, 100405526263⟩, ⟨96894018771, 103960772230⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 237240320 248381440 t = true :=
  ⟨_, (join_su (m := 196608000) (by decide) (join_sr (m := 242810880) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 240025600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 195297280) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 245596160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 242810880) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 240025600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 197918720) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 245596160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
