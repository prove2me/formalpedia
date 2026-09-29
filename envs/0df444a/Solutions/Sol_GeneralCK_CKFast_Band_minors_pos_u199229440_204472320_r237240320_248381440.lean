-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_204472320_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:32:19.671074+00:00
-- url     : https://prove2.me/submissions/dfd45ff1-b099-4437-8ef3-0ece07d55770

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 39/160]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 237240320 240025600 ⟨⟨96425452581, 96425452585⟩, ⟨92954274525, 99940020722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 200540160 240025600 242810880 ⟨⟨97482045514, 97482045518⟩, ⟨94003101348, 101004392627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 200540160 201850880 237240320 240025600 ⟨⟨95638954622, 95638954628⟩, ⟨92184588031, 99136400493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 200540160 201850880 240025600 242810880 ⟨⟨96687946494, 96687946501⟩, ⟨93225840771, 100193145707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 200540160 242810880 245596160 ⟨⟨98537308008, 98537308011⟩, ⟨95050609779, 102067421711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 200540160 245596160 248381440 ⟨⟨99591247772, 99591247774⟩, ⟨96096807454, 103129115760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 200540160 201850880 242810880 245596160 ⟨⟨97735636651, 97735636659⟩, ⟨94265803428, 101248577245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 200540160 201850880 245596160 248381440 ⟨⟨98782032587, 98782032593⟩, ⟨95304483421, 102302702676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 201850880 203161600 237240320 240025600 ⟨⟨94857371271, 94857371277⟩, ⟨91419642070, 98337873048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 201850880 203161600 240025600 242810880 ⟨⟨95898787263, 95898787269⟩, ⟨92453346163, 99387016458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203161600 204472320 237240320 240025600 ⟨⟨94080629674, 94080629681⟩, ⟨90659366512, 97544362740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 203161600 204472320 240025600 242810880 ⟨⟨95114494776, 95114494784⟩, ⟨91685547193, 98585929056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 201850880 203161600 242810880 245596160 ⟨⟨96938929743, 96938929750⟩, ⟨93485787967, 100434874810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 201850880 203161600 245596160 248381440 ⟨⟨97977805996, 97977806002⟩, ⟨94516974698, 101481455458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203161600 204472320 242810880 245596160 ⟨⟨96147114060, 96147114067⟩, ⟨92710492877, 99626238414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203161600 204472320 245596160 248381440 ⟨⟨97178494603, 97178494609⟩, ⟨93734210577, 100665297958⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 204472320 237240320 248381440 t = true :=
  ⟨_, (join_su (m := 201850880) (by decide) (join_sr (m := 242810880) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 240025600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 200540160) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 245596160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 242810880) (by decide) (join_su (m := 203161600) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 240025600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 203161600) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 245596160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
