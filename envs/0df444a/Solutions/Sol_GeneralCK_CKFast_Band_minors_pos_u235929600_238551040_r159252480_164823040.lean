-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:13:45.924092+00:00
-- url     : https://prove2.me/submissions/bd87026b-775e-43a0-a403-7f524846e654

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 159252480 160645120 ⟨⟨51773633469, 51773633474⟩, ⟨50337413177, 53218579751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 236584960 160645120 162037760 ⟨⟨52211580311, 52211580316⟩, ⟨50773593959, 53658298193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 236584960 237240320 159252480 160645120 ⟨⟨51538769554, 51538769559⟩, ⟨50105538265, 52980697404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 160645120 162037760 ⟨⟨51974838098, 51974838105⟩, ⟨50539845453, 53418532875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 236584960 162037760 163430400 ⟨⟨52649325620, 52649325625⟩, ⟨51209573684, 54097814613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 236584960 163430400 164823040 ⟨⟨53086869879, 53086869885⟩, ⟨51645352836, 54537129497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 237240320 162037760 163430400 ⟨⟨52410707660, 52410707665⟩, ⟨50973954117, 53856168890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 236584960 237240320 163430400 164823040 ⟨⟨52846378711, 52846378716⟩, ⟨51407864732, 54293605924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237895680 159252480 160645120 ⟨⟨51304555466, 51304555467⟩, ⟨49874298671, 52743479580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 237895680 160645120 162037760 ⟨⟨51738749550, 51738749553⟩, ⟨50306736095, 53179435924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237895680 238551040 159252480 160645120 ⟨⟨51070986353, 51070986358⟩, ⟨49643689657, 52506921329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237895680 238551040 160645120 162037760 ⟨⟨51503309790, 51503309795⟩, ⟨50074261121, 52941002365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 162037760 163430400 ⟨⟨52172747172, 52172747175⟩, ⟨50738977501, 53615195350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237240320 237895680 163430400 164823040 ⟨⟨52606548800, 52606548803⟩, ⟨51171023356, 54050758327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237895680 238551040 162037760 163430400 ⟨⟨51935439261, 51935439268⟩, ⟨50504639048, 53374888996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 237895680 238551040 163430400 164823040 ⟨⟨52367375225, 52367375232⟩, ⟨50934823895, 53808581683⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 159252480 164823040 t = true :=
  ⟨_, (join_su (m := 237240320) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 160645120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 236584960) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163430400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 162037760) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 160645120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 237895680) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163430400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
