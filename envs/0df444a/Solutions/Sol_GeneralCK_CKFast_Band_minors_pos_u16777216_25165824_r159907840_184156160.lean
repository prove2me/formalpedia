-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:28:01.354412+00:00
-- url     : https://prove2.me/submissions/efaf05aa-140c-4cd7-94c1-434da0ef7c7a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 3/100]`, `ρ ∈ [61/320, 281/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 18874368 159907840 165969920 ⟨⟨293300280054, 293300280080⟩, ⟨269060349165, 318856591625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 16777216 18874368 165969920 172032000 ⟨⟨298967822085, 298967822111⟩, ⟨274974160489, 324217051546⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 18874368 20971520 159907840 165969920 ⟨⟨284341251542, 284341251567⟩, ⟨261092776488, 308835333274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 18874368 20971520 165969920 172032000 ⟨⟨290042453963, 290042453983⟩, ⟨267008261786, 314267635456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 16777216 18874368 172032000 178094080 ⟨⟨304498294917, 304498294942⟩, ⟨280744425414, 329450626051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 16777216 18874368 178094080 184156160 ⟨⟨309899993997, 309899994022⟩, ⟨286379584817, 334565164450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 18874368 20971520 172032000 178094080 ⟨⟨295608526760, 295608526784⟩, ⟨272783713481, 319572877969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 18874368 20971520 178094080 184156160 ⟨⟨301047418272, 301047418297⟩, ⟨278427127565, 324758717161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 20971520 23068672 159907840 165969920 ⟨⟨275962411989, 275962412012⟩, ⟨253621173698, 299483458984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 20971520 23068672 165969920 172032000 ⟨⟨281682932315, 281682932335⟩, ⟨259528117585, 304968358821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 23068672 25165824 159907840 165969920 ⟨⟨268100460979, 268100461003⟩, ⟨246593527251, 290726172327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 23068672 25165824 165969920 172032000 ⟨⟨273828350347, 273828350370⟩, ⟨252483466172, 296247577066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 20971520 23068672 172032000 178094080 ⟨⟨287270802561, 287270802585⟩, ⟨265298787277, 310326946202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 20971520 23068672 178094080 184156160 ⟨⟨292733606911, 292733606930⟩, ⟨270940742305, 315566630759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 23068672 25165824 172032000 178094080 ⟨⟨279426459576, 279426459594⟩, ⟨258241044309, 301644115318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 23068672 25165824 178094080 184156160 ⟨⟨284902002786, 284902002809⟩, ⟨263873398225, 306922915879⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 25165824 159907840 184156160 t = true :=
  ⟨_, (join_su (m := 20971520) (by decide) (join_sr (m := 172032000) (by decide) (join_su (m := 18874368) (by decide) (join_sr (m := 165969920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 165969920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 18874368) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 178094080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 172032000) (by decide) (join_su (m := 23068672) (by decide) (join_sr (m := 165969920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 165969920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 23068672) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 178094080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
