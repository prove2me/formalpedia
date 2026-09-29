-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:46.661343+00:00
-- url     : https://prove2.me/submissions/8eb0b490-a193-4092-af36-b856e3c54b65

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 203816960 206602240 ⟨⟨98579130871, 98579130873⟩, ⟨94830979588, 102378127312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173015040 174325760 206602240 209387520 ⟨⟨99818747662, 99818747667⟩, ⟨96062083788, 103626238368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 174325760 175636480 203816960 206602240 ⟨⟨97777792866, 97777792872⟩, ⟨94050333175, 101555658836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 206602240 209387520 ⟨⟨99008743158, 99008743165⟩, ⟨95272797440, 102795079129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 174325760 209387520 212172800 ⟨⟨101056165401, 101056165406⟩, ⟨97291013563, 104872125284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 173015040 174325760 212172800 214958080 ⟨⟨102291398845, 102291398850⟩, ⟨98517783470, 106115803019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 174325760 175636480 209387520 212172800 ⟨⟨100237540361, 100237540368⟩, ⟨96493132538, 104032321954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 174325760 175636480 212172800 214958080 ⟨⟨101464198812, 101464198820⟩, ⟨97711352618, 105267401842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 175636480 176947200 203816960 206602240 ⟨⟨96982750728, 96982750735⟩, ⟨93275733370, 100739742252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 175636480 176947200 206602240 209387520 ⟨⟨98205072664, 98205072671⟩, ⟨94489596293, 101970509407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 176947200 178257920 203816960 206602240 ⟨⟨96193900435, 96193900442⟩, ⟨92507080660, 99930268890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 176947200 178257920 206602240 209387520 ⟨⟨97407631844, 97407631852⟩, ⟨93712380502, 101152420240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 175636480 176947200 209387520 212172800 ⟨⟨99425286611, 99425286620⟩, ⟨95701374463, 103199144888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 176947200 212172800 214958080 ⟨⟨100643406502, 100643406510⟩, ⟨96911081628, 104425662814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 176947200 178257920 209387520 212172800 ⟨⟨98619299523, 98619299531⟩, ⟨94915639172, 102372484854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 176947200 178257920 212172800 214958080 ⟨⟨99828917006, 99828917012⟩, ⟨96116870031, 103590476448⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 203816960 214958080 t = true :=
  ⟨_, (join_su (m := 175636480) (by decide) (join_sr (m := 209387520) (by decide) (join_su (m := 174325760) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 206602240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 174325760) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 212172800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 209387520) (by decide) (join_su (m := 176947200) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 206602240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 176947200) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 212172800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
