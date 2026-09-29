-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r192675840_198246400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:47:25.9955+00:00
-- url     : https://prove2.me/submissions/0789eb30-a20f-44ae-ab1b-056519bd74dc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [147/640, 121/512]` by 13 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 192675840 194068480 ⟨⟨64490848192, 64490848196⟩, ⟨62987052525, 66003735817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231342080 194068480 195461120 ⟨⟨64938761345, 64938761347⟩, ⟨63433176094, 66453443539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231342080 231997440 192675840 194068480 ⟨⟨64205516951, 64205516958⟩, ⟨62704939694, 65715155997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 194068480 195461120 ⟨⟨64651584388, 64651584393⟩, ⟨63149221886, 66163013701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231342080 195461120 198246400 ⟨⟨65610237299, 65610237303⟩, ⟨63838036280, 67395452172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 231342080 231997440 195461120 198246400 ⟨⟨65320296586, 65320296591⟩, ⟨63552641241, 67100914760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 232652800 192675840 194068480 ⟨⟨63920964890, 63920964895⟩, ⟨62423590531, 65427371054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231997440 232652800 194068480 195461120 ⟨⟨64365189989, 64365189994⟩, ⟨62866034724, 65873382123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 232652800 233308160 192675840 194068480 ⟨⟨63637186301, 63637186307⟩, ⟨62142999447, 65140375173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 232652800 233308160 194068480 195461120 ⟨⟨64079572425, 64079572430⟩, ⟨62583608999, 65584542965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 231997440 232652800 195461120 198246400 ⟨⟨65031143450, 65031143455⟩, ⟨63268013342, 66807185680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232652800 233308160 195461120 196853760 ⟨⟨64521756082, 64521756088⟩, ⟨63024016614, 66028507750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 232652800 233308160 196853760 198246400 ⟨⟨64963737769, 64963737775⟩, ⟨63464222788, 66472270024⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 192675840 198246400 t = true :=
  ⟨_, (join_su (m := 231997440) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 194068480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231342080) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 195461120) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 194068480) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 232652800) (by decide) (leaf_ok cell10) (join_sr (m := 196853760) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (121/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
