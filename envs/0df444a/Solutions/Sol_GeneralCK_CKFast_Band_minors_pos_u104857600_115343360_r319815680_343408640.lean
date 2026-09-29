-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r319815680_343408640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:43:18.338654+00:00
-- url     : https://prove2.me/submissions/d5e690f4-ee24-4e0f-9d67-87214e6876f0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [61/160, 131/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 319815680 325713920 ⟨⟨220702507529, 220702507538⟩, ⟨209419902727, 232292777682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 107479040 325713920 331612160 ⟨⟨223932227096, 223932227108⟩, ⟨212625421104, 235544089159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 107479040 110100480 319815680 325713920 ⟨⟨217279668802, 217279668811⟩, ⟨206157714378, 228703720099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 107479040 110100480 325713920 331612160 ⟨⟨220479797290, 220479797302⟩, ⟨209332759540, 231926480639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 107479040 331612160 337510400 ⟨⟨227143763455, 227143763467⟩, ⟨215813148756, 238776837027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 107479040 337510400 343408640 ⟨⟨230337481179, 230337481188⟩, ⟨218983438002, 241991398060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 107479040 110100480 331612160 337510400 ⟨⟨223662316820, 223662316832⟩, ⟨212490581024, 235131256704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 107479040 110100480 337510400 343408640 ⟨⟨226827574992, 226827575002⟩, ⟨215631514767, 238318407540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 112721920 319815680 325713920 ⟨⟨213924555708, 213924555711⟩, ⟨202958721682, 225187079314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 110100480 112721920 325713920 331612160 ⟨⟨217094907879, 217094907886⟩, ⟨206103179521, 228381024067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 112721920 115343360 319815680 325713920 ⟨⟨210634610622, 210634610631⟩, ⟨199820559155, 221740099921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 112721920 115343360 325713920 331612160 ⟨⟨213775026887, 213775026898⟩, ⟨202934336539, 224904994864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 110100480 112721920 331612160 337510400 ⟨⟨220248211436, 220248211440⟩, ⟨209230966202, 231557550425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 110100480 112721920 337510400 343408640 ⟨⟨223384797750, 223384797755⟩, ⟨212342402023, 234717000861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 112721920 115343360 331612160 337510400 ⟨⟨216898941039, 216898941048⟩, ⟨206031980939, 228053024382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112721920 115343360 337510400 343408640 ⟨⟨220006668957, 220006668968⟩, ⟨209113797710, 231184514918⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 319815680 343408640 t = true :=
  ⟨_, (join_su (m := 110100480) (by decide) (join_sr (m := 331612160) (by decide) (join_su (m := 107479040) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 325713920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 107479040) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 337510400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 331612160) (by decide) (join_su (m := 112721920) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 325713920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 112721920) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 337510400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (61/160 : ℝ) (131/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  have e3 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
