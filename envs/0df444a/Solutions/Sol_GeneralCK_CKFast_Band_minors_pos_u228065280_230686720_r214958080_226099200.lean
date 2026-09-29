-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_230686720_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:25:48.042961+00:00
-- url     : https://prove2.me/submissions/b1e7e38f-b700-42bd-88ab-0d15b62fbbc4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 11/40]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 228065280 228720640 214958080 217743360 ⟨⟨73125153001, 73125153008⟩, ⟨71307250521, 74956329279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228720640 229376000 214958080 217743360 ⟨⟨72806303526, 72806303533⟩, ⟨70993100563, 74632728954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228065280 228720640 217743360 220528640 ⟨⟨74028460255, 74028460262⟩, ⟨72206671219, 75863530329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228720640 229376000 217743360 220528640 ⟨⟨73705980618, 73705980625⟩, ⟨71888900829, 75536290258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 229376000 230031360 214958080 217743360 ⟨⟨72488310182, 72488310188⟩, ⟨70679785692, 74310006119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230031360 230686720 214958080 217743360 ⟨⟨72171166793, 72171166799⟩, ⟨70367299886, 73988154444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 229376000 230031360 217743360 220528640 ⟨⟨73384363149, 73384363156⟩, ⟨71571971568, 75209933707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230031360 230686720 217743360 220528640 ⟨⟨73063601641, 73063601648⟩, ⟨71255877384, 74884454315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 228720640 220528640 223313920 ⟨⟨74930922893, 74930922900⟩, ⟨73105251002, 76769882990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228720640 229376000 220528640 223313920 ⟨⟨74604823216, 74604823223⟩, ⟨72783870217, 76439013384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 228720640 223313920 226099200 ⟨⟨75832545157, 75832545162⟩, ⟨74002994093, 77675391529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228720640 229376000 223313920 226099200 ⟨⟨75502835501, 75502835506⟩, ⟨73678012886, 77340902534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 229376000 230031360 220528640 223313920 ⟨⟨74279591647, 74279591653⟩, ⟨72463336505, 76109033228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 230031360 230686720 220528640 223313920 ⟨⟨73955221948, 73955221955⟩, ⟨72143643786, 75779936132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230031360 223313920 226099200 ⟨⟨75173999792, 75173999799⟩, ⟨73353884601, 77007308819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230031360 230686720 223313920 226099200 ⟨⟨74846031769, 74846031774⟩, ⟨73030603128, 76674603970⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 230686720 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 228720640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 230031360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 229376000) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 228720640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 230031360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
