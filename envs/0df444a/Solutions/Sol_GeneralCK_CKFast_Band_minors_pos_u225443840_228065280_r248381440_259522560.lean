-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_228065280_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:37:32.638537+00:00
-- url     : https://prove2.me/submissions/3870866d-4e11-446c-8111-d5a658b2b1c2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 87/320]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226099200 248381440 251166720 ⟨⟨85366402757, 85366402763⟩, ⟨83482646391, 87263716326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226099200 226754560 248381440 251166720 ⟨⟨85000890605, 85000890611⟩, ⟨83122030104, 86893257603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226099200 251166720 253952000 ⟨⟨86273951481, 86273951488⟩, ⟨84386316872, 88175149070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226099200 226754560 251166720 253952000 ⟨⟨85904906654, 85904906660⟩, ⟨84022176566, 87801149180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 226754560 227409920 248381440 251166720 ⟨⟨84636327195, 84636327201⟩, ⟨82762341040, 86523769442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 227409920 228065280 248381440 251166720 ⟨⟨84272705836, 84272705839⟩, ⟨82403572660, 86155244992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 227409920 251166720 253952000 ⟨⟨85536815567, 85536815575⟩, ⟨83658968502, 87428124829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227409920 228065280 251166720 253952000 ⟨⟨85169671510, 85169671513⟩, ⟨83296686116, 87056069145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226099200 253952000 256737280 ⟨⟨87180666891, 87180666898⟩, ⟨85289157824, 89085744644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226099200 226754560 253952000 256737280 ⟨⟨86808099133, 86808099139⟩, ⟨84921503159, 88708213416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226099200 256737280 259522560 ⟨⟨88086553263, 88086553269⟩, ⟨86191173497, 89995507347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226099200 226754560 256737280 259522560 ⟨⟨87710472253, 87710472259⟩, ⟨85820014072, 89614454544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226754560 227409920 253952000 256737280 ⟨⟨86436490021, 86436490028⟩, ⟨84554785663, 88331662610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 227409920 228065280 253952000 256737280 ⟨⟨86065832826, 86065832829⟩, ⟨84188998752, 87956085338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 226754560 227409920 256737280 259522560 ⟨⟨87335354709, 87335354715⟩, ⟨85449796653, 89234386959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227409920 228065280 256737280 259522560 ⟨⟨86961193878, 86961193881⟩, ⟨85080514638, 88855297682⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 228065280 248381440 259522560 t = true :=
  ⟨_, (join_sr (m := 253952000) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 251166720) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226099200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 251166720) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 227409920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 226754560) (by decide) (join_sr (m := 256737280) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226099200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 256737280) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 227409920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
