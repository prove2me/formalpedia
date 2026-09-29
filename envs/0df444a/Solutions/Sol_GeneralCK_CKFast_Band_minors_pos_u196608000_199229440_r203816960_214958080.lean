-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u196608000_199229440_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:15:09.625423+00:00
-- url     : https://prove2.me/submissions/ce8de1ab-ed0a-49c8-9a1e-75bd539cf1da

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [15/64, 19/80]`, `ρ ∈ [311/1280, 41/160]` by 15 cells of the computing
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
theorem cell0 : cellOK 196608000 197263360 203816960 206602240 ⟨⟨85215942545, 85215942551⟩, ⟨83161731922, 87286333959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 197263360 197918720 203816960 206602240 ⟨⟨84863592575, 84863592581⟩, ⟨82815269107, 86928025369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 196608000 197263360 206602240 209387520 ⟨⟨86307154056, 86307154064⟩, ⟨84248569142, 88381917094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 197263360 197918720 206602240 209387520 ⟨⟨85950781918, 85950781925⟩, ⟨83898093543, 88019577248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 197918720 198574080 203816960 206602240 ⟨⟨84512434771, 84512434773⟩, ⟨82469967780, 86570940128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 198574080 199229440 203816960 206602240 ⟨⟨84162459889, 84162459895⟩, ⟨82125818953, 86215068733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 197918720 198574080 206602240 209387520 ⟨⟨85595610130, 85595610135⟩, ⟨83548787647, 87658468897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 198574080 199229440 206602240 209387520 ⟨⟨85241629410, 85241629417⟩, ⟨83200642428, 87298582504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197263360 209387520 212172800 ⟨⟨87396866058, 87396866066⟩, ⟨85333916375, 89475991087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 197263360 197918720 209387520 212172800 ⟨⟨87036488249, 87036488257⟩, ⟨84979444334, 89109636638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 197918720 212172800 214958080 ⟨⟨88302751199, 88302751205⟩, ⟨84868385163, 91781035448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197918720 198574080 209387520 212172800 ⟨⟨86677318818, 86677318823⟩, ⟨84626150059, 88744521672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 198574080 199229440 209387520 212172800 ⟨⟨86319348446, 86319348453⟩, ⟨84274024484, 88380636617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 197918720 198574080 212172800 214958080 ⟨⟨87757569405, 87757569409⟩, ⟨85702063520, 89829107087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 198574080 199229440 212172800 214958080 ⟨⟨87395625443, 87395625449⟩, ⟨85345973502, 89461239583⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 196608000 199229440 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 197263360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 198574080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 197918720) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 212172800) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 198574080) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (15/64 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
