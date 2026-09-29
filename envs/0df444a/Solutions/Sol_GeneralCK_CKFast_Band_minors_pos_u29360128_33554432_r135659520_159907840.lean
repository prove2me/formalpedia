-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u29360128_33554432_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:27:21.257018+00:00
-- url     : https://prove2.me/submissions/9240a865-72ca-4301-9008-f7f7e0de0154

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/200, 1/25]`, `ρ ∈ [207/1280, 61/320]` by 12 cells of the computing
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
theorem cell0 : cellOK 29360128 30408704 135659520 141721600 ⟨⟨224582601139, 224582601160⟩, ⟨210764686264, 238921201293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 30408704 31457280 135659520 141721600 ⟨⟨221434833818, 221434833836⟩, ⟨207866608684, 235509167826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 29360128 30408704 141721600 147783680 ⟨⟨230839428068, 230839428089⟩, ⟨217112549473, 245066977757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 30408704 31457280 141721600 147783680 ⟨⟨227671908301, 227671908318⟩, ⟨214188070408, 241642836082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 31457280 32505856 135659520 141721600 ⟨⟨218377048250, 218377048270⟩, ⟨205049526230, 232196719241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 32505856 33554432 135659520 141721600 ⟨⟨215405024459, 215405024476⟩, ⟨202309704854, 228979115478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 31457280 32505856 141721600 147783680 ⟨⟨224592950911, 224592950928⟩, ⟨211343587702, 238316378214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 32505856 33554432 141721600 147783680 ⟨⟨221598474102, 221598474122⟩, ⟨208575474696, 235083037597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 29360128 31457280 147783680 153845760 ⟨⟨235341848002, 235341848023⟩, ⟨215772984584, 255943178518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 29360128 31457280 153845760 159907840 ⟨⟨241298079853, 241298079870⟩, ⟨221834633971, 261757458500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 31457280 33554432 147783680 153845760 ⟨⟨229145921318, 229145921333⟩, ⟨210227513401, 249045066023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 31457280 33554432 153845760 159907840 ⟨⟨235069948218, 235069948233⟩, ⟨216241213507, 254846274151⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 29360128 33554432 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 31457280) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 30408704) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 30408704) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 32505856) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 32505856) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 31457280) (by decide) (join_sr (m := 153845760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 153845760) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/200 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
