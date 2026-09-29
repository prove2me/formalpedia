-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u196608000_199229440_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:36.801623+00:00
-- url     : https://prove2.me/submissions/39d0b549-dc8e-47d3-9d22-dd8d214d3c55

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [15/64, 19/80]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 196608000 197263360 181534720 184320000 ⟨⟨76431191318, 76431191324⟩, ⟨74412325967, 78466254849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 197263360 197918720 181534720 184320000 ⟨⟨76111628326, 76111628333⟩, ⟨74098569348, 78140811695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 196608000 197263360 184320000 187105280 ⟨⟨77534723096, 77534723102⟩, ⟨75511404821, 79574237766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 197263360 197918720 184320000 187105280 ⟨⟨77211001215, 77211001221⟩, ⟨75193499981, 79244625342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 197918720 198574080 181534720 184320000 ⟨⟨75793186187, 75793186192⟩, ⟨73785902710, 77816520802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 198574080 199229440 181534720 184320000 ⟨⟨75475856023, 75475856029⟩, ⟨73474317435, 77493373028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 197918720 198574080 184320000 187105280 ⟨⟨76888409687, 76888409691⟩, ⟨74876694638, 78916174658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 198574080 199229440 184320000 187105280 ⟨⟨76566939581, 76566939587⟩, ⟨74560980126, 78588876519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197263360 187105280 189890560 ⟨⟨78636682806, 78636682814⟩, ⟨76608921681, 80680638430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 197263360 197918720 187105280 189890560 ⟨⟨78308819597, 78308819604⟩, ⟨76286886015, 80346874465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 197263360 189890560 192675840 ⟨⟨79737079715, 79737079721⟩, ⟨77704885740, 81785466178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197263360 197918720 189890560 192675840 ⟨⟨79405092603, 79405092609⟩, ⟨77378736509, 81447568262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 197918720 198574080 187105280 189890560 ⟨⟨77982096070, 77982096075⟩, ⟨75965959195, 80014281545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 198574080 199229440 187105280 189890560 ⟨⟨77656503245, 77656503252⟩, ⟨75646132503, 79682850426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 198574080 189890560 192675840 ⟨⟨79074254333, 79074254335⟩, ⟨77053705305, 81110850525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 198574080 199229440 189890560 192675840 ⟨⟨78744555875, 78744555881⟩, ⟨76729783360, 80775303676⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 196608000 199229440 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 197263360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 198574080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 197918720) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 197263360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 198574080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (15/64 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
