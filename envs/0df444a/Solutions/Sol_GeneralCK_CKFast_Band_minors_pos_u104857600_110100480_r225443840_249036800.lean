-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_110100480_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:36:21.930423+00:00
-- url     : https://prove2.me/submissions/065c2416-d191-41a9-954a-2348d562cd45

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 21/160]`, `ρ ∈ [43/160, 19/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 106168320 225443840 231342080 ⟨⟨166943259573, 166943259584⟩, ⟨160012334018, 174015329466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 106168320 107479040 225443840 231342080 ⟨⟨165498319859, 165498319870⟩, ⟨158627752640, 172508186848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 106168320 231342080 237240320 ⟨⟨170532154983, 170532154994⟩, ⟨163584810679, 177619329131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 106168320 107479040 231342080 237240320 ⟨⟨169066346054, 169066346063⟩, ⟨162179095449, 176091626959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 107479040 108789760 225443840 231342080 ⟨⟨164070955612, 164070955619⟩, ⟨157259748037, 171019655694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 108789760 110100480 225443840 231342080 ⟨⟨162660779207, 162660779217⟩, ⟨155907957602, 169549322365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 107479040 108789760 231342080 237240320 ⟨⟨167618153641, 167618153643⟩, ⟨160790012502, 174582561318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 108789760 110100480 231342080 237240320 ⟨⟨166187192643, 166187192651⟩, ⟨159417201152, 173091721759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 106168320 237240320 243138560 ⟨⟨174095358292, 174095358303⟩, ⟨167132020804, 181197220085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 106168320 107479040 237240320 243138560 ⟨⟨172609161653, 172609161664⟩, ⟨165705646458, 179649445895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 106168320 243138560 249036800 ⟨⟨177633426457, 177633426468⟩, ⟨170654506156, 184749574482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 106168320 107479040 243138560 249036800 ⟨⟨176127308071, 176127308080⟩, ⟨169207932360, 183182199794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 107479040 108789760 237240320 243138560 ⟨⟨171140614129, 171140614136⟩, ⟨164295951425, 178120324923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 108789760 110100480 237240320 243138560 ⟨⟨169689333285, 169689333296⟩, ⟨162902577090, 176609450035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 107479040 108789760 243138560 249036800 ⟨⟨174638863396, 174638863404⟩, ⟨167778076868, 181633487095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 108789760 110100480 243138560 249036800 ⟨⟨173167712784, 173167712794⟩, ⟨166364583261, 180103032673⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 110100480 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 107479040) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 106168320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 106168320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 108789760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 108789760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 107479040) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 106168320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 106168320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 243138560) (by decide) (join_su (m := 108789760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 108789760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
