-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r214958080_220528640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:52:56.236684+00:00
-- url     : https://prove2.me/submissions/9b91e276-289f-446e-98ca-eb2b2724d794

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [41/160, 673/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 214958080 216350720 ⟨⟨63120068700, 63120068705⟩, ⟨61674190165, 64574354884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249036800 249692160 216350720 217743360 ⟨⟨63515205260, 63515205267⟩, ⟨62067660369, 64971163524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249692160 250347520 214958080 216350720 ⟨⟨62826643517, 62826643523⟩, ⟨61383655159, 64278014597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 216350720 217743360 ⟨⟨63220052455, 63220052461⟩, ⟨61775401804, 64673091572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 249692160 217743360 219136000 ⟨⟨63910199959, 63910199966⟩, ⟨62460988876, 65367830124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 249036800 249692160 219136000 220528640 ⟨⟨64305053119, 64305053126⟩, ⟨62854176012, 65764355011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250347520 217743360 219136000 ⟨⟨63613321378, 63613321384⟩, ⟨62167008589, 65068028368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249692160 250347520 219136000 220528640 ⟨⟨64006450604, 64006450609⟩, ⟨62558475835, 65462825302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 251002880 214958080 216350720 ⟨⟨62533897638, 62533897639⟩, ⟨61093786685, 63982366522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250347520 251002880 216350720 217743360 ⟨⟨62925581526, 62925581529⟩, ⟨61483812346, 64375714409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251002880 251658240 214958080 216350720 ⟨⟨62241826230, 62241826235⟩, ⟨60804580007, 63687405748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251002880 251658240 216350720 217743360 ⟨⟨62631787630, 62631787636⟩, ⟨61192887244, 64079027108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 217743360 219136000 ⟨⟨63317127228, 63317127230⟩, ⟨61873699966, 64768923956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251002880 219136000 220528640 ⟨⟨63708535057, 63708535059⟩, ⟨62263449857, 65161995477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251658240 217743360 219136000 ⟨⟨63021612653, 63021612660⟩, ⟨61581058238, 64470511950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 219136000 220528640 ⟨⟨63411301609, 63411301616⟩, ⟨61969093298, 64861860582⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 214958080 220528640 t = true :=
  ⟨_, (join_su (m := 250347520) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 216350720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 216350720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 249692160) (by decide) (join_sr (m := 219136000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 219136000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 217743360) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 216350720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 216350720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 251002880) (by decide) (join_sr (m := 219136000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 219136000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (673/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((220528640 : ℤ) : ℝ) / (D : ℝ)) = (673/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
