-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_196608000_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:46.386159+00:00
-- url     : https://prove2.me/submissions/356bd35c-5ede-4103-8a05-ec8b3b8c69dd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 15/64]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 194641920 181534720 184320000 ⟨⟨77720832441, 77720832449⟩, ⟨75678427541, 79779736164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 194641920 195297280 181534720 184320000 ⟨⟨77396695503, 77396695506⟩, ⟨75360223137, 79449590693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 194641920 184320000 187105280 ⟨⟨78841095800, 78841095807⟩, ⟨76794195501, 80904491939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 194641920 195297280 184320000 187105280 ⟨⟨78512761460, 78512761463⟩, ⟨76471804283, 80570138786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 195297280 195952640 181534720 184320000 ⟨⟨77073715807, 77073715813⟩, ⟨75043144033, 79120634977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 195952640 196608000 181534720 184320000 ⟨⟨76751884127, 76751884134⟩, ⟨74727181267, 78792859502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 195952640 184320000 187105280 ⟨⟨78185594069, 78185594075⟩, ⟨76150548091, 80236985066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195952640 196608000 184320000 187105280 ⟨⟨77859584346, 77859584353⟩, ⟨75830417913, 79905021215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 194641920 187105280 189890560 ⟨⟨79959715098, 79959715104⟩, ⟨77908330154, 82027592783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 194641920 195297280 187105280 189890560 ⟨⟨79627201620, 79627201623⟩, ⟨77581770213, 81689050385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193986560 194641920 189890560 192675840 ⟨⟨81076700169, 81076700175⟩, ⟨79020841260, 83149048607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 194641920 195297280 189890560 192675840 ⟨⟨80740025672, 80740025673⟩, ⟨78690130542, 82806335254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 195297280 195952640 187105280 189890560 ⟨⟨79295864619, 79295864625⟩, ⟨77256354849, 81351716918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 195952640 196608000 187105280 189890560 ⟨⟨78965694762, 78965694769⟩, ⟨76932074996, 81015582774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 195297280 195952640 189890560 192675840 ⟨⟨80404537001, 80404537007⟩, ⟨78360573775, 82464840155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 195952640 196608000 189890560 192675840 ⟨⟨80070224780, 80070224786⟩, ⟨78032161850, 82124553652⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 196608000 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 194641920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 194641920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 195952640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 195952640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 195297280) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 194641920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 194641920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 195952640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 195952640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (15/64 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
