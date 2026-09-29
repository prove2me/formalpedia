-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r220528640_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:54:42.385968+00:00
-- url     : https://prove2.me/submissions/0c41bd79-1988-47cf-b247-815776817b60

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [673/2560, 69/256]` by 14 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 220528640 221921280 ⟨⟨64699765064, 64699765071⟩, ⟨63247222098, 66160738507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249036800 249692160 221921280 223313920 ⟨⟨65094336117, 65094336122⟩, ⟨63640127460, 66556980935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249692160 250347520 220528640 221921280 ⟨⟨64399440451, 64399440458⟩, ⟨62949803858, 65857482695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 221921280 223313920 ⟨⟨64792291240, 64792291245⟩, ⟨63340992976, 66252000865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 249692160 223313920 226099200 ⟨⟨65685929228, 65685929235⟩, ⟨63997966310, 67385700545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 249692160 250347520 223313920 226099200 ⟨⟨65381307379, 65381307384⟩, ⟨63697469015, 67076911998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 250347520 251002880 220528640 221921280 ⟨⟨64099805326, 64099805329⟩, ⟨62653062334, 65554929286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250347520 251002880 221921280 223313920 ⟨⟨64490938350, 64490938352⟩, ⟨63042537707, 65947725698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 251002880 251658240 220528640 221921280 ⟨⟨63800854806, 63800854811⟩, ⟨62356992731, 65253073314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 251002880 251658240 221921280 223313920 ⟨⟨64190272551, 64190272557⟩, ⟨62744756847, 65644150454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251002880 223313920 224706560 ⟨⟨64881934440, 64881934442⟩, ⟨63431876290, 66340385025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250347520 251002880 224706560 226099200 ⟨⟨65272793907, 65272793910⟩, ⟨63821078393, 66732907579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 251002880 251658240 223313920 224706560 ⟨⟨64579555153, 64579555159⟩, ⟨63132385950, 66035092311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251658240 224706560 226099200 ⟨⟨64968702918, 64968702924⟩, ⟨63519880348, 66425899191⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 220528640 226099200 t = true :=
  ⟨_, (join_su (m := 250347520) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 221921280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 221921280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 249692160) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 223313920) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 221921280) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 221921280) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 251002880) (by decide) (join_sr (m := 224706560) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 224706560) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (673/2560 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((220528640 : ℤ) : ℝ) / (D : ℝ)) = (673/2560 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
