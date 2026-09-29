-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_224133120_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:44:48.210453+00:00
-- url     : https://prove2.me/submissions/de65acb2-6714-430a-b214-544d3f18b4ce

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 171/640]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 222822400 223150080 131399680 132792320 ⟨⟨47085159576, 47085159582⟩, ⟨46215844343, 47957848403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 223150080 223477760 131399680 132792320 ⟨⟨46980459808, 46980459815⟩, ⟨46112284191, 47852001676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 223150080 132792320 134184960 ⟨⟨47567332865, 47567332871⟩, ⟨46696988203, 48441052153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223150080 223477760 132792320 134184960 ⟨⟨47461619320, 47461619325⟩, ⟨46592415882, 48334190047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 223477760 223805440 131399680 132792320 ⟨⟨46875926584, 46875926585⟩, ⟨46008887802, 47746324292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 223805440 224133120 131399680 132792320 ⟨⟨46771559245, 46771559251⟩, ⟨45905654533, 47640815595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 223477760 223805440 132792320 134184960 ⟨⟨47356073575, 47356073577⟩, ⟨46488008582, 48227498546⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 223805440 224133120 132792320 134184960 ⟨⟨47250694970, 47250694977⟩, ⟨46383765651, 48120976985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 223150080 134184960 135577600 ⟨⟨48049233289, 48049233295⟩, ⟨47177859864, 48923982365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 223150080 223477760 134184960 135577600 ⟨⟨47942507648, 47942507654⟩, ⟨47072277050, 48816106570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222822400 223150080 135577600 136970240 ⟨⟨48530861546, 48530861551⟩, ⟨47658460023, 49406639741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 223150080 223477760 135577600 136970240 ⟨⟨48423125486, 48423125491⟩, ⟨47551868386, 49297751941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 223477760 223805440 134184960 135577600 ⟨⟨47835951057, 47835951059⟩, ⟨46966860504, 48708402630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 223805440 224133120 134184960 135577600 ⟨⟨47729562851, 47729562857⟩, ⟨46861609570, 48600869879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 223477760 223805440 135577600 136970240 ⟨⟨48315559715, 48315559718⟩, ⟨47445444253, 49189037237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 223805440 224133120 135577600 136970240 ⟨⟨48208163566, 48208163572⟩, ⟨47339186968, 49080494960⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 224133120 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 223477760) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 223150080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 223150080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 223805440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 223805440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 223477760) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 223150080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 223150080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 223805440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 223805440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (171/640 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((224133120 : ℤ) : ℝ) / (D : ℝ)) = (171/640 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
