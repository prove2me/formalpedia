-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r555745280_602931200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:47:13.982775+00:00
-- url     : https://prove2.me/submissions/0c65b42c-c9f7-4066-9d31-96375a36e985

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [53/80, 23/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 555745280 567541760 ⟨⟨340036223257, 340036223270⟩, ⟨325217670701, 355171004957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 107479040 110100480 555745280 567541760 ⟨⟨335742041987, 335742041999⟩, ⟨321090351421, 350708501502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 107479040 567541760 579338240 ⟨⟨345462907389, 345462907402⟩, ⟨330618989607, 360615785086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 107479040 110100480 567541760 579338240 ⟨⟨341137464721, 341137464733⟩, ⟨326458052058, 356124661308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 110100480 112721920 555745280 567541760 ⟨⟨331502157725, 331502157732⟩, ⟨317014489245, 346303067898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112721920 115343360 555745280 567541760 ⟨⟨327314945178, 327314945190⟩, ⟨312988542251, 341953001352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110100480 112721920 567541760 579338240 ⟨⟨336865529490, 336865529494⟩, ⟨322347897462, 351689694307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 112721920 115343360 567541760 579338240 ⟨⟨332645512858, 332645512870⟩, ⟨318287015743, 347309222541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 107479040 579338240 591134720 ⟨⟨350857335363, 350857335375⟩, ⟨335988523951, 366027901758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 110100480 579338240 591134720 ⟨⟨346501329263, 346501329275⟩, ⟨331794684365, 361508829568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 107479040 591134720 602931200 ⟨⟨356220763712, 356220763725⟩, ⟨341327496213, 371408642627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 107479040 110100480 591134720 602931200 ⟨⟨351834853162, 351834853174⟩, ⟨337101432250, 366862254847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 110100480 112721920 579338240 591134720 ⟨⟨342198040213, 342198040220⟩, ⟨327650949722, 357045003826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112721920 115343360 579338240 591134720 ⟨⟨337945914878, 337945914892⟩, ⟨323555841062, 352634803031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 110100480 112721920 591134720 602931200 ⟨⟨347500869226, 347500869234⟩, ⟨332924792210, 362370206588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112721920 115343360 591134720 602931200 ⟨⟨343217293128, 343217293140⟩, ⟨328796127522, 357930915200⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 555745280 602931200 t = true :=
  ⟨_, (join_sr (m := 579338240) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 567541760) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 107479040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 567541760) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 112721920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 110100480) (by decide) (join_sr (m := 591134720) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 107479040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 591134720) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 112721920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (53/80 : ℝ) (23/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  have e3 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
