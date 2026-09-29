-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_225443840_r181534720_187105280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:44:33.969884+00:00
-- url     : https://prove2.me/submissions/f8e66174-6196-45b9-afa0-b176610d9183

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 43/160]`, `ρ ∈ [277/1280, 571/2560]` by 14 cells of the computing
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
theorem cell0 : cellOK 222822400 223477760 181534720 182927360 ⟨⟨64206258746, 64206258751⟩, ⟨62677353242, 65744597606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 222822400 223477760 182927360 184320000 ⟨⟨64678557735, 64678557742⟩, ⟨63147803953, 66218749471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 223477760 224133120 181534720 182927360 ⟨⟨63926322285, 63926322290⟩, ⟨62400794958, 65461249984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223477760 224133120 182927360 184320000 ⟨⟨64396710020, 64396710025⟩, ⟨62869338929, 65933486124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 223477760 184320000 187105280 ⟨⟨65386541294, 65386541300⟩, ⟨63574171746, 67212536245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 223477760 224133120 184320000 187105280 ⟨⟨65101832267, 65101832274⟩, ⟨63294223469, 66923010747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 224133120 224788480 181534720 182927360 ⟨⟨63647207344, 63647207347⟩, ⟨62125041251, 65178741041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224133120 224788480 182927360 184320000 ⟨⟨64115687667, 64115687670⟩, ⟨62591682323, 65649065300⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 224788480 225443840 181534720 182927360 ⟨⟨63368907783, 63368907788⟩, ⟨61850086114, 64897064513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224788480 225443840 182927360 184320000 ⟨⟨63835484512, 63835484518⟩, ⟨62314828104, 65365480710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 224788480 184320000 185712640 ⟨⟨64583925838, 64583925841⟩, ⟨63058082025, 66119146611⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224133120 224788480 185712640 187105280 ⟨⟨65051922475, 65051922478⟩, ⟨63524240970, 66588985596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224788480 225443840 184320000 185712640 ⟨⟨64301822003, 64301822010⟩, ⟨62779331616, 65833656895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224788480 225443840 185712640 187105280 ⟨⟨64767920866, 64767920872⟩, ⟨63243597258, 66301593677⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 225443840 181534720 187105280 t = true :=
  ⟨_, (join_su (m := 224133120) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 223477760) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 182927360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 223477760) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 184320000) (by decide) (join_su (m := 224788480) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 182927360) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 224788480) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 185712640) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (571/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
