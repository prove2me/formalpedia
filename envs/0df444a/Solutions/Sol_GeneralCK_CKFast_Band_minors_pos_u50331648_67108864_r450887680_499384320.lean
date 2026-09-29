-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_67108864_r450887680_499384320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:21:08.550407+00:00
-- url     : https://prove2.me/submissions/1f274dd6-100e-4d66-9218-60d40c78fdb2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 2/25]`, `ρ ∈ [43/80, 381/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 54525952 450887680 463011840 ⟨⟨389876375137, 389876375144⟩, ⟨363293537734, 417338641240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 54525952 463011840 475136000 ⟨⟨396360830174, 396360830184⟩, ⟨369852142402, 423712114711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 54525952 58720256 450887680 463011840 ⟨⟨380477857904, 380477857919⟩, ⟨354564243715, 407263205293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 54525952 58720256 463011840 475136000 ⟨⟨386949260370, 386949260385⟩, ⟨361092858492, 413643011270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 54525952 475136000 487260160 ⟨⟨402773127866, 402773127876⟩, ⟨376337408449, 430015790864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 50331648 54525952 487260160 499384320 ⟨⟨409116918415, 409116918423⟩, ⟨382752947700, 436253290659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 54525952 58720256 475136000 487260160 ⟨⟨393349920804, 393349920819⟩, ⟨367550042536, 419953794432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 54525952 58720256 487260160 499384320 ⟨⟨399683340880, 399683340895⟩, ⟨373939239905, 426199057272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 58720256 62914560 450887680 463011840 ⟨⟨371428793291, 371428793306⟩, ⟨346150508368, 397569707517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 58720256 62914560 463011840 475136000 ⟨⟨377880007077, 377880007092⟩, ⟨352643520599, 403947037833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 62914560 67108864 450887680 463011840 ⟨⟨362702432319, 362702432333⟩, ⟨338028688367, 388228647958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 62914560 67108864 463011840 475136000 ⟨⟨369127081582, 369127081597⟩, ⟨344481096529, 394595612331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 58720256 62914560 475136000 487260160 ⟨⟨384262064630, 384262064645⟩, ⟨359067102566, 410256384195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 58720256 62914560 487260160 499384320 ⟨⟨390578316282, 390578316299⟩, ⟨365424532558, 416501121401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 62914560 67108864 475136000 487260160 ⟨⟨375484294460, 375484294474⟩, ⟨350866141680, 400895847248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 62914560 67108864 487260160 499384320 ⟨⟨381777269171, 381777269184⟩, ⟨357186939498, 407132593768⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 67108864 450887680 499384320 t = true :=
  ⟨_, (join_su (m := 58720256) (by decide) (join_sr (m := 475136000) (by decide) (join_su (m := 54525952) (by decide) (join_sr (m := 463011840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 463011840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 54525952) (by decide) (join_sr (m := 487260160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 487260160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 475136000) (by decide) (join_su (m := 62914560) (by decide) (join_sr (m := 463011840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 463011840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 62914560) (by decide) (join_sr (m := 487260160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 487260160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (43/80 : ℝ) (381/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((450887680 : ℤ) : ℝ) / (D : ℝ)) = (43/80 : ℝ) := by norm_num [D]
  have e3 : (((499384320 : ℤ) : ℝ) / (D : ℝ)) = (381/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
