-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r367001600_414187520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:43:53.485584+00:00
-- url     : https://prove2.me/submissions/39bf1b32-4e48-440f-a543-57d6fcc6e867

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [7/16, 79/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 367001600 378798080 ⟨⟨247599922754, 247599922766⟩, ⟨233288884743, 262354727795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 107479040 110100480 367001600 378798080 ⟨⟨243942743623, 243942743635⟩, ⟨229837968109, 258483914602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 107479040 378798080 390594560 ⟨⟨253757017884, 253757017896⟩, ⟨239406255982, 268542832019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 107479040 110100480 378798080 390594560 ⟨⟨250049857255, 250049857266⟩, ⟨235902869875, 264624987401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 110100480 112721920 367001600 378798080 ⟨⟨240351320958, 240351320966⟩, ⟨226447646501, 254684183289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112721920 115343360 367001600 378798080 ⟨⟨236823315598, 236823315608⟩, ⟨223115779955, 250952992006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110100480 112721920 378798080 390594560 ⟨⟨246407880940, 246407880946⟩, ⟨232459680161, 260777456966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 112721920 115343360 378798080 390594560 ⟨⟨242828800559, 242828800571⟩, ⟨229074587486, 256997760964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 107479040 390594560 402391040 ⟨⟨259853948898, 259853948908⟩, ⟨245464882422, 274669466467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 110100480 390594560 402391040 ⟨⟨256098542008, 256098542017⟩, ⟨241910753479, 270706319600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 107479040 402391040 414187520 ⟨⟨265893036998, 265893037011⟩, ⟨251466993390, 280737041183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 107479040 110100480 402391040 414187520 ⟨⟨262091021276, 262091021288⟩, ⟨247863754001, 276730220426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 110100480 112721920 390594560 402391040 ⟨⟨252407715043, 252407715047⟩, ⟨238416386153, 266812692189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112721920 115343360 390594560 402391040 ⟨⟨248779229875, 248779229884⟩, ⟨234979721638, 262986165470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 110100480 112721920 402391040 414187520 ⟨⟨258352952550, 258352952556⟩, ⟨244319808986, 272792101002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112721920 115343360 402391040 414187520 ⟨⟨254676642297, 254676642309⟩, ⟨240833139898, 268920323943⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 367001600 414187520 t = true :=
  ⟨_, (join_sr (m := 390594560) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 378798080) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 107479040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 378798080) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 112721920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 110100480) (by decide) (join_sr (m := 402391040) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 107479040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 402391040) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 112721920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (7/16 : ℝ) (79/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  have e3 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
