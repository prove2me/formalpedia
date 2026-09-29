-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_241172480_r727449600_749731840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:03:39.848099+00:00
-- url     : https://prove2.me/submissions/2c331ad2-2d74-4e10-96cc-6246b35f0b7a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 23/80]`, `ρ ∈ [111/128, 143/160]` by 20 cells of the computing
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
theorem cell0 : cellOK 230686720 233308160 727449600 733020160 ⟨⟨224408478793, 224408478801⟩, ⟨215838117735, 233138890541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 233308160 733020160 738590720 ⟨⟨225990276039, 225990276048⟩, ⟨217393294635, 234747282535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 235929600 727449600 733020160 ⟨⟨220959851460, 220959851468⟩, ⟨212452474326, 229626941102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233308160 235929600 733020160 738590720 ⟨⟨222521134689, 222521134698⟩, ⟨213987166052, 231214812499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 233308160 738590720 744161280 ⟨⟨227571040912, 227571040921⟩, ⟨218947442768, 236354634230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 233308160 744161280 749731840 ⟨⟨229150790820, 229150790829⟩, ⟨220500579256, 237960963309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 235929600 738590720 744161280 ⟨⟨224081426875, 224081426883⟩, ⟨215520868888, 232801686505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 233308160 235929600 744161280 749731840 ⟨⟨225640744659, 225640744668⟩, ⟨217053599204, 234387580015⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 238551040 727449600 733020160 ⟨⟨217525602227, 217525602236⟩, ⟨209080769661, 226129796363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 235929600 238551040 733020160 738590720 ⟨⟨219066288263, 219066288274⟩, ⟨210594901599, 227697054844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 239861760 727449600 733020160 ⟨⟨214959167245, 214959167251⟩, ⟨210168375850, 219802724074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 241172480 727449600 733020160 ⟨⟨213252545765, 213252545774⟩, ⟨208482885007, 218074852799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 733020160 738590720 ⟨⟨216484352241, 216484352247⟩, ⟨211679641593, 221341811091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 241172480 733020160 738590720 ⟨⟨214767371974, 214767371982⟩, ⟨209983805556, 219603571005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 235929600 238551040 738590720 744161280 ⟨⟨220606023554, 220606023563⟩, ⟨212108083520, 229263357777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235929600 238551040 744161280 749731840 ⟨⟨222144823999, 222144824008⟩, ⟨213620331068, 230828721302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 238551040 239861760 738590720 744161280 ⟨⟨218008616040, 218008616043⟩, ⟨213189988745, 222879973120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 239861760 241172480 738590720 744161280 ⟨⟨216281296361, 216281296370⟩, ⟨211483826496, 221131384016⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 238551040 239861760 744161280 749731840 ⟨⟨219531973998, 219531974004⟩, ⟨214699432518, 224417225672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 239861760 241172480 744161280 749731840 ⟨⟨217794333936, 217794333945⟩, ⟨212982962690, 222658306985⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 241172480 727449600 749731840 t = true :=
  ⟨_, (join_su (m := 235929600) (by decide) (join_sr (m := 738590720) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 733020160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 733020160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 233308160) (by decide) (join_sr (m := 744161280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 744161280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 738590720) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 733020160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 733020160) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 239861760) (by decide) (leaf_ok cell12) (leaf_ok cell13)))) (join_su (m := 238551040) (by decide) (join_sr (m := 744161280) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 744161280) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 239861760) (by decide) (leaf_ok cell18) (leaf_ok cell19))))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (111/128 : ℝ) (143/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((727449600 : ℤ) : ℝ) / (D : ℝ)) = (111/128 : ℝ) := by norm_num [D]
  have e3 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
