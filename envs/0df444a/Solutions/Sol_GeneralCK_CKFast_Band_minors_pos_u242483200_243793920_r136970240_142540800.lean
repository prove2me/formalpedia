-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u242483200_243793920_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:29:55.462291+00:00
-- url     : https://prove2.me/submissions/6a1af582-87a5-48c7-8d42-742fbd4496ad

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/128, 93/320]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 242483200 242810880 136970240 138362880 ⟨⟨42769672040, 42769672045⟩, ⟨41960423112, 43581901544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242810880 243138560 136970240 138362880 ⟨⟨42670132876, 42670132881⟩, ⟨41861880518, 43481359842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 242810880 138362880 139755520 ⟨⟨43192367828, 43192367833⟩, ⟨42382183767, 44005533891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242810880 243138560 138362880 139755520 ⟨⟨43091888356, 43091888361⟩, ⟨42282702337, 43904050414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243138560 243466240 136970240 138362880 ⟨⟨42570729991, 42570729995⟩, ⟨41763471992, 43380956649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243466240 243793920 136970240 138362880 ⟨⟨42471462870, 42471462875⟩, ⟨41665197022, 43280691448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243138560 243466240 138362880 139755520 ⟨⟨42991546170, 42991546171⟩, ⟨42183355978, 43802706456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243466240 243793920 138362880 139755520 ⟨⟨42891340748, 42891340754⟩, ⟨42084144177, 43701501494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 242810880 139755520 141148160 ⟨⟨43614879129, 43614879135⟩, ⟨42803760237, 44428981447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242810880 243138560 139755520 141148160 ⟨⟨43513460556, 43513460562⟩, ⟨42703341172, 44326557409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 242483200 242810880 141148160 142540800 ⟨⟨44037206369, 44037206374⟩, ⟨43225152944, 44852244638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242810880 243138560 141148160 142540800 ⟨⟨43934849899, 43934849904⟩, ⟨43123797445, 44748881247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243138560 243466240 139755520 141148160 ⟨⟨43412180269, 43412180273⟩, ⟨42603058178, 44224273890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243466240 243793920 139755520 141148160 ⟨⟨43311037744, 43311037751⟩, ⟨42502910737, 44122130366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243466240 141148160 142540800 ⟨⟨43832632710, 43832632713⟩, ⟨43022579009, 44645659370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243466240 243793920 141148160 142540800 ⟨⟨43730554274, 43730554279⟩, ⟨42921497115, 44542578481⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 242483200 243793920 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242810880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243466240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243138560) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 242810880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 243466240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/128 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
