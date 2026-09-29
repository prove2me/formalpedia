-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r359792640_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:00:06.620988+00:00
-- url     : https://prove2.me/submissions/e6cd2694-2e88-429b-88de-e4c6766cd0b6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [549/1280, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 359792640 362577920 ⟨⟨109111553966, 109111553974⟩, ⟨105805602301, 112454353191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 242483200 362577920 365363200 ⟨⟨109911384246, 109911384252⟩, ⟨106598700380, 113260949899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 243793920 359792640 362577920 ⟨⟨108162185150, 108162185156⟩, ⟨104869774012, 111491263288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 362577920 365363200 ⟨⟨108955735989, 108955735996⟩, ⟨105656615574, 112291558372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 242483200 365363200 368148480 ⟨⟨110710705977, 110710705983⟩, ⟨107391291636, 114067036156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 242483200 368148480 370933760 ⟨⟨111509521741, 111509521747⟩, ⟨108183378638, 114872614556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243793920 365363200 368148480 ⟨⟨109748790394, 109748790401⟩, ⟨106442962263, 113091355287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242483200 243793920 368148480 370933760 ⟨⟨110541350873, 110541350879⟩, ⟨107228816572, 113890656553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 245104640 359792640 362577920 ⟨⟨107216493607, 107216493615⟩, ⟨103937519669, 110531955662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 243793920 245104640 362577920 365363200 ⟨⟨108003772674, 108003772680⟩, ⟨104718112602, 111325956549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 246415360 359792640 362577920 ⟨⟨106274431855, 106274431858⟩, ⟨103008793033, 109576381558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245104640 246415360 362577920 365363200 ⟨⟨107055446793, 107055446796⟩, ⟨103783145195, 110364095662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 365363200 368148480 ⟨⟨108790567202, 108790567209⟩, ⟨105498222396, 112119471330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243793920 245104640 368148480 370933760 ⟨⟨109576879631, 109576879638⟩, ⟨106277851480, 112912502454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 246415360 365363200 368148480 ⟨⟨107835988879, 107835988883⟩, ⟨104557025748, 111151335507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 368148480 370933760 ⟨⟨108616060483, 108616060487⟩, ⟨105330437049, 111938103476⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 359792640 370933760 t = true :=
  ⟨_, (join_su (m := 243793920) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 362577920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 362577920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 242483200) (by decide) (join_sr (m := 368148480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 368148480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 365363200) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 362577920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 362577920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245104640) (by decide) (join_sr (m := 368148480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 368148480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (549/1280 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((359792640 : ℤ) : ℝ) / (D : ℝ)) = (549/1280 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
