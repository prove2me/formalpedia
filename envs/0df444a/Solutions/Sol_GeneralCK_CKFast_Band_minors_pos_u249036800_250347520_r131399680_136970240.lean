-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_250347520_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:50:42.808202+00:00
-- url     : https://prove2.me/submissions/b717107b-1ad4-4c27-b785-5cb9c5cd3a6a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 191/640]`, `ρ ∈ [401/2560, 209/1280]` by 17 cells of the computing
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
theorem cell0 : cellOK 249036800 249364480 131399680 132792320 ⟨⟨39186274682, 39186274688⟩, ⟨38400172065, 39975236007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249364480 249692160 131399680 132792320 ⟨⟨39093059839, 39093059845⟩, ⟨38307905250, 39881067526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249364480 132792320 134184960 ⟨⟨39591001541, 39591001546⟩, ⟨38803992025, 40380871299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249364480 249692160 132792320 134184960 ⟨⟨39496861541, 39496861547⟩, ⟨38710801504, 40285776213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249692160 250019840 131399680 132792320 ⟨⟨38999967554, 38999967555⟩, ⟨38215758943, 39787023663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250019840 250347520 131399680 132096000 ⟨⟨38806483793, 38806483798⟩, ⟨38134547140, 39480424300⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 250019840 250347520 132096000 132792320 ⟨⟨39007500920, 39007500925⟩, ⟨38335146005, 39681860466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249692160 250019840 132792320 134184960 ⟨⟨39402845064, 39402845067⟩, ⟨38617732456, 40190806714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250019840 250347520 132792320 134184960 ⟨⟨39308951641, 39308951646⟩, ⟨38524784418, 40095962337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249036800 249364480 134184960 135577600 ⟨⟨39995565433, 39995565438⟩, ⟨39207649230, 40786343406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249364480 249692160 134184960 135577600 ⟨⟨39900501370, 39900501376⟩, ⟨39113536095, 40690322814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249036800 249364480 135577600 136970240 ⟨⟨40399966718, 40399966723⟩, ⟨39611144041, 41191652693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249364480 249692160 135577600 136970240 ⟨⟨40303979689, 40303979694⟩, ⟨39516109382, 41094707694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 249692160 250019840 134184960 135577600 ⟨⟨39805561793, 39805561795⟩, ⟨39019545391, 40594428775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250019840 250347520 134184960 135577600 ⟨⟨39710746228, 39710746233⟩, ⟨38925676654, 40498660816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 249692160 250019840 135577600 136970240 ⟨⟨40208118098, 40208118101⟩, ⟨39421198107, 40997890204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 250019840 250347520 135577600 136970240 ⟨⟨40112381472, 40112381476⟩, ⟨39326409748, 40901199750⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 250347520 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249364480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell4) (join_sr (m := 132096000) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 250019840) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 249692160) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 249364480) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 135577600) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 250019840) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (191/640 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
