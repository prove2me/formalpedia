-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r187105280_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:10:53.835284+00:00
-- url     : https://prove2.me/submissions/dd07d09b-5b11-4417-9bf0-2214dfe9313f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [571/2560, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 187105280 188497920 ⟨⟨55187041727, 55187041733⟩, ⟨53774526429, 56607848575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249036800 249692160 188497920 189890560 ⟨⟨55585084536, 55585084541⟩, ⟨54170899411, 57007567093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249692160 250347520 187105280 188497920 ⟨⟨54928565021, 54928565026⟩, ⟨53518856130, 56346540031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 188497920 189890560 ⟨⟨55324842157, 55324842163⟩, ⟨53913467740, 56744488601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 249692160 189890560 191283200 ⟨⟨55982978875, 55982978880⟩, ⟨54567124101, 57407136954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 249036800 249692160 191283200 192675840 ⟨⟨56380725079, 56380725085⟩, ⟨54963200837, 57806558495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250347520 189890560 191283200 ⟨⟨55720972777, 55720972782⟩, ⟨54307933000, 57142290479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249692160 250347520 191283200 192675840 ⟨⟨56116957210, 56116957216⟩, ⟨54702252239, 57539945996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 251002880 187105280 188497920 ⟨⟨54670712053, 54670712054⟩, ⟨53263796866, 56085868080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250347520 251002880 188497920 189890560 ⟨⟨55065226484, 55065226487⟩, ⟨53656650066, 56482049673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251002880 251658240 187105280 188497920 ⟨⟨54413478305, 54413478311⟩, ⟨53009344212, 55825828124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251002880 251658240 188497920 189890560 ⟨⟨54806232982, 54806232987⟩, ⟨53400441947, 56220245694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 189890560 191283200 ⟨⟨55459596331, 55459596334⟩, ⟨54049358836, 56878086519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251002880 191283200 192675840 ⟨⟨55853821919, 55853821922⟩, ⟨54441923502, 57273978943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251658240 189890560 191283200 ⟨⟨55198844985, 55198844992⟩, ⟨53791397153, 56614520440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 191283200 192675840 ⟨⟨55591314638, 55591314645⟩, ⟨54182210150, 57008652685⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 187105280 192675840 t = true :=
  ⟨_, (join_su (m := 250347520) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 188497920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 249692160) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 191283200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 189890560) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 188497920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 251002880) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 191283200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (571/2560 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
