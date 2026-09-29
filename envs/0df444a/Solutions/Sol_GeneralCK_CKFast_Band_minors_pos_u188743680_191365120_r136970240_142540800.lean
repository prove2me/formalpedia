-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_191365120_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:26:59.835138+00:00
-- url     : https://prove2.me/submissions/bfc8187c-3414-4381-aa9d-3709b94d88ad

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 73/320]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 189399040 136970240 138362880 ⟨⟨61339419961, 61339419968⟩, ⟨59675711532, 63014590281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 189399040 138362880 139755520 ⟨⟨61932176095, 61932176101⟩, ⟨60266307138, 63609508806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 189399040 190054400 136970240 138362880 ⟨⟨61078095210, 61078095217⟩, ⟨59418699949, 62748901559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 189399040 190054400 138362880 139755520 ⟨⟨61668537447, 61668537453⟩, ⟨60006987356, 63341500580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 189399040 139755520 141148160 ⟨⟨62524433756, 62524433763⟩, ⟨60856406850, 64203926256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 189399040 141148160 142540800 ⟨⟨63116194502, 63116194509⟩, ⟨61446012212, 64797844195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 189399040 190054400 139755520 141148160 ⟨⟨62258486893, 62258486901⟩, ⟨60594784507, 63933604254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 189399040 190054400 141148160 142540800 ⟨⟨62847945083, 62847945089⟩, ⟨61182092922, 64525214118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 190054400 190709760 136970240 138362880 ⟨⟨60817811361, 60817811367⟩, ⟨59162703307, 62484280110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 190054400 190709760 138362880 139755520 ⟨⟨61405946535, 61405946541⟩, ⟨59748689343, 63074566466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 190709760 191365120 136970240 138362880 ⟨⟨60558559569, 60558559576⟩, ⟨58907712997, 62220716849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 190709760 191365120 138362880 139755520 ⟨⟨61144394469, 61144394475⟩, ⟨59491404444, 62808697333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 190054400 190709760 139755520 141148160 ⟨⟨61993594542, 61993594549⟩, ⟨60334190702, 63664363141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 190054400 190709760 141148160 142540800 ⟨⟨62580756890, 62580756896⟩, ⟨60919208880, 64253671648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 190709760 191365120 139755520 141148160 ⟨⟨61729747766, 61729747772⟩, ⟨60074616734, 63396193744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 190709760 191365120 141148160 142540800 ⟨⟨62314620944, 62314620950⟩, ⟨60657351343, 63983207570⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 191365120 136970240 142540800 t = true :=
  ⟨_, (join_su (m := 190054400) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 189399040) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 138362880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 189399040) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 141148160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 139755520) (by decide) (join_su (m := 190709760) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 138362880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 190709760) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 141148160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (73/320 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
