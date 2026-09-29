-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u191365120_193986560_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:27:16.606494+00:00
-- url     : https://prove2.me/submissions/3dde56ac-e041-472b-a48a-6647aed19ea2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [73/320, 37/160]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 191365120 192020480 136970240 138362880 ⟨⟨60300331086, 60300331089⟩, ⟨58653720500, 61958202786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 191365120 192020480 138362880 139755520 ⟨⟨60883872456, 60883872457⟩, ⟨59235124096, 62543884149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 192020480 192675840 136970240 138362880 ⟨⟨60043117246, 60043117253⟩, ⟨58400717388, 61696729031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 192020480 192675840 138362880 139755520 ⟨⟨60624371786, 60624371792⟩, ⟨58979839826, 62280117976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 191365120 192020480 139755520 141148160 ⟨⟨61466937728, 61466937731⟩, ⟨59816053998, 63129086986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 191365120 192020480 141148160 142540800 ⟨⟨62049528365, 62049528368⟩, ⟨60396511660, 63713812765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 192020480 192675840 139755520 141148160 ⟨⟨61205155677, 61205155683⟩, ⟨59558493976, 62863033887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 192020480 192675840 141148160 142540800 ⟨⟨61785470358, 61785470364⟩, ⟨60136681271, 63445478208⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 192675840 193331200 136970240 138362880 ⟨⟨59786909491, 59786909497⟩, ⟨58148695323, 61436286784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 192675840 193331200 138362880 139755520 ⟨⟨60365883856, 60365883862⟩, ⟨58725543251, 62017389974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193331200 193986560 136970240 138362880 ⟨⟨59531699341, 59531699349⟩, ⟨57897646054, 61176867342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 193331200 193986560 138362880 139755520 ⟨⟨60108400144, 60108400150⟩, ⟨58472226076, 61755691393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 192675840 193331200 139755520 141148160 ⟨⟨60944392964, 60944392971⟩, ⟨59301928243, 62598025562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 192675840 193331200 141148160 142540800 ⟨⟨61522438233, 61522438240⟩, ⟨59877851708, 63178194973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 193331200 193986560 139755520 141148160 ⟨⟨60684641026, 60684641033⟩, ⟨59046348459, 62334053222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 193331200 193986560 141148160 142540800 ⟨⟨61260423384, 61260423390⟩, ⟨59620014589, 62911954225⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 191365120 193986560 136970240 142540800 t = true :=
  ⟨_, (join_su (m := 192675840) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 192020480) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 138362880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 192020480) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 141148160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 139755520) (by decide) (join_su (m := 193331200) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 138362880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 193331200) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 141148160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (73/320 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
