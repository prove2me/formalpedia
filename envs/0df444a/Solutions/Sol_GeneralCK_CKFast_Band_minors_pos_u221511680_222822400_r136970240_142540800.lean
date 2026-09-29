-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u221511680_222822400_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:47:42.9956+00:00
-- url     : https://prove2.me/submissions/e8ae05f9-00e3-4a85-8719-7d125abff4eb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [169/640, 17/64]`, `ρ ∈ [209/1280, 87/512]` by 12 cells of the computing
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
theorem cell0 : cellOK 221511680 221839360 136970240 138362880 ⟨⟨49448926207, 49448926212⟩, ⟨48570885110, 50330374490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 221839360 222167040 136970240 138362880 ⟨⟨49339488589, 49339488592⟩, ⟨48462604765, 50219772185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 221511680 221839360 138362880 139755520 ⟨⟨49934052852, 49934052858⟩, ⟨49054978646, 50816535221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221839360 222167040 138362880 139755520 ⟨⟨49823603222, 49823603224⟩, ⟨48945687874, 50704919324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222167040 222494720 136970240 138362880 ⟨⟨49230225188, 49230225195⟩, ⟨48354495804, 50109346960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222494720 222822400 136970240 138362880 ⟨⟨49121135328, 49121135333⟩, ⟨48246557563, 49999098117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222167040 222494720 138362880 139755520 ⟨⟨49713329045, 49713329051⟩, ⟨48836569724, 50593481747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222494720 222822400 138362880 139755520 ⟨⟨49603229645, 49603229650⟩, ⟨48727623526, 50482221791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 221511680 222167040 139755520 141148160 ⟨⟨50363150580, 50363150586⟩, ⟨48883569552, 51852089484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221511680 222167040 141148160 142540800 ⟨⟨50847219846, 50847219851⟩, ⟨49365754532, 52338047988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222167040 222822400 139755520 141148160 ⟨⟨50140583880, 50140583887⟩, ⟨48664269638, 51626221286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 222167040 222822400 141148160 142540800 ⟨⟨50622638328, 50622638334⟩, ⟨49144444979, 52110159833⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 221511680 222822400 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 222167040) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 221839360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 221839360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 222494720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 222494720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 222167040) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 141148160) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (169/640 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((221511680 : ℤ) : ℝ) / (D : ℝ)) = (169/640 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
