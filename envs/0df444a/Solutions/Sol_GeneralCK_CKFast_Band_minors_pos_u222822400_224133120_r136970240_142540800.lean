-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_224133120_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:48:20.523982+00:00
-- url     : https://prove2.me/submissions/0c58399d-f3b8-4d6a-946a-2faf0071811d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 171/640]`, `ρ ∈ [209/1280, 87/512]` by 14 cells of the computing
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
theorem cell0 : cellOK 222822400 223150080 136970240 138362880 ⟨⟨49012218330, 49012218335⟩, ⟨48138789374, 49889024976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 223150080 223477760 136970240 138362880 ⟨⟨48903473521, 48903473528⟩, ⟨48031190576, 49779126848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 223150080 138362880 139755520 ⟨⟨49493304336, 49493304342⟩, ⟨48618848611, 50371138765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223150080 223477760 138362880 139755520 ⟨⟨49383552445, 49383552451⟩, ⟨48510244309, 50260231984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 223477760 223805440 136970240 138362880 ⟨⟨48794900234, 48794900237⟩, ⟨47923760513, 49669403051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 223805440 224133120 136970240 138362880 ⟨⟨48686497796, 48686497801⟩, ⟨47816498522, 49559852909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 223477760 223805440 138362880 139755520 ⟨⟨49273973298, 49273973299⟩, ⟨48401809964, 50149500755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 223805440 224133120 138362880 139755520 ⟨⟨49164566218, 49164566223⟩, ⟨48293544908, 50038944404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 223150080 139755520 141148160 ⟨⟨49974120257, 49974120264⟩, ⟨49098638420, 50852981805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 223150080 223477760 139755520 141148160 ⟨⟨49863362943, 49863362948⟩, ⟨48989030269, 50741068035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222822400 223477760 141148160 142540800 ⟨⟨50398764304, 50398764309⟩, ⟨48923825902, 51882996428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 223477760 223805440 139755520 141148160 ⟨⟨49752779585, 49752779588⟩, ⟨48879593286, 50629331036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 223805440 224133120 139755520 141148160 ⟨⟨49642369507, 49642369512⟩, ⟨48770326800, 50517770125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 223477760 224133120 141148160 142540800 ⟨⟨50175592290, 50175592295⟩, ⟨48703891955, 51656552161⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 224133120 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 223477760) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 223150080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 223150080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 223805440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 223805440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 223477760) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 223150080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 141148160) (by decide) (join_su (m := 223805440) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (171/640 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((224133120 : ℤ) : ℝ) / (D : ℝ)) = (171/640 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
