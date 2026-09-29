-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_245104640_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:34:57.094522+00:00
-- url     : https://prove2.me/submissions/475a0645-efcd-42b2-951e-055c3335f8f6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 187/640]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244121600 136970240 138362880 ⟨⟨42372331002, 42372331007⟩, ⟨41567055111, 43180563715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244121600 244449280 136970240 138362880 ⟨⟨42273333877, 42273333883⟩, ⟨41469045752, 43080572934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244121600 138362880 139755520 ⟨⟨42791271582, 42791271587⟩, ⟨41985066434, 43600434999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244121600 244449280 138362880 139755520 ⟨⟨42691338154, 42691338159⟩, ⟨41886122237, 43499506456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 244449280 244776960 136970240 138362880 ⟨⟨42174470987, 42174470993⟩, ⟨41371168447, 42980718590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 244776960 245104640 136970240 138362880 ⟨⟨42075741829, 42075741832⟩, ⟨41273422700, 42881000164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 244776960 138362880 139755520 ⟨⟨42591539956, 42591539961⟩, ⟨41787311086, 43398715346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244776960 245104640 138362880 139755520 ⟨⟨42491876479, 42491876481⟩, ⟨41688632480, 43298061146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244121600 139755520 141148160 ⟨⟨43210032467, 43210032473⟩, ⟨42402898345, 44020126305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244121600 244449280 139755520 141148160 ⟨⟨43109163920, 43109163926⟩, ⟨42303020488, 43918261188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244121600 141148160 142540800 ⟨⟨43628614071, 43628614077⟩, ⟨42820551254, 44439638044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244121600 244449280 141148160 142540800 ⟨⟨43526811583, 43526811588⟩, ⟨42719740911, 44336837535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 244449280 244776960 139755520 141148160 ⟨⟨43008431589, 43008431594⟩, ⟨42203276660, 43816534491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 244776960 245104640 139755520 141148160 ⟨⟨42907834962, 42907834965⟩, ⟨42103666362, 43714945691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 244449280 244776960 141148160 142540800 ⟨⟨43425146291, 43425146297⟩, ⟨42619065577, 44234176431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 244776960 245104640 141148160 142540800 ⟨⟨43323617682, 43323617685⟩, ⟨42518524747, 44131654201⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 245104640 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244121600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 244776960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 244449280) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244121600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 244776960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (187/640 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
