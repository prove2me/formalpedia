-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_214958080_r482344960_504627200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:38:37.692213+00:00
-- url     : https://prove2.me/submissions/2795efa0-ec21-45d4-8c48-283929791220

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 41/160]`, `ρ ∈ [23/40, 77/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 211025920 482344960 487915520 ⟨⟨174758288403, 174758288411⟩, ⟨170109451885, 179465657478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 211025920 212336640 482344960 487915520 ⟨⟨173432948577, 173432948586⟩, ⟨168807259226, 178116875713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 211025920 487915520 493486080 ⟨⟨176594805811, 176594805818⟩, ⟨171931241442, 181316853833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 211025920 212336640 487915520 493486080 ⟨⟨175257942632, 175257942639⟩, ⟨170617536839, 179956541700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 213647360 482344960 487915520 ⟨⟨172112727268, 172112727272⟩, ⟨167510028048, 176773371220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 213647360 214958080 482344960 487915520 ⟨⟨170797562898, 170797562907⟩, ⟨166217698525, 175435080679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 213647360 487915520 493486080 ⟨⟨173926191802, 173926191804⟩, ⟨169308788971, 178601499171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 213647360 214958080 487915520 493486080 ⟨⟨172599492045, 172599492052⟩, ⟨168004938280, 177251663253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 211025920 493486080 499056640 ⟨⟨178428660381, 178428660390⟩, ⟨173750395131, 183165359033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 211025920 212336640 493486080 499056640 ⟨⟨177080326203, 177080326212⟩, ⟨172425230043, 181793569801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209715200 211025920 499056640 504627200 ⟨⟨180259884920, 180259884929⟩, ⟨175566945363, 185011206280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 211025920 212336640 499056640 504627200 ⟨⟨178900131328, 178900131335⟩, ⟨174230370492, 183627992427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 212336640 213647360 493486080 499056640 ⟨⟨175737097481, 175737097485⟩, ⟨171105016227, 180427041763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 213647360 214958080 493486080 499056640 ⟨⟨174398913246, 174398913254⟩, ⟨169789694401, 179065712264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 212336640 213647360 499056640 504627200 ⟨⟨177545475587, 177545475591⟩, ⟨172898740727, 182250030639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 213647360 214958080 499056640 504627200 ⟨⟨176195857039, 176195857047⟩, ⟨171571997066, 180877258604⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 214958080 482344960 504627200 t = true :=
  ⟨_, (join_sr (m := 493486080) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 487915520) (by decide) (join_su (m := 211025920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 211025920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 487915520) (by decide) (join_su (m := 213647360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 213647360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 212336640) (by decide) (join_sr (m := 499056640) (by decide) (join_su (m := 211025920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 211025920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 499056640) (by decide) (join_su (m := 213647360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 213647360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (23/40 : ℝ) (77/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  have e3 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
