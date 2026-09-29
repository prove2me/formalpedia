-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_157286400_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:01:36.337344+00:00
-- url     : https://prove2.me/submissions/8cc023b9-4462-4b4f-ba27-987e91c24c71

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 3/16]`, `ρ ∈ [113/320, 61/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 152043520 153354240 296222720 302120960 ⟨⟨157466015760, 157466015770⟩, ⟨151992121348, 163028243694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 153354240 154664960 296222720 302120960 ⟨⟨156264262418, 156264262422⟩, ⟨150825984032, 161790084988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 153354240 302120960 308019200 ⟨⟨160199368857, 160199368865⟩, ⟨154707718420, 165778985534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 153354240 154664960 302120960 308019200 ⟨⟨158981697596, 158981697601⟩, ⟨153525625117, 164524960495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 154664960 155975680 296222720 302120960 ⟨⟨155071715933, 155071715940⟩, ⟨149668649098, 160561548346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 155975680 157286400 296222720 302120960 ⟨⟨153888228615, 153888228624⟩, ⟨148519975941, 159342478785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 154664960 155975680 302120960 308019200 ⟨⟨157773257962, 157773257971⟩, ⟨152352362898, 163280577998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 155975680 157286400 302120960 308019200 ⟨⟨156573902824, 156573902833⟩, ⟨151187791593, 162045683761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 153354240 308019200 313917440 ⟨⟨162922141903, 162922141912⟩, ⟨157412893949, 168518987514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 153354240 154664960 308019200 313917440 ⟨⟨161688746663, 161688746668⟩, ⟨156215035352, 167249293254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 152043520 153354240 313917440 319815680 ⟨⟨165634499542, 165634499552⟩, ⟨160107809250, 171248417635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 153354240 154664960 313917440 319815680 ⟨⟨164385570119, 164385570123⟩, ⟨158894372016, 169963247019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154664960 155975680 308019200 313917440 ⟨⟨160464604827, 160464604837⟩, ⟨155026033585, 165989259001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 155975680 157286400 308019200 313917440 ⟨⟨159249569868, 159249569878⟩, ⟨153845748949, 164738731210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 155975680 313917440 319815680 ⟨⟨163145912990, 163145912997⟩, ⟨157689814496, 168687750963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 155975680 157286400 313917440 319815680 ⟨⟨161915382265, 161915382272⟩, ⟨156493997502, 167421776696⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 157286400 296222720 319815680 t = true :=
  ⟨_, (join_sr (m := 308019200) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 302120960) (by decide) (join_su (m := 153354240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 153354240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 302120960) (by decide) (join_su (m := 155975680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 155975680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 154664960) (by decide) (join_sr (m := 313917440) (by decide) (join_su (m := 153354240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 153354240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 313917440) (by decide) (join_su (m := 155975680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 155975680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
