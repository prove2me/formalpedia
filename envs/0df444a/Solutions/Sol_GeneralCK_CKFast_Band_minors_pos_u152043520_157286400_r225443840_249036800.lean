-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_157286400_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:54:49.75799+00:00
-- url     : https://prove2.me/submissions/81d8ea57-4e8f-4409-826e-6d5fd7a05852

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 3/16]`, `ρ ∈ [43/160, 19/64]` by 18 cells of the computing
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
theorem cell0 : cellOK 152043520 153354240 225443840 231342080 ⟨⟨123776553193, 123776553200⟩, ⟨118529421539, 129116309832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 153354240 154664960 225443840 231342080 ⟨⟨122782596367, 122782596371⟩, ⟨117571240775, 128085620384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 153354240 231342080 237240320 ⟨⟨126650804743, 126650804750⟩, ⟨121383724038, 132010161965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 153354240 154664960 231342080 237240320 ⟨⟨125638239827, 125638239829⟩, ⟨120406945725, 130960868155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 154664960 155975680 225443840 228392960 ⟨⟨121086053945, 121086053952⟩, ⟨116896789417, 125334240715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154664960 155975680 228392960 231342080 ⟨⟨122507714037, 122507714044⟩, ⟨118309347580, 126764932029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 155975680 157286400 225443840 228392960 ⟨⟨120113872251, 120113872258⟩, ⟨115949972694, 124336151893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 155975680 157286400 228392960 231342080 ⟨⟨121526236295, 121526236303⟩, ⟨117353245759, 125757540076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 154664960 155975680 231342080 237240320 ⟨⟨124634379592, 124634379599⟩, ⟨119438427333, 129920738768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 155975680 157286400 231342080 237240320 ⟨⟨123639073604, 123639073613⟩, ⟨118478026955, 128889614513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 152043520 153354240 237240320 243138560 ⟨⟨129512260160, 129512260169⟩, ⟨124225435766, 134891010773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 153354240 154664960 237240320 243138560 ⟨⟨128481339595, 128481339599⟩, ⟨123230307517, 133823369815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152043520 153354240 243138560 249036800 ⟨⟨132361122834, 132361122843⟩, ⟨127054755658, 137759064153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 153354240 154664960 243138560 249036800 ⟨⟨131312093485, 131312093489⟩, ⟨126041519662, 136673327527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 155975680 237240320 243138560 ⟨⟨127459189080, 127459189087⟩, ⟨122243507917, 132764954873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 155975680 157286400 237240320 243138560 ⟨⟨126445658109, 126445658116⟩, ⟨121264894859, 131715606726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 154664960 155975680 243138560 249036800 ⟨⟨130271895197, 130271895206⟩, ⟨125036676763, 135596874084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 155975680 157286400 243138560 249036800 ⟨⟨129240377470, 129240377478⟩, ⟨124040084727, 134529544753⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 157286400 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 153354240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 153354240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 155975680) (by decide) (join_sr (m := 228392960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 228392960) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 155975680) (by decide) (leaf_ok cell8) (leaf_ok cell9)))) (join_su (m := 154664960) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 153354240) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 153354240) (by decide) (leaf_ok cell12) (leaf_ok cell13))) (join_sr (m := 243138560) (by decide) (join_su (m := 155975680) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_su (m := 155975680) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
