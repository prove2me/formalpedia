-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r281804800_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.148312+00:00
-- url     : https://prove2.me/submissions/503a72ab-6c3c-462c-bb6e-a7b09778a4c3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [43/128, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 281804800 287375360 ⟨⟨137295030557, 137295030566⟩, ⟨132369006891, 142297915578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 169082880 170393600 281804800 287375360 ⟨⟨136233897765, 136233897772⟩, ⟨131338107246, 141205888170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 169082880 287375360 292945920 ⟨⟨139718216359, 139718216368⟩, ⟨134775071509, 144738028392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 169082880 170393600 287375360 292945920 ⟨⟨138641967172, 138641967181⟩, ⟨133729064256, 143630884681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 170393600 171704320 281804800 287375360 ⟨⟨135180299782, 135180299789⟩, ⟨130314416085, 140121730718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 171704320 173015040 281804800 287375360 ⟨⟨134134120246, 134134120254⟩, ⟨129297822520, 139045321228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 171704320 287375360 292945920 ⟨⟨137573287095, 137573287104⟩, ⟨132690302124, 142531642655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 171704320 173015040 287375360 292945920 ⟨⟨136512059910, 136512059917⟩, ⟨131658674291, 141440180550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 169082880 292945920 298516480 ⟨⟨142133592264, 142133592271⟩, ⟨137173437146, 147170218701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 169082880 170393600 292945920 298516480 ⟨⟨141042377149, 141042377158⟩, ⟨136112470105, 146048111787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 169082880 298516480 304087040 ⟨⟨144541264214, 144541264223⟩, ⟨139564207827, 149594594391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 169082880 170393600 298516480 304087040 ⟨⟨143435230895, 143435230902⟩, ⟨138488426138, 148457674563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 170393600 171704320 292945920 298516480 ⟨⟨139958763000, 139958763009⟩, ⟨135058782414, 144933935809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 171704320 173015040 292945920 298516480 ⟨⟨138882633781, 138882633788⟩, ⟨134012263354, 143827569269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 170393600 171704320 298516480 304087040 ⟨⟨142336828023, 142336828031⟩, ⟨137419955692, 147328712515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 171704320 173015040 298516480 304087040 ⟨⟨141245939773, 141245939780⟩, ⟨136358685900, 146207587048⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 281804800 304087040 t = true :=
  ⟨_, (join_sr (m := 292945920) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 169082880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 287375360) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 171704320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 170393600) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 169082880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 298516480) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 171704320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
