-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r304087040_315228160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:04:56.415976+00:00
-- url     : https://prove2.me/submissions/9a56420c-94a4-4fea-986c-61b436b48194

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [29/80, 481/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 304087040 306872320 ⟨⟨106655335505, 106655335512⟩, ⟨103259922660, 110090284431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 221511680 306872320 309657600 ⟨⟨107572235868, 107572235875⟩, ⟨104169655597, 111014376845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 221511680 222822400 304087040 306872320 ⟨⟨105771713860, 105771713866⟩, ⟨102391263621, 109191469270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 306872320 309657600 ⟨⟨106681868753, 106681868760⟩, ⟨103294274336, 110108793950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 221511680 309657600 312442880 ⟨⟨108488318339, 108488318346⟩, ⟨105078576148, 111937645616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 221511680 312442880 315228160 ⟨⟨109403587286, 109403587292⟩, ⟨105986688647, 112860095142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222822400 309657600 312442880 ⟨⟨107591223980, 107591223988⟩, ⟨104196490638, 111025313471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 221511680 222822400 312442880 315228160 ⟨⟨108499783789, 108499783795⟩, ⟨105097916737, 111941032113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 224133120 304087040 306872320 ⟨⟨104892408309, 104892408315⟩, ⟨101526788492, 108297104924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 222822400 224133120 306872320 309657600 ⟨⟨105795831241, 105795831249⟩, ⟨102423090746, 109207675099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 225443840 304087040 306872320 ⟨⟨104017360412, 104017360420⟩, ⟨100666440623, 107407131121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224133120 225443840 306872320 309657600 ⟨⟨104914064831, 104914064839⟩, ⟨101556048107, 108310959977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 309657600 312442880 ⟨⟨106698472415, 106698472423⟩, ⟨103318616242, 110117458283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222822400 224133120 312442880 315228160 ⟨⟨107600335961, 107600335967⟩, ⟨104213369081, 111026458629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224133120 225443840 309657600 312442880 ⟨⟨105810005087, 105810005093⟩, ⟨102444896182, 109214019683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224133120 225443840 312442880 315228160 ⟨⟨106705185193, 106705185199⟩, ⟨103332988835, 110116314280⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 304087040 315228160 t = true :=
  ⟨_, (join_su (m := 222822400) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 306872320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 221511680) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 312442880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 309657600) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 306872320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 224133120) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 312442880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (481/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
