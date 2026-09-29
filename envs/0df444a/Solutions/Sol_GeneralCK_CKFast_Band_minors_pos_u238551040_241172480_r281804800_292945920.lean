-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:15:01.29489+00:00
-- url     : https://prove2.me/submissions/eaf9db6b-efd9-46b9-9e67-a899d9c457e0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [43/128, 447/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 281804800 284590080 ⟨⟨88240354371, 88240354379⟩, ⟨86406317869, 90087088283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 239206400 239861760 281804800 284590080 ⟨⟨87851883425, 87851883431⟩, ⟨86022443049, 89693977569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 239206400 284590080 287375360 ⟨⟨89070522904, 89070522910⟩, ⟨87232810851, 90920940344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 284590080 287375360 ⟨⟨88678708824, 88678708830⟩, ⟨86845601072, 90524478453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239861760 240517120 281804800 284590080 ⟨⟨87464286674, 87464286681⟩, ⟨85639423891, 89301759820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240517120 241172480 281804800 284590080 ⟨⟨87077558165, 87077558169⟩, ⟨85257254560, 88910428955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239861760 240517120 284590080 287375360 ⟨⟨88287772630, 88287772636⟩, ⟨86459250663, 90128913197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240517120 241172480 284590080 287375360 ⟨⟨87897708353, 87897708356⟩, ⟨86073753775, 89734238483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239206400 287375360 290160640 ⟨⟨89900073796, 89900073804⟩, ⟨88058688319, 91754172582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239206400 239861760 287375360 290160640 ⟨⟨89504924081, 89504924088⟩, ⟨87668151018, 91354367077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 239206400 290160640 292945920 ⟨⟨90729010085, 90729010091⟩, ⟨88883953294, 92586788048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239206400 239861760 290160640 292945920 ⟨⟨90330532187, 90330532193⟩, ⟨88490095861, 92183646444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239861760 240517120 287375360 290160640 ⟨⟨89110655871, 89110655878⟩, ⟨87278476724, 90955461804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240517120 241172480 287375360 290160640 ⟨⟨88717263186, 88717263188⟩, ⟨86889659576, 90557450657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 240517120 290160640 292945920 ⟨⟨89932939345, 89932939352⟩, ⟨88097105005, 91781408600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240517120 241172480 290160640 292945920 ⟨⟨89536225564, 89536225567⟩, ⟨87704974853, 91380068396⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 281804800 292945920 t = true :=
  ⟨_, (join_sr (m := 287375360) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 284590080) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 239206400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 284590080) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240517120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239861760) (by decide) (join_sr (m := 290160640) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 239206400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290160640) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240517120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
