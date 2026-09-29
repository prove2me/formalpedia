-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:30:58.874808+00:00
-- url     : https://prove2.me/submissions/0b981f8a-51a5-453b-b33e-47f6ca15bff7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [43/128, 447/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 281804800 284590080 ⟨⟨82126461941, 82126461947⟩, ⟨80363806024, 83901144058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249692160 250347520 281804800 284590080 ⟨⟨81751286174, 81751286180⟩, ⟨79992943966, 83521614472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249692160 284590080 287375360 ⟨⟨82903575257, 82903575264⟩, ⟨81137376587, 84681809996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 284590080 287375360 ⟨⟨82525113705, 82525113712⟩, ⟨80763237169, 84298986305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 250347520 251002880 281804800 284590080 ⟨⟨81376894122, 81376894125⟩, ⟨79622848930, 83142885500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 251002880 251658240 281804800 284590080 ⟨⟨81003280447, 81003280453⟩, ⟨79253515689, 82764951700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 250347520 251002880 284590080 287375360 ⟨⟨82147439331, 82147439334⟩, ⟨80389868245, 83916966678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251002880 251658240 284590080 287375360 ⟨⟨81770546783, 81770546790⟩, ⟨80017264579, 83535745659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249692160 287375360 290160640 ⟨⟨83680182756, 83680182763⟩, ⟨81910442549, 85461968855⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249692160 250347520 287375360 290160640 ⟨⟨83298441853, 83298441860⟩, ⟨81533032150, 85075857547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249692160 290160640 292945920 ⟨⟨84456286823, 84456286830⟩, ⟨82683006284, 86241623029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249692160 250347520 290160640 292945920 ⟨⟨84071272967, 84071272974⟩, ⟨82302331255, 85852230551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 287375360 290160640 ⟨⟨82917491530, 82917491531⟩, ⟨81156395663, 84690553687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251658240 287375360 290160640 ⟨⟨82537326419, 82537326426⟩, ⟨80780527832, 84306051809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251002880 290160640 292945920 ⟨⟨83687053030, 83687053033⟩, ⟨81922433489, 85463648847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 290160640 292945920 ⟨⟨83303621632, 83303621638⟩, ⟨81543307718, 85075872435⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 281804800 292945920 t = true :=
  ⟨_, (join_sr (m := 287375360) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 284590080) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249692160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 284590080) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 251002880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 250347520) (by decide) (join_sr (m := 290160640) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249692160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290160640) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 251002880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
