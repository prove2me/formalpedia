-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:10:05.118696+00:00
-- url     : https://prove2.me/submissions/b01cf2aa-bcf2-4fef-ba31-916d099a0a25

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 270663680 273448960 ⟨⟨84913442759, 84913442766⟩, ⟨83094129951, 86745420489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 239206400 239861760 270663680 273448960 ⟨⟨84538420227, 84538420234⟩, ⟨82723670226, 86365790994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 239206400 273448960 276234240 ⟨⟨85746112423, 85746112429⟩, ⟨83923115439, 87581782534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 273448960 276234240 ⟨⟨85367716313, 85367716319⟩, ⟨83549290561, 87198771164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239861760 240517120 270663680 273448960 ⟨⟨84164256419, 84164256425⟩, ⟨82354050619, 85987039067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240517120 241172480 270663680 273448960 ⟨⟨83790945439, 83790945442⟩, ⟨81985265360, 85609158685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239861760 240517120 273448960 276234240 ⟨⟨84990182905, 84990182910⟩, ⟨83176309795, 86816641322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240517120 241172480 273448960 276234240 ⟨⟨84613506286, 84613506287⟩, ⟨82804167354, 86435386968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239206400 276234240 279019520 ⟨⟨86578152194, 86578152200⟩, ⟨84751473211, 88417512453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239206400 239861760 276234240 279019520 ⟨⟨86196390188, 86196390193⟩, ⟨84374290798, 88031126954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 239206400 279019520 281804800 ⟨⟨87409565154, 87409565161⟩, ⟨85579206336, 89252613343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239206400 239861760 279019520 281804800 ⟨⟨87024444883, 87024444890⟩, ⟨85198673957, 88862861409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239861760 240517120 276234240 279019520 ⟨⟨85815494785, 85815494791⟩, ⟨83997956418, 87645626866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240517120 241172480 276234240 279019520 ⟨⟨85435460060, 85435460063⟩, ⟨83622464265, 87261006139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 240517120 279019520 281804800 ⟨⟨86640195049, 86640195055⟩, ⟨84818993460, 88473998702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240517120 241172480 279019520 281804800 ⟨⟨86256809709, 86256809712⟩, ⟨84440159026, 88086019152⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 270663680 281804800 t = true :=
  ⟨_, (join_sr (m := 276234240) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 273448960) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 239206400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 273448960) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240517120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239861760) (by decide) (join_sr (m := 279019520) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 239206400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 279019520) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240517120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
