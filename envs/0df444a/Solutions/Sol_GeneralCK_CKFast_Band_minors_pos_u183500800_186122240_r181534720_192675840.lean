-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_186122240_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:22:10.774016+00:00
-- url     : https://prove2.me/submissions/3bff26f8-bdd9-4a8e-8199-acaace5f4f4e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 71/320]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184156160 181534720 184320000 ⟨⟨83072314948, 83072314955⟩, ⟨80930408701, 85232016849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184156160 184811520 181534720 184320000 ⟨⟨82728327326, 82728327332⟩, ⟨80592904672, 84881459864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 183500800 184156160 184320000 187105280 ⟨⟨84261099564, 84261099572⟩, ⟨82114532267, 86425453943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184156160 184811520 184320000 187105280 ⟨⟨83912752071, 83912752077⟩, ⟨81772678469, 86070527376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 184811520 185466880 181534720 184320000 ⟨⟨82385658075, 82385658080⟩, ⟨80256682235, 84532258691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 185466880 186122240 181534720 184320000 ⟨⟨82044296329, 82044296337⟩, ⟨79921730854, 84184402130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184811520 185466880 184320000 187105280 ⟨⟨83565733507, 83565733512⟩, ⟨81432116859, 85716967134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 185466880 186122240 184320000 187105280 ⟨⟨83220032953, 83220032959⟩, ⟨81092836845, 85364761965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184156160 187105280 189890560 ⟨⟨85447922235, 85447922243⟩, ⟨83296707709, 87616915140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184156160 184811520 187105280 189890560 ⟨⟨85095236230, 85095236237⟩, ⟨82950525292, 87257640561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 184156160 189890560 192675840 ⟨⟨86632795430, 86632795436⟩, ⟨84476947386, 88806413020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 184156160 184811520 189890560 192675840 ⟨⟨86275792087, 86275792093⟩, ⟨84126457319, 88442811810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 184811520 185466880 187105280 189890560 ⟨⟨84743889504, 84743889507⟩, ⟨82605645453, 86899742608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 185466880 186122240 187105280 189890560 ⟨⟨84393871085, 84393871091⟩, ⟨82262057550, 86543209980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 184811520 185466880 189890560 192675840 ⟨⟨85920138171, 85920138172⟩, ⟨83777280019, 88080597323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 185466880 186122240 189890560 192675840 ⟨⟨85565822653, 85565822659⟩, ⟨83429404791, 87719758205⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 186122240 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 184811520) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 184156160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 184156160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 185466880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 185466880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 184811520) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 184156160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 184156160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 185466880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 185466880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (71/320 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
