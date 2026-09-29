-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_20971520_r111411200_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:25:03.737989+00:00
-- url     : https://prove2.me/submissions/3b86ed8d-f988-4b5a-a76f-8ed641c047f8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/40]`, `ρ ∈ [17/128, 207/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 17825792 111411200 117473280 ⟨⟨244118171567, 244118171594⟩, ⟨225410595149, 263775820820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 17825792 18874368 111411200 117473280 ⟨⟨239375457404, 239375457431⟩, ⟨221156497011, 258506528738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 16777216 17825792 117473280 123535360 ⟨⟨251296385493, 251296385521⟩, ⟨232834569202, 270655059727⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 17825792 18874368 117473280 123535360 ⟨⟨246557200557, 246557200584⟩, ⟨228564132277, 265412755975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 18874368 19922944 111411200 117473280 ⟨⟨234831152833, 234831152860⟩, ⟨217075121028, 253463598872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 19922944 20971520 111411200 117473280 ⟨⟨230471647705, 230471647731⟩, ⟨213154910799, 248631194061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 18874368 19922944 117473280 123535360 ⟨⟨242010790997, 242010791025⟩, ⟨224462461723, 260389196688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 19922944 20971520 117473280 123535360 ⟨⟨237644205470, 237644205491⟩, ⟨220518489674, 255569405275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 16777216 17825792 123535360 129597440 ⟨⟨258230858325, 258230858352⟩, ⟨240008450768, 277300983246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 17825792 18874368 123535360 129597440 ⟨⟨253499013163, 253499013184⟩, ⟨235726650945, 272087924717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 16777216 17825792 129597440 135659520 ⟨⟨264940230707, 264940230735⟩, ⟨246950822254, 283731885465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 17825792 18874368 129597440 135659520 ⟨⟨260218900644, 260218900671⟩, ⟨242661921124, 278549822820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 18874368 19922944 123535360 129597440 ⟨⟨248954498201, 248954498223⟩, ⟨231609703135, 267086372060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 19922944 20971520 123535360 129597440 ⟨⟨244584973212, 244584973233⟩, ⟨227646999587, 262282136982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 18874368 19922944 129597440 135659520 ⟨⟨255679651002, 255679651023⟩, ⟨238534020730, 273572390929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 19922944 20971520 129597440 135659520 ⟨⟨251310708629, 251310708654⟩, ⟨234556946142, 268786124742⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 20971520 111411200 135659520 t = true :=
  ⟨_, (join_sr (m := 123535360) (by decide) (join_su (m := 18874368) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 17825792) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 17825792) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 117473280) (by decide) (join_su (m := 19922944) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 19922944) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 18874368) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 17825792) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 17825792) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 129597440) (by decide) (join_su (m := 19922944) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 19922944) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/40 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((20971520 : ℤ) : ℝ) / (D : ℝ)) = (1/40 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
