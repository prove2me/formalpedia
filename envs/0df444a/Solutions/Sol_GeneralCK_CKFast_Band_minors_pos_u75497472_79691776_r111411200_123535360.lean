-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_79691776_r111411200_123535360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:46:13.679058+00:00
-- url     : https://prove2.me/submissions/53be4c99-daf8-4e86-be76-e69a95fddda8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 19/200]`, `ρ ∈ [17/128, 377/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 76546048 111411200 114442240 ⟨⟨115857121490, 115857121500⟩, ⟨110242533518, 121589666837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 75497472 76546048 114442240 117473280 ⟨⟨118492918065, 118492918077⟩, ⟨112868682646, 124234259175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 76546048 77594624 111411200 114442240 ⟨⟨114758119108, 114758119120⟩, ⟨109199321977, 120432836702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 76546048 77594624 114442240 117473280 ⟨⟨117375771595, 117375771607⟩, ⟨111807195401, 123059448604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 76546048 117473280 120504320 ⟨⟨121109666737, 121109666747⟩, ⟨115476083269, 126859509767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 75497472 76546048 120504320 123535360 ⟨⟨123707698415, 123707698425⟩, ⟨118065057161, 129465758693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 76546048 77594624 117473280 120504320 ⟨⟨119974766854, 119974766866⟩, ⟨114396704695, 125667115313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 76546048 77594624 120504320 123535360 ⟨⟨122555425319, 122555425332⟩, ⟨116968161491, 128256166100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 77594624 78643200 111411200 114442240 ⟨⟨113677357461, 113677357471⟩, ⟨108173169156, 119295485648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 77594624 78643200 114442240 117473280 ⟨⟨116277017046, 116277017058⟩, ⟨110762927802, 121904257200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 78643200 79691776 111411200 114442240 ⟨⟨112614334420, 112614334430⟩, ⟨107163610379, 118177071986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 78643200 79691776 114442240 117473280 ⟨⟨115196151641, 115196151653⟩, ⟨109735413987, 120768143235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 77594624 78643200 117473280 120504320 ⟨⟨118858400824, 118858400836⟩, ⟨113334697536, 124494470788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 77594624 78643200 120504320 123535360 ⟨⟨121421819131, 121421819143⟩, ⟨115888780214, 127066445263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 78643200 79691776 117473280 120504320 ⟨⟨117760065476, 117760065488⟩, ⟨112289594999, 123341034678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 78643200 79691776 120504320 123535360 ⟨⟨120306376528, 120306376540⟩, ⟨114826445852, 125896055120⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 79691776 111411200 123535360 t = true :=
  ⟨_, (join_su (m := 77594624) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 76546048) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114442240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 76546048) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 120504320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 117473280) (by decide) (join_su (m := 78643200) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114442240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 78643200) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 120504320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (377/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
