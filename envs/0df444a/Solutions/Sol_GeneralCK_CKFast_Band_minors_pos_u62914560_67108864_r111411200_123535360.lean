-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u62914560_67108864_r111411200_123535360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:12:30.98942+00:00
-- url     : https://prove2.me/submissions/8f62d270-f624-4a03-98fa-a6bb2b3b45c1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/40, 2/25]`, `ρ ∈ [17/128, 377/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 62914560 63963136 111411200 114442240 ⟨⟨130680791925, 130680791936⟩, ⟨124288319495, 137220986106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 62914560 63963136 114442240 117473280 ⟨⟨133546155610, 133546155621⟩, ⟨127146627706, 140092031142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 63963136 65011712 111411200 114442240 ⟨⟨129315465305, 129315465319⟩, ⟨122996595950, 135779134610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 63963136 65011712 114442240 117473280 ⟨⟨132160874161, 132160874172⟩, ⟨125834643075, 138630586728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 62914560 63963136 117473280 120504320 ⟨⟨136386956122, 136386956133⟩, ⟨129980753735, 142938145850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 62914560 63963136 120504320 123535360 ⟨⟨139203686406, 139203686420⟩, ⟨132791176105, 145759837533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 63963136 65011712 117473280 120504320 ⟨⟨134982244770, 134982244781⟩, ⟨128649025892, 141457639504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 63963136 65011712 120504320 123535360 ⟨⟨137780053530, 137780053544⟩, ⟨131440206914, 144260783171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 65011712 66060288 111411200 114442240 ⟨⟨127976268581, 127976268586⟩, ⟨121729210788, 134365296304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 65011712 66060288 114442240 117473280 ⟨⟨130801868742, 130801868747⟩, ⟨124547162778, 137197279193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 66060288 67108864 111411200 114442240 ⟨⟨126662382805, 126662382818⟩, ⟨120485410011, 132978583451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 66060288 67108864 114442240 117473280 ⟨⟨129468322160, 129468322174⟩, ⟨123283433390, 135791223871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 65011712 66060288 117473280 120504320 ⟨⟨133603942569, 133603942571⟩, ⟨127341955327, 140005380768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 65011712 66060288 120504320 123535360 ⟨⟨136382950539, 136382950545⟩, ⟨130114035550, 142790074841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 66060288 67108864 117473280 120504320 ⟨⟨132251234428, 132251234439⟩, ⟨126058789558, 138580488388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 66060288 67108864 120504320 123535360 ⟨⟨135011564789, 135011564800⟩, ⟨128811910829, 141346835023⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 62914560 67108864 111411200 123535360 t = true :=
  ⟨_, (join_su (m := 65011712) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 63963136) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114442240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 63963136) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 120504320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 117473280) (by decide) (join_su (m := 66060288) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114442240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 66060288) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 120504320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/40 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (377/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
