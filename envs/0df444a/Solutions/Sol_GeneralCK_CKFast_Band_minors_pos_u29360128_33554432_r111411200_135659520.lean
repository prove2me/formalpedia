-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u29360128_33554432_r111411200_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:26:35.396105+00:00
-- url     : https://prove2.me/submissions/42fd0d55-0c52-44be-b488-8272adfb4d9a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/200, 1/25]`, `ρ ∈ [17/128, 207/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 29360128 30408704 111411200 117473280 ⟨⟨197849111171, 197849111192⟩, ⟨183670562951, 212640119886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 30408704 31457280 111411200 117473280 ⟨⟨194813856909, 194813856930⟩, ⟨180913865131, 209306847669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 29360128 30408704 117473280 123535360 ⟨⟨204810281208, 204810281226⟩, ⟨190720696859, 219487454282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 30408704 31457280 117473280 123535360 ⟨⟨201741078360, 201741078377⟩, ⟨187922493359, 216129165627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 31457280 32505856 111411200 117473280 ⟨⟨191873932398, 191873932419⟩, ⟨178241551698, 206080789857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 32505856 33554432 111411200 117473280 ⟨⟨189024512471, 189024512491⟩, ⟨175649436433, 202956422426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 31457280 32505856 117473280 123535360 ⟨⟨198765946587, 198765946607⟩, ⟨185207949958, 212876203802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 32505856 33554432 117473280 123535360 ⟨⟨195880219321, 195880219341⟩, ⟨182572995738, 209723254526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 29360128 30408704 123535360 129597440 ⟨⟨211578480737, 211578480754⟩, ⟨197578908391, 226142115521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 30408704 31457280 123535360 129597440 ⟨⟨208479500021, 208479500042⟩, ⟨194743595646, 222762646375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 29360128 30408704 129597440 135659520 ⟨⟨218165619782, 218165619803⟩, ⟨204256714234, 232616314933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 30408704 31457280 129597440 135659520 ⟨⟨215040582641, 215040582658⟩, ⟨201388241895, 229219059534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 31457280 32505856 123535360 129597440 ⟨⟨205473268416, 205473268432⟩, ⟨191991124524, 219486594047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 32505856 33554432 123535360 129597440 ⟨⟨202555273342, 202555273359⟩, ⟨189317538377, 216308844797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 31457280 32505856 129597440 135659520 ⟨⟨212006926734, 212006926755⟩, ⟨198601717545, 225923303095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 32505856 33554432 129597440 135659520 ⟨⟨209060288451, 209060288469⟩, ⟨195893297014, 222724123232⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 29360128 33554432 111411200 135659520 t = true :=
  ⟨_, (join_sr (m := 123535360) (by decide) (join_su (m := 31457280) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 30408704) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 30408704) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 117473280) (by decide) (join_su (m := 32505856) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 32505856) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 31457280) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 30408704) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 30408704) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 129597440) (by decide) (join_su (m := 32505856) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 32505856) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/200 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
