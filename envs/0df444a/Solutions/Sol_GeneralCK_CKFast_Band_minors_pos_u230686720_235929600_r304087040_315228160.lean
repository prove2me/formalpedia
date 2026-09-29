-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r304087040_315228160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:31:41.240264+00:00
-- url     : https://prove2.me/submissions/6d687350-d370-4fa8-a39f-1398317b2be7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [29/80, 481/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 304087040 306872320 ⟨⟨99704000217, 99704000225⟩, ⟨96424685244, 103021072947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231997440 306872320 309657600 ⟨⟨100567311525, 100567311531⟩, ⟨97281021695, 103891390944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 233308160 304087040 306872320 ⟨⟨98853318470, 98853318473⟩, ⟨95587957086, 102156225978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 306872320 309657600 ⟨⟨99709990572, 99709990575⟩, ⟨96437679368, 103019880536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231997440 309657600 312442880 ⟨⟨101429942092, 101429942100⟩, ⟨98136681010, 104761024392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231997440 312442880 315228160 ⟨⟨102291895404, 102291895411⟩, ⟨98991666649, 105629976796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 233308160 309657600 312442880 ⟨⟨100565997739, 100565997742⟩, ⟨97286740104, 103882866570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231997440 233308160 312442880 315228160 ⟨⟨101421343356, 101421343360⟩, ⟨98135142654, 104745187486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 234618880 304087040 306872320 ⟨⟨98006508663, 98006508669⟩, ⟨94754982183, 101295371904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233308160 234618880 306872320 309657600 ⟨⟨98856554533, 98856554539⟩, ⟨95598103461, 102152375783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 235929600 304087040 306872320 ⟨⟨97163518835, 97163518843⟩, ⟨93925710122, 100438457172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234618880 235929600 306872320 309657600 ⟨⟨98006951375, 98006951381⟩, ⟨94762243481, 101288823070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 309657600 312442880 ⟨⟨99705950990, 99705950997⟩, ⟨96440578502, 103008726878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 233308160 234618880 312442880 315228160 ⟨⟨100554701323, 100554701330⟩, ⟨97282410573, 103864428494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235929600 309657600 312442880 ⟨⟨98849749743, 98849749749⟩, ⟨95598145637, 102138551637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 312442880 315228160 ⟨⟨99691917134, 99691917141⟩, ⟨96433419764, 102987646085⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 304087040 315228160 t = true :=
  ⟨_, (join_su (m := 233308160) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 306872320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231997440) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 312442880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 309657600) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 306872320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 234618880) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 312442880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (481/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
