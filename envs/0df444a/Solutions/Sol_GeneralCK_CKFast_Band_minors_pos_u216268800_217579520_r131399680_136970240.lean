-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u216268800_217579520_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:19:46.60288+00:00
-- url     : https://prove2.me/submissions/3c3a595d-eb2b-455b-ae97-0be5902a2791

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/128, 83/320]`, `ρ ∈ [401/2560, 209/1280]` by 12 cells of the computing
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
theorem cell0 : cellOK 216268800 216596480 131399680 132792320 ⟨⟨49215158054, 49215158061⟩, ⟨48322449108, 50111393118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 216596480 216924160 131399680 132792320 ⟨⟨49106986029, 49106986036⟩, ⟨48215474718, 50002015569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 216268800 216596480 132792320 134184960 ⟨⟨49717877528, 49717877533⟩, ⟨48824106556, 50615175458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216596480 216924160 132792320 134184960 ⟨⟨49608665679, 49608665685⟩, ⟨48716093989, 50504756448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 216924160 217251840 131399680 132792320 ⟨⟨48998994220, 48998994222⟩, ⟨48108677530, 49892821273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 217251840 217579520 131399680 132792320 ⟨⟨48891181905, 48891181912⟩, ⟨48002056836, 49783809510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216924160 217251840 132792320 134184960 ⟨⟨49499635389, 49499635391⟩, ⟨48608259967, 50394522035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 217251840 217579520 132792320 134184960 ⟨⟨49390785933, 49390785938⟩, ⟨48500603775, 50284471497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 216268800 216924160 134184960 135577600 ⟨⟨50165140761, 50165140768⟩, ⟨48666512509, 51673395082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 216268800 216924160 135577600 136970240 ⟨⟨50666725977, 50666725984⟩, ⟨49166167083, 52176915615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 216924160 217579520 134184960 135577600 ⟨⟨49945006752, 49945006759⟩, ⟨48449764993, 51449837644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 216924160 217579520 135577600 136970240 ⟨⟨50444522428, 50444522434⟩, ⟨48947355394, 51951283315⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 216268800 217579520 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 216924160) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 216596480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 216596480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 217251840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 217251840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 216924160) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 135577600) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/128 : ℝ) (83/320 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((216268800 : ℤ) : ℝ) / (D : ℝ)) = (33/128 : ℝ) := by norm_num [D]
  have e1 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
