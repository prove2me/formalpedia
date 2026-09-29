-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u234618880_235929600_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:22:47.765104+00:00
-- url     : https://prove2.me/submissions/657c76c0-ec71-4f12-be01-7b4c2356de6d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [179/640, 9/32]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 234618880 234946560 131399680 132792320 ⟨⟨43416410140, 43416410147⟩, ⟨42586445747, 44249499193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 234946560 235274240 131399680 132792320 ⟨⟨43317316016, 43317316018⟩, ⟨42488397759, 44149352443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 234618880 234946560 132792320 134184960 ⟨⟨43862851149, 43862851154⟩, ⟨43031914034, 44696914225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 234946560 235274240 132792320 134184960 ⟨⟨43762786020, 43762786023⟩, ⟨42932896581, 44595794937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235274240 235601920 131399680 132792320 ⟨⟨43218366748, 43218366755⟩, ⟨42390492216, 44049352992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235601920 235929600 131399680 132792320 ⟨⟨43119561790, 43119561796⟩, ⟨42292728576, 43949500272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 235274240 235601920 132792320 134184960 ⟨⟨43662866867, 43662866872⟩, ⟨42834022688, 44494824069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235601920 235929600 132792320 134184960 ⟨⟨43563093135, 43563093140⟩, ⟨42735291809, 44394001048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 234618880 234946560 134184960 135577600 ⟨⟨44309074574, 44309074579⟩, ⟨43477165169, 45144111237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 234946560 235274240 134184960 135577600 ⟨⟨44208039830, 44208039834⟩, ⟨43377179635, 45042020809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 234946560 135577600 136970240 ⟨⟨44755080935, 44755080942⟩, ⟨43922199671, 45591090753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234946560 235274240 135577600 136970240 ⟨⟨44653077963, 44653077967⟩, ⟨43821247435, 45488030575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 235274240 235601920 134184960 135577600 ⟨⟨44107152172, 44107152177⟩, ⟨43277338767, 44940079912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235601920 235929600 134184960 135577600 ⟨⟨44006411043, 44006411048⟩, ⟨43177642020, 44838287970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 235274240 235601920 135577600 136970240 ⟨⟨44551223179, 44551223186⟩, ⟨43720440967, 45385121033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235601920 235929600 135577600 136970240 ⟨⟨44449516022, 44449516029⟩, ⟨43619779716, 45282361547⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 234618880 235929600 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 235274240) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 234946560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235601920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 235274240) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 234946560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235601920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (179/640 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
