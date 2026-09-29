-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u224133120_225443840_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:44:43.48668+00:00
-- url     : https://prove2.me/submissions/f2260d2e-119e-4af9-a9ff-48819c6cf965

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [171/640, 43/160]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 224133120 224460800 131399680 132792320 ⟨⟨46667357150, 46667357157⟩, ⟨45802583750, 47535474922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 224460800 224788480 131399680 132792320 ⟨⟨46563319653, 46563319659⟩, ⟨45699674816, 47430301619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 224133120 224460800 132792320 134184960 ⟨⟨47145482860, 47145482865⟩, ⟨46279686456, 48014624701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 224460800 224788480 132792320 134184960 ⟨⟨47040436591, 47040436597⟩, ⟨46175770353, 47908441033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 224788480 225116160 131399680 132792320 ⟨⟨46459446111, 46459446117⟩, ⟨45596927101, 47325295035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225116160 225443840 131399680 132792320 ⟨⟨46355735887, 46355735889⟩, ⟨45494339979, 47220454513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 224788480 225116160 132792320 134184960 ⟨⟨46935555519, 46935555526⟩, ⟨46072016708, 47802425328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 225116160 225443840 132792320 134184960 ⟨⟨46830839003, 46830839006⟩, ⟨45968424893, 47696576924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 224133120 224460800 134184960 135577600 ⟨⟨47623342379, 47623342385⟩, ⟨46756523611, 48493507645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224460800 224788480 134184960 135577600 ⟨⟨47517288987, 47517288992⟩, ⟨46651601978, 48386315267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 224460800 135577600 136970240 ⟨⟨48100936384, 48100936389⟩, ⟨47233095887, 48972124434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224460800 224788480 135577600 136970240 ⟨⟨47993877509, 47993877514⟩, ⟨47127170359, 48863924995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224788480 225116160 134184960 135577600 ⟨⟨47411402023, 47411402030⟩, ⟨46546844035, 48279292085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225116160 225443840 134184960 135577600 ⟨⟨47305680844, 47305680846⟩, ⟨46442249147, 48172437437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224788480 225116160 135577600 136970240 ⟨⟨47886986287, 47886986293⟩, ⟨47021409743, 48755895977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 225116160 225443840 135577600 136970240 ⟨⟨47780262069, 47780262072⟩, ⟨46915813401, 48648036714⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 224133120 225443840 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 224788480) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 224460800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 224460800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 225116160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 225116160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 224788480) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 224460800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 224460800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 225116160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 225116160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (171/640 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((224133120 : ℤ) : ℝ) / (D : ℝ)) = (171/640 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
