-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_167772160_r178257920_190054400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:52:35.466037+00:00
-- url     : https://prove2.me/submissions/d09ca161-2a7e-4bbe-adab-dabb1332ac05

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 1/5]`, `ρ ∈ [17/80, 29/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163840000 178257920 181207040 ⟨⟨93119869935, 93119869941⟩, ⟨89227101485, 97069145783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162529280 163840000 181207040 184156160 ⟨⟨94533343288, 94533343295⟩, ⟨90630985415, 98492168391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163840000 165150720 178257920 181207040 ⟨⟨92348878823, 92348878831⟩, ⟨88479223917, 96274496960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163840000 165150720 181207040 184156160 ⟨⟨93752297966, 93752297973⟩, ⟨89873085768, 97687436402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 163840000 184156160 187105280 ⟨⟨95943704508, 95943704515⟩, ⟨92031795350, 99912040131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 163840000 187105280 190054400 ⟨⟨97350977381, 97350977388⟩, ⟨93429554711, 101328785157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163840000 165150720 184156160 187105280 ⟨⟨95152670623, 95152670632⟩, ⟨91263938214, 99097291690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163840000 165150720 187105280 190054400 ⟨⟨96550019889, 96550019897⟩, ⟨92651803998, 100504086268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 165150720 166461440 178257920 181207040 ⟨⟨91584681503, 91584681511⟩, ⟨87737839659, 95486951578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165150720 166461440 181207040 184156160 ⟨⟨92978099855, 92978099862⟩, ⟨89121733395, 96889860636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 166461440 167772160 178257920 181207040 ⟨⟨90827157820, 90827157823⟩, ⟨87002834430, 94706383396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 166461440 167772160 181207040 184156160 ⟨⟨92210628284, 92210628286⟩, ⟨88376813464, 96099314363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165150720 166461440 184156160 187105280 ⟨⟨94368536084, 94368536090⟩, ⟨90502681050, 98289750940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 166461440 187105280 190054400 ⟨⟨95756012603, 95756012611⟩, ⟨91880704703, 99686645247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 166461440 167772160 184156160 187105280 ⟨⟨93591179718, 93591179722⟩, ⟨89747908499, 97489290693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166461440 167772160 187105280 190054400 ⟨⟨94968833887, 94968833891⟩, ⟨91116140973, 98876334472⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 167772160 178257920 190054400 t = true :=
  ⟨_, (join_su (m := 165150720) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 163840000) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 181207040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 163840000) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 187105280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184156160) (by decide) (join_su (m := 166461440) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 181207040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 166461440) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 187105280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (29/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
