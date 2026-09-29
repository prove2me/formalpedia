-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_218890240_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:21:19.92959+00:00
-- url     : https://prove2.me/submissions/80c67724-cbab-45a1-bbaf-2afb925d0bb3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 167/640]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 217579520 217907200 125829120 127221760 ⟨⟨46786249422, 46786249427⟩, ⟨45902542738, 47673447256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 217907200 218234880 125829120 127221760 ⟨⟨46682950306, 46682950311⟩, ⟨45800422630, 47568961315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 217579520 217907200 127221760 128614400 ⟨⟨47286029670, 47286029677⟩, ⟨46401264347, 48174287046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 217907200 218234880 127221760 128614400 ⟨⟨47181688695, 47181688702⟩, ⟨46298104053, 48068757584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 218234880 218562560 125829120 127221760 ⟨⟨46579823164, 46579823170⟩, ⟨45698471537, 47464650338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 218562560 218890240 125829120 127221760 ⟨⟨46476867316, 46476867320⟩, ⟨45596688794, 47360513623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218234880 218562560 127221760 128614400 ⟨⟨47077521060, 47077521067⟩, ⟨46195114139, 47963404452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218562560 218890240 127221760 128614400 ⟨⟨46973526078, 46973526082⟩, ⟨46092293931, 47858226943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 217907200 128614400 130007040 ⟨⟨47785505712, 47785505719⟩, ⟨46899682552, 48674821823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217907200 218234880 128614400 130007040 ⟨⟨47680124735, 47680124740⟩, ⟨46795483920, 48568250704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 217907200 130007040 131399680 ⟨⟨48284678349, 48284678356⟩, ⟨47397798152, 49175052391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217907200 218234880 130007040 131399680 ⟨⟨48178259217, 48178259222⟩, ⟨47292563021, 49067441469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218234880 218562560 128614400 130007040 ⟨⟨47574918451, 47574918456⟩, ⟨46691457020, 48461857268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218562560 218890240 128614400 130007040 ⟨⟨47469886171, 47469886175⟩, ⟨46587601175, 48355640811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218234880 218562560 130007040 131399680 ⟨⟨48072016124, 48072016130⟩, ⟨47187500966, 48960009580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218562560 218890240 130007040 131399680 ⟨⟨47965948375, 47965948379⟩, ⟨47082611306, 48852756011⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 218890240 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 218234880) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 217907200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 217907200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 218562560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 218562560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 218234880) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 217907200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 217907200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 218562560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 218562560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (167/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((218890240 : ℤ) : ℝ) / (D : ℝ)) = (167/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
