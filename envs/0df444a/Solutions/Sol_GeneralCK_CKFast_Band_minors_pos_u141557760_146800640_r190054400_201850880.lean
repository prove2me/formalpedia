-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_146800640_r190054400_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:34:34.585403+00:00
-- url     : https://prove2.me/submissions/56dc1f4b-9773-4f4c-9c4e-1795086fdc32

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 7/40]`, `ρ ∈ [29/128, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142868480 190054400 193003520 ⟨⟨112791867333, 112791867342⟩, ⟨108443295813, 117206662550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 141557760 142868480 193003520 195952640 ⟨⟨114356677575, 114356677584⟩, ⟨109998337006, 118781131655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 142868480 144179200 190054400 193003520 ⟨⟨111849857656, 111849857665⟩, ⟨107530216447, 116235018789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142868480 144179200 193003520 195952640 ⟨⟨113404043495, 113404043503⟩, ⟨109074645468, 117798856582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 142868480 195952640 198901760 ⟨⟨115917276305, 115917276313⟩, ⟨111549222497, 120351332868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 141557760 142868480 198901760 201850880 ⟨⟨117473700227, 117473700235⟩, ⟨113095988339, 121917303557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 142868480 144179200 195952640 198901760 ⟨⟨114954103872, 114954103880⟩, ⟨110615003463, 119358513903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 142868480 144179200 198901760 201850880 ⟨⟨116500074430, 116500074438⟩, ⟨112151325443, 120914027035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 144179200 145489920 190054400 193003520 ⟨⟨110917251186, 110917251195⟩, ⟨106626125447, 115273205912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 144179200 145489920 193003520 195952640 ⟨⟨112460867218, 112460867226⟩, ⟨108159998277, 116826465437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 145489920 146800640 190054400 193003520 ⟨⟨109993868426, 109993868435⟩, ⟨105730852238, 114321035187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 145489920 146800640 193003520 195952640 ⟨⟨111526968909, 111526968916⟩, ⟨107254224446, 115863769222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 144179200 145489920 195952640 198901760 ⟨⟨114000442162, 114000442169⟩, ⟨109689883100, 118375630211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 144179200 145489920 198901760 201850880 ⟨⟨115536010622, 115536010631⟩, ⟨111215813915, 119920735455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 145489920 146800640 195952640 198901760 ⟨⟨113056111030, 113056111037⟩, ⟨108773690048, 117402492555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 145489920 146800640 198901760 201850880 ⟨⟨114581328391, 114581328398⟩, ⟨110289282062, 118937239380⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 146800640 190054400 201850880 t = true :=
  ⟨_, (join_su (m := 144179200) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 142868480) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 193003520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 142868480) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 198901760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 195952640) (by decide) (join_su (m := 145489920) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 193003520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 145489920) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 198901760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (29/128 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
