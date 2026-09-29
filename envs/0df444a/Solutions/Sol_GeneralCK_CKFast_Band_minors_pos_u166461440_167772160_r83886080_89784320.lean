-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u166461440_167772160_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:19:16.425127+00:00
-- url     : https://prove2.me/submissions/59425435-3be5-4d66-a623-67279d504479

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [127/640, 1/5]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 166461440 166789120 83886080 85360640 ⟨⟨44649839267, 44649839275⟩, ⟨43554078952, 45751078927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 166789120 167116800 83886080 85360640 ⟨⟨44550498941, 44550498947⟩, ⟨43456575454, 45649885078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 166461440 166789120 85360640 86835200 ⟨⟨45397907692, 45397907698⟩, ⟨44300601519, 46500690935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 166789120 167116800 85360640 86835200 ⟨⟨45297019192, 45297019198⟩, ⟨44201552709, 46397946092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167116800 167444480 83886080 85360640 ⟨⟨44451413345, 44451413351⟩, ⟨43359320497, 45548952227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167444480 167772160 83886080 85360640 ⟨⟨44352581212, 44352581219⟩, ⟨43262312850, 45448279077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 167116800 167444480 85360640 86835200 ⟨⟨45196388726, 45196388732⟩, ⟨44102755738, 46295465554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 167444480 167772160 85360640 86835200 ⟨⟨45096015012, 45096015018⟩, ⟨44004209361, 46193248009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 166461440 166789120 86835200 88309760 ⟨⟨46145029849, 46145029856⟩, ⟨45046181935, 47249352551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 166789120 167116800 86835200 88309760 ⟨⟨46042598756, 46042598764⟩, ⟨44945593360, 47145062325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 166461440 166789120 88309760 89784320 ⟨⟨46891209470, 46891209476⟩, ⟨45790823903, 47997067523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 166789120 167116800 88309760 89784320 ⟨⟨46787241333, 46787241339⟩, ⟨45688701080, 47891237497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 167116800 167444480 86835200 88309760 ⟨⟨45940428968, 45940428974⟩, ⟨44845259890, 47041039681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 167444480 167772160 86835200 88309760 ⟨⟨45838519187, 45838519193⟩, ⟨44745180266, 46937283289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 167116800 167444480 88309760 89784320 ⟨⟨46683537738, 46683537744⟩, ⟨45586836596, 47785678294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 167444480 167772160 88309760 89784320 ⟨⟨46580097375, 46580097381⟩, ⟨45485229177, 47680388572⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 166461440 167772160 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 167116800) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 166789120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 166789120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 167444480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 167444480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 167116800) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 166789120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 166789120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 88309760) (by decide) (join_su (m := 167444480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 167444480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (127/640 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
