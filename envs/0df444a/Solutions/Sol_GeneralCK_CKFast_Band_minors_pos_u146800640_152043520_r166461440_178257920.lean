-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_152043520_r166461440_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:39:45.49003+00:00
-- url     : https://prove2.me/submissions/ecbfa214-3f68-4c26-93d6-65eea29db08c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 29/160]`, `ρ ∈ [127/640, 17/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 148111360 166461440 169410560 ⟨⟨96754815026, 96754815028⟩, ⟨92599094172, 100974717237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 148111360 169410560 172359680 ⟨⟨98309687511, 98309687514⟩, ⟨94143829775, 102539641714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 148111360 149422080 166461440 169410560 ⟨⟨95935605013, 95935605022⟩, ⟨91807019951, 100127679696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 149422080 169410560 172359680 ⟨⟨97479397443, 97479397450⟩, ⟨93340703907, 101681500396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 148111360 172359680 175308800 ⟨⟨99860409306, 99860409310⟩, ⟨95684469922, 104100359614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 148111360 175308800 178257920 ⟨⟨101407015846, 101407015849⟩, ⟨97221049416, 105656907008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 148111360 149422080 172359680 175308800 ⟨⟨99019126781, 99019126790⟩, ⟨94870378538, 103231203582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 148111360 149422080 175308800 178257920 ⟨⟨100554827405, 100554827412⟩, ⟨96396077622, 104776824237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 149422080 150732800 166461440 169410560 ⟨⟨95124622007, 95124622016⟩, ⟨91022783947, 99289270790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 149422080 150732800 169410560 172359680 ⟨⟨96657401009, 96657401017⟩, ⟨92545483792, 100832053277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 150732800 152043520 166461440 169410560 ⟨⟨94321707923, 94321707931⟩, ⟨90246236447, 98459323746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 150732800 152043520 169410560 172359680 ⟨⟨95843539460, 95843539468⟩, ⟨91758019007, 99991132970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 150732800 172359680 175308800 ⟨⟨98186202727, 98186202734⟩, ⟨94064258691, 102370805486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 149422080 150732800 175308800 178257920 ⟨⟨99711060509, 99711060517⟩, ⟨95579141415, 103905561353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 150732800 152043520 172359680 175308800 ⟨⟨97361477771, 97361477777⟩, ⟨93265959279, 101518997376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 150732800 152043520 175308800 178257920 ⟨⟨98875555208, 98875555216⟩, ⟨94770089061, 103042949879⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 152043520 166461440 178257920 t = true :=
  ⟨_, (join_su (m := 149422080) (by decide) (join_sr (m := 172359680) (by decide) (join_su (m := 148111360) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 169410560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 148111360) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 175308800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 172359680) (by decide) (join_su (m := 150732800) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 169410560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 150732800) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 175308800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (127/640 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
