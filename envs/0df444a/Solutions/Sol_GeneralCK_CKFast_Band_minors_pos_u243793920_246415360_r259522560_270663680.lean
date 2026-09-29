-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:18:34.620577+00:00
-- url     : https://prove2.me/submissions/2bda2add-d7a4-4fb4-92a2-d21ae70473fc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 259522560 262307840 ⟨⟨78708054011, 78708054013⟩, ⟨76939212134, 80489176927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244449280 245104640 259522560 262307840 ⟨⟨78353179342, 78353179349⟩, ⟨76588720122, 80129876870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244449280 262307840 265093120 ⟨⟨79516154843, 79516154846⟩, ⟨77743689755, 81300910360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 262307840 265093120 ⟨⟨79157909092, 79157909098⟩, ⟨77389835435, 80938230558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245104640 245760000 259522560 262307840 ⟨⟨77999101309, 77999101315⟩, ⟨76239007063, 79771391360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245760000 246415360 259522560 262307840 ⟨⟨77645814408, 77645814414⟩, ⟨75890067573, 79413714777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245104640 245760000 262307840 265093120 ⟨⟨78800464102, 78800464107⟩, ⟨77036764202, 80576369417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245760000 246415360 262307840 265093120 ⟨⟨78443814352, 78443814358⟩, ⟨76684470656, 80215321301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244449280 265093120 267878400 ⟨⟨80323674197, 80323674200⟩, ⟨78547587628, 82112060531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244449280 245104640 265093120 267878400 ⟨⟨79962064642, 79962064649⟩, ⟨78190378219, 81746008323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244449280 267878400 270663680 ⟨⟨81130614840, 81130614843⟩, ⟨79350908513, 82922630221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244449280 245104640 267878400 270663680 ⟨⟨80765648721, 80765648726⟩, ⟨78990351195, 82553212904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 265093120 267878400 ⟨⟨79601259904, 79601259911⟩, ⟨77833955966, 81380778819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245760000 246415360 265093120 267878400 ⟨⟨79241254446, 79241254451⟩, ⟨77478315446, 81016366367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 245760000 267878400 270663680 ⟨⟨80401491403, 80401491410⟩, ⟨78630585030, 82184622265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 267878400 270663680 ⟨⟨80038137333, 80038137340⟩, ⟨78271604579, 81816852632⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 259522560 270663680 t = true :=
  ⟨_, (join_sr (m := 265093120) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 262307840) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244449280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 262307840) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245760000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 245104640) (by decide) (join_sr (m := 267878400) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244449280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 267878400) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245760000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
