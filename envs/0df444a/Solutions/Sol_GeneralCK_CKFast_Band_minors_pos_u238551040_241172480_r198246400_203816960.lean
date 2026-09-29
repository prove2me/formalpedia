-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r198246400_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:52:22.51912+00:00
-- url     : https://prove2.me/submissions/48c18d0a-7eeb-4be1-9d1e-5eadfdb2d99a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [121/512, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 198246400 199639040 ⟨⟨62819917433, 62819917438⟩, ⟨61346795117, 64301803568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238551040 239206400 199639040 201031680 ⟨⟨63245179916, 63245179922⟩, ⟨61770321486, 64728807525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239206400 239861760 198246400 199639040 ⟨⟨62536358042, 62536358047⟩, ⟨61066292404, 64015159661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 199639040 201031680 ⟨⟨62959823212, 62959823217⟩, ⟨61488025712, 64440362088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239206400 201031680 202424320 ⟨⟨63670263211, 63670263218⟩, ⟨62193669054, 65155631901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238551040 239206400 202424320 203816960 ⟨⟨64095167747, 64095167752⟩, ⟨62616838246, 65582277122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239861760 201031680 202424320 ⟨⟨63383111444, 63383111451⟩, ⟨61909582455, 64865387196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239206400 239861760 202424320 203816960 ⟨⟨63806223161, 63806223166⟩, ⟨62330963049, 65290235407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240517120 198246400 199639040 ⟨⟨62253524856, 62253524863⟩, ⟨60786501665, 63729256368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239861760 240517120 199639040 201031680 ⟨⟨62675195783, 62675195790⟩, ⟨61206444979, 64152660333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 240517120 241172480 198246400 199639040 ⟨⟨61971412633, 61971412636⟩, ⟨60507417754, 63444088339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240517120 241172480 199639040 201031680 ⟨⟨62391292369, 62391292372⟩, ⟨60925574122, 63865696897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239861760 240517120 201031680 202424320 ⟨⟨63096692000, 63096692006⟩, ⟨61626213940, 64575889222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 240517120 202424320 203816960 ⟨⟨63518013921, 63518013927⟩, ⟨62045808958, 64998943450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 241172480 201031680 202424320 ⟨⟨62810999600, 62810999601⟩, ⟨61343558328, 64287132598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240517120 241172480 202424320 203816960 ⟨⟨63230534731, 63230534734⟩, ⟨61761370776, 64708395852⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 198246400 203816960 t = true :=
  ⟨_, (join_su (m := 239861760) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 199639040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 239206400) (by decide) (join_sr (m := 202424320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202424320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 201031680) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 199639040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 240517120) (by decide) (join_sr (m := 202424320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 202424320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (121/512 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
