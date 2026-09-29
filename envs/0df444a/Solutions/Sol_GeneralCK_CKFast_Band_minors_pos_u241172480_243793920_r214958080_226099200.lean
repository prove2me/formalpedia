-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:44:45.904555+00:00
-- url     : https://prove2.me/submissions/0c567134-05f2-4242-a9ee-9c492bee6972

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 214958080 217743360 ⟨⟨66904019367, 66904019372⟩, ⟨65176276947, 68644066073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241827840 242483200 214958080 217743360 ⟨⟨66601172983, 66601172988⟩, ⟨64877736766, 68336867999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241827840 217743360 220528640 ⟨⟨67735836341, 67735836347⟩, ⟨66004402531, 69479584215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 217743360 220528640 ⟨⟨67429474885, 67429474892⟩, ⟨65702357043, 69168861412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 242483200 243138560 214958080 217743360 ⟨⟨66299068030, 66299068037⟩, ⟨64579919782, 68030429859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243138560 243793920 214958080 217743360 ⟨⟨65997699229, 65997699236⟩, ⟨64282820842, 67724746244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243138560 217743360 220528640 ⟨⟨67123860310, 67123860317⟩, ⟨65401040199, 68858903992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243138560 243793920 217743360 220528640 ⟨⟨66818987306, 66818987313⟩, ⟨65100446819, 68549706515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241827840 220528640 223313920 ⟨⟨68566993416, 68566993421⟩, ⟨66831870380, 70314440241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241827840 242483200 220528640 223313920 ⟨⟨68257125198, 68257125203⟩, ⟨66526327828, 70000201086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 241827840 223313920 226099200 ⟨⟨69397493713, 69397493719⟩, ⟨67658683603, 71148637282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 241827840 242483200 223313920 226099200 ⟨⟨69084126994, 69084126999⟩, ⟨67349652181, 70830890105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 242483200 243138560 220528640 223313920 ⟨⟨67948009226, 67948009233⟩, ⟨66221519284, 69686732677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243138560 243793920 220528640 223313920 ⟨⟨67639640163, 67639640169⟩, ⟨65917439540, 69374029550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 242483200 243138560 223313920 226099200 ⟨⟨68771517804, 68771517810⟩, ⟨67041360051, 70513918953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243138560 243793920 223313920 226099200 ⟨⟨68459660779, 68459660786⟩, ⟨66733801976, 70197718340⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241827840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243138560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 242483200) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 241827840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 243138560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
