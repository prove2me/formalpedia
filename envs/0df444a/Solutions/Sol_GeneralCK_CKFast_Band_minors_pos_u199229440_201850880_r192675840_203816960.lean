-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_201850880_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:17:03.905905+00:00
-- url     : https://prove2.me/submissions/3e1f9f7c-404d-4e24-8c07-6d9abdcb8444

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 77/320]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 199884800 192675840 195461120 ⟨⟨79498458921, 79498458928⟩, ⟨77485050540, 81527770241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199884800 200540160 192675840 195461120 ⟨⟨79166942445, 79166942451⟩, ⟨77159260495, 81190456748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 199884800 195461120 198246400 ⟨⟨80579452736, 80579452742⟩, ⟨78561671501, 82613135817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 199884800 200540160 195461120 198246400 ⟨⟨80243881840, 80243881846⟩, ⟨78231837145, 82271758071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 200540160 201195520 192675840 195461120 ⟨⟨78836548033, 78836548041⟩, ⟨76834562738, 80854295599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201195520 201850880 192675840 195461120 ⟨⟨78507266959, 78507266962⟩, ⟨76510948789, 80519277806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 200540160 201195520 195461120 198246400 ⟨⟨79909441657, 79909441664⟩, ⟨77903103749, 81931541290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201195520 201850880 195461120 198246400 ⟨⟨79576123417, 79576123422⟩, ⟨77575462785, 81592476448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 199884800 198246400 201031680 ⟨⟨81658978310, 81658978317⟩, ⟨79636833389, 83697023883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 199884800 200540160 198246400 201031680 ⟨⟨81319369370, 81319369377⟩, ⟨79302970944, 83351598414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 199884800 201031680 203816960 ⟨⟨82737044169, 82737044175⟩, ⟨80710544660, 84779443025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 199884800 200540160 201031680 203816960 ⟨⟨82393413434, 82393413442⟩, ⟨80372670226, 84429986233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 200540160 201195520 198246400 201031680 ⟨⟨80980899636, 80980899643⟩, ⟨78970217975, 83007342372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 201195520 201850880 198246400 201031680 ⟨⟨80643560293, 80643560297⟩, ⟨78638565911, 82664246692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 200540160 201195520 201031680 203816960 ⟨⟨82050930244, 82050930250⟩, ⟨80035913630, 84081707176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 201195520 201850880 201031680 203816960 ⟨⟨81709585738, 81709585741⟩, ⟨79700266256, 83734596749⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 201850880 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 199884800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 201195520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 200540160) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 199884800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 201195520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (77/320 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
