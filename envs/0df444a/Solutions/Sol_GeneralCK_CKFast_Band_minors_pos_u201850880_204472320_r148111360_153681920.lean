-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u201850880_204472320_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:52:39.729583+00:00
-- url     : https://prove2.me/submissions/d43319c3-7f3d-472b-96d6-cc6c26606d24

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [77/320, 39/160]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 201850880 202506240 148111360 149504000 ⟨⟨60671858364, 60671858371⟩, ⟨59073402516, 62280859789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 202506240 149504000 150896640 ⟨⟨61216453863, 61216453870⟩, ⟨59615964255, 62827492302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 202506240 203161600 148111360 149504000 ⟨⟨60412417506, 60412417512⟩, ⟨58817840719, 62017497000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 202506240 203161600 149504000 150896640 ⟨⟨60954864004, 60954864009⟩, ⟨59358258726, 62561975307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 202506240 150896640 152289280 ⟨⟨61760662987, 61760662994⟩, ⟨60158141367, 63373736670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201850880 202506240 152289280 153681920 ⟨⟨62304486846, 62304486852⟩, ⟨60699934958, 63919594007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 202506240 203161600 150896640 152289280 ⟨⟨61496928596, 61496928601⟩, ⟨59898296545, 63106069972⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 202506240 203161600 152289280 153681920 ⟨⟨62038612379, 62038612385⟩, ⟨60437955266, 63649782095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 203161600 203816960 148111360 149504000 ⟨⟨60153903805, 60153903811⟩, ⟨58563184269, 61755083494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 203161600 203816960 149504000 150896640 ⟨⟨60694206917, 60694206922⟩, ⟨59101464157, 62297413217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203816960 204472320 148111360 149504000 ⟨⟨59896309775, 59896309783⟩, ⟨58309425872, 61493611604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 203816960 204472320 149504000 150896640 ⟨⟨60434475086, 60434475093⟩, ⟨58845573219, 62033798331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 203161600 203816960 150896640 152289280 ⟨⟨61234132551, 61234132557⟩, ⟨59639368253, 62839363758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203161600 203816960 152289280 153681920 ⟨⟨61773681786, 61773681791⟩, ⟨60176897625, 63380936200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203816960 204472320 150896640 152289280 ⟨⟨60972267301, 60972267307⟩, ⟨59381349120, 62573610290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203816960 204472320 152289280 153681920 ⟨⟨61509687481, 61509687486⟩, ⟨59916754633, 63113048546⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 201850880 204472320 148111360 153681920 t = true :=
  ⟨_, (join_su (m := 203161600) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 202506240) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 149504000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 202506240) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 152289280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 150896640) (by decide) (join_su (m := 203816960) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 149504000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 203816960) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 152289280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (77/320 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
