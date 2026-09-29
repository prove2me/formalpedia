-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:32:24.294659+00:00
-- url     : https://prove2.me/submissions/4a858cdf-98e2-4f52-8505-6190cf539183

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 214958080 217743360 ⟨⟨71854867232, 71854867236⟩, ⟨70055637169, 73667167646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231342080 231997440 214958080 217743360 ⟨⟨71539405420, 71539405426⟩, ⟨69744791613, 73347039495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231342080 217743360 220528640 ⟨⟨72743689940, 72743689942⟩, ⟨70940612269, 74559845770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 217743360 220528640 ⟨⟨72424621931, 72424621938⟩, ⟨70626170266, 74236101813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 231997440 232652800 214958080 217743360 ⟨⟨71224775331, 71224775336⟩, ⟨69434757341, 73027763809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 232652800 233308160 214958080 217743360 ⟨⟨70910970979, 70910970986⟩, ⟨69125528514, 72709334457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 232652800 217743360 220528640 ⟨⟨72106391563, 72106391569⟩, ⟨70312545467, 73913216232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 232652800 233308160 217743360 220528640 ⟨⟨71788992820, 71788992827⟩, ⟨69999732005, 73591182865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231342080 220528640 223313920 ⟨⟨73631707935, 73631707940⟩, ⟨71824786022, 75451715756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231342080 231997440 220528640 223313920 ⟨⟨73309043467, 73309043474⟩, ⟨71506757225, 75124365811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231342080 223313920 226099200 ⟨⟨74518925214, 74518925218⟩, ⟨72708162401, 76342781615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231342080 231997440 223313920 226099200 ⟨⟨74192673961, 74192673967⟩, ⟨72386556405, 76011835438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 232652800 220528640 223313920 ⟨⟨72987222460, 72987222466⟩, ⟨71189551459, 74797880056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 232652800 233308160 220528640 223313920 ⟨⟨72666238871, 72666238878⟩, ⟨70873162825, 74472252302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 231997440 232652800 223313920 226099200 ⟨⟨73867271896, 73867271902⟩, ⟨72065779171, 75681759173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232652800 233308160 223313920 226099200 ⟨⟨73542712949, 73542712956⟩, ⟨71745824776, 75352546599⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 231342080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231342080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 232652800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 232652800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 231997440) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 231342080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231342080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 232652800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 232652800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
