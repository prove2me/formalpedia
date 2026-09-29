-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_154664960_r119275520_125173760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:10:14.278721+00:00
-- url     : https://prove2.me/submissions/36952daf-3da4-49b3-aed9-e32200ae45b3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 59/320]`, `ρ ∈ [91/640, 191/1280]` by 15 cells of the computing
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
theorem cell0 : cellOK 152043520 152698880 119275520 120750080 ⟨⟨68562373361, 68562373363⟩, ⟨66611814984, 70528596937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 152043520 152698880 120750080 122224640 ⟨⟨69353246101, 69353246106⟩, ⟨67399957635, 71322192762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152698880 153354240 119275520 120750080 ⟨⟨68261125599, 68261125605⟩, ⟨66316884282, 70220942708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 152698880 153354240 120750080 122224640 ⟨⟨69048912280, 69048912288⟩, ⟨67101947905, 71011445697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152043520 152698880 122224640 125173760 ⟨⟨70537488490, 70537488492⟩, ⟨68094236563, 73005425160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 152698880 153354240 122224640 123699200 ⟨⟨69835608370, 69835608377⟩, ⟨67885928354, 71800850623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 152698880 153354240 123699200 125173760 ⟨⟨70621218505, 70621218513⟩, ⟨68668830229, 72589162169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 153354240 154009600 119275520 120750080 ⟨⟨67961482532, 67961482539⟩, ⟨66023511612, 69914940716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 153354240 154009600 120750080 122224640 ⟨⟨68746195245, 68746195252⟩, ⟨66805508306, 70702362946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 154009600 154664960 119275520 120750080 ⟨⟨67663427943, 67663427949⟩, ⟨65731681279, 69610574212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154009600 154664960 120750080 122224640 ⟨⟨68445078687, 68445078695⟩, ⟨66510623056, 70394927669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 153354240 154009600 122224640 123699200 ⟨⟨69529829672, 69529829678⟩, ⟨67586434024, 71488699529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 153354240 154009600 123699200 125173760 ⟨⟨70312390376, 70312390383⟩, ⟨68366293291, 72273955072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154009600 154664960 122224640 123699200 ⟨⟨69225663315, 69225663322⟩, ⟨67288505917, 71178207757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154009600 154664960 123699200 125173760 ⟨⟨70005186313, 70005186321⟩, ⟨68065334311, 71960419008⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 154664960 119275520 125173760 t = true :=
  ⟨_, (join_su (m := 153354240) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 152698880) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 120750080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 152698880) (by decide) (leaf_ok cell4) (join_sr (m := 123699200) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 122224640) (by decide) (join_su (m := 154009600) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 120750080) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 154009600) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 123699200) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (59/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (191/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
