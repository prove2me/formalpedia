-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r393216000_415498240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:26:27.431512+00:00
-- url     : https://prove2.me/submissions/a5f4ccb5-566f-4e6c-8aa1-c03d51c1c81e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [15/32, 317/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 393216000 398786560 ⟨⟨131708904625, 131708904629⟩, ⟨127562410996, 135910372938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226754560 228065280 393216000 398786560 ⟨⟨130632865221, 130632865228⟩, ⟨126507205698, 134813171972⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226754560 398786560 404357120 ⟨⟨133443566771, 133443566775⟩, ⟨129282263072, 137659862037⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 398786560 404357120 ⟨⟨132355156062, 132355156069⟩, ⟨128214726757, 136550252643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228065280 229376000 393216000 398786560 ⟨⟨129561203560, 129561203566⟩, ⟨125456224655, 133720505005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 229376000 230686720 393216000 398786560 ⟨⟨128493864244, 128493864252⟩, ⟨124409414314, 132632314770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228065280 229376000 398786560 404357120 ⟨⟨131271132401, 131271132408⟩, ⟨127151424874, 135445185609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229376000 230686720 398786560 404357120 ⟨⟨130191440477, 130191440484⟩, ⟨126092303939, 134344603772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226754560 404357120 409927680 ⟨⟨135175732199, 135175732201⟩, ⟨130999639647, 139406832062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226754560 228065280 404357120 409927680 ⟨⟨134075004805, 134075004812⟩, ⟨129919825994, 138284869822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226754560 409927680 415498240 ⟨⟨136905428277, 136905428281⟩, ⟨132714567804, 141151310667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226754560 228065280 409927680 415498240 ⟨⟨135792438103, 135792438111⟩, ⟨131622529790, 140017050429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 404357120 409927680 ⟨⟨132978672880, 132978672886⟩, ⟨128844256085, 137167457394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229376000 230686720 404357120 409927680 ⟨⟨131886681208, 131886681214⟩, ⟨127772876506, 136054537741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 229376000 409927680 415498240 ⟨⟨134683850947, 134683850955⟩, ⟨130534743976, 138887346575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 409927680 415498240 ⟨⟨133579611700, 133579611706⟩, ⟨129451157031, 137762142194⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 393216000 415498240 t = true :=
  ⟨_, (join_sr (m := 404357120) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 398786560) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226754560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 398786560) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 229376000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 228065280) (by decide) (join_sr (m := 409927680) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226754560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 409927680) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 229376000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (317/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
