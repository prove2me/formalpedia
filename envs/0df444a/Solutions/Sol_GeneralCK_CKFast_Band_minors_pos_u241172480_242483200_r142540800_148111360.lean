-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_242483200_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:29:35.754921+00:00
-- url     : https://prove2.me/submissions/533aa1a9-eaa8-4766-a9be-c5f8f4ae8915

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 37/128]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241500160 142540800 143933440 ⟨⟨44873935901, 44873935906⟩, ⟨44056916154, 45693965891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241500160 241827840 142540800 143933440 ⟨⟨44770076362, 44770076364⟩, ⟨43954068009, 45589088930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241500160 143933440 145326080 ⟨⟨45299648147, 45299648152⟩, ⟨44481688638, 46120619290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241500160 241827840 143933440 145326080 ⟨⟨45194849155, 45194849158⟩, ⟨44377902501, 46014801423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241827840 242155520 142540800 143933440 ⟨⟨44666359214, 44666359219⟩, ⟨43851360003, 45484356639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 242155520 242483200 142540800 143933440 ⟨⟨44562783929, 44562783934⟩, ⟨43748791614, 45379768472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242155520 143933440 145326080 ⟨⟨45090193550, 45090193555⟩, ⟨44274257494, 45909129223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242155520 242483200 143933440 145326080 ⟨⟨44985680797, 44985680802⟩, ⟨44170753094, 45803602138⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241500160 145326080 146718720 ⟨⟨45725172760, 45725172765⟩, ⟨44906273808, 46547084736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241500160 241827840 145326080 146718720 ⟨⟨45619435537, 45619435539⟩, ⟨44801550893, 46440327189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 241500160 146718720 148111360 ⟨⟨46150510176, 46150510181⟩, ⟨45330672096, 46973362666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 241500160 241827840 146718720 148111360 ⟨⟨46043835938, 46043835940⟩, ⟨45225013615, 46865666659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 241827840 242155520 145326080 146718720 ⟨⟨45513842687, 45513842692⟩, ⟨44696970094, 46333716297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242155520 242483200 145326080 146718720 ⟨⟨45408393672, 45408393677⟩, ⟨44592530883, 46227251505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 241827840 242155520 146718720 148111360 ⟨⟨45937307052, 45937307059⟩, ⟨45119498230, 46758118290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 242155520 242483200 146718720 148111360 ⟨⟨45830922980, 45830922986⟩, ⟨45014125407, 46650717000⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 242483200 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 241500160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241500160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 242155520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 241827840) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 241500160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 241500160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 242155520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (37/128 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
