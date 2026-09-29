-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r187105280_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:03:02.03107+00:00
-- url     : https://prove2.me/submissions/9c0ebda2-5efb-4491-962f-9c652b9157f0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [571/2560, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 187105280 188497920 ⟨⟨58339103562, 58339103567⟩, ⟨56891887842, 59794928530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 241827840 188497920 189890560 ⟨⟨58758572244, 58758572250⟩, ⟨57309634750, 60216124554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241827840 242483200 187105280 188497920 ⟨⟨58072777316, 58072777322⟩, ⟨56628527511, 59525608981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 188497920 189890560 ⟨⟨58490443348, 58490443355⟩, ⟨57044476120, 59944998033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 241827840 189890560 191283200 ⟨⟨59177867370, 59177867376⟩, ⟨57727208436, 60637146677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 241827840 191283200 192675840 ⟨⟨59596989346, 59596989351⟩, ⟨58144609303, 61057995306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242483200 189890560 191283200 ⟨⟨58907938035, 58907938042⟩, ⟨57460253705, 60364215407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 241827840 242483200 191283200 192675840 ⟨⟨59325261777, 59325261783⟩, ⟨57875860665, 60783261507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 243138560 187105280 188497920 ⟨⟨57807131717, 57807131722⟩, ⟨56365834014, 59256984061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243138560 188497920 189890560 ⟨⟨58222998280, 58222998286⟩, ⟨56779987503, 59674569322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243138560 243793920 187105280 188497920 ⟨⟨57542161818, 57542161823⟩, ⟨56103802504, 58989048723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 243138560 243793920 188497920 189890560 ⟨⟨57956232073, 57956232078⟩, ⟨56516164030, 59404833360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 242483200 243138560 189890560 191283200 ⟨⟨58638695685, 58638695692⟩, ⟨57193972142, 60091985109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242483200 243138560 191283200 192675840 ⟨⟨59054224329, 59054224334⟩, ⟨57607788323, 60509231818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243793920 189890560 191283200 ⟨⟨58370135337, 58370135342⟩, ⟨56928358857, 59820450703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243138560 243793920 191283200 192675840 ⟨⟨58783871998, 58783872004⟩, ⟨57340387375, 60235901141⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 187105280 192675840 t = true :=
  ⟨_, (join_su (m := 242483200) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 188497920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 241827840) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 191283200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 189890560) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 188497920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 243138560) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 191283200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (571/2560 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
