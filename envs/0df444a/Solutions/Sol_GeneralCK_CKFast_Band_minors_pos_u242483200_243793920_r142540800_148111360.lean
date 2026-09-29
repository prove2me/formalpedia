-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u242483200_243793920_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:34:15.92161+00:00
-- url     : https://prove2.me/submissions/1e8b99e2-5eb1-4549-b818-2cc9a03664e9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/128, 93/320]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 242483200 242810880 142540800 143933440 ⟨⟨44459349969, 44459349976⟩, ⟨43646362313, 45275323890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242810880 243138560 142540800 143933440 ⟨⟨44356056806, 44356056811⟩, ⟨43544071576, 45171022352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 242810880 143933440 145326080 ⟨⟨44881310357, 44881310362⟩, ⟨44067388765, 45698219625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242810880 243138560 143933440 145326080 ⟨⟨44777081694, 44777081701⟩, ⟨43964163985, 45592981142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243138560 243466240 142540800 143933440 ⟨⟨44252903908, 44252903912⟩, ⟨43441918889, 45066863316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243466240 243793920 142540800 143933440 ⟨⟨44149890748, 44149890753⟩, ⟨43339903724, 44962846255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243138560 243466240 143933440 145326080 ⟨⟨44672994281, 44672994285⟩, ⟨43861078231, 45487886145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243466240 243793920 143933440 145326080 ⟨⟨44569047582, 44569047588⟩, ⟨43758130976, 45382934100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 242810880 145326080 146718720 ⟨⟨45303087951, 45303087956⟩, ⟨44488232724, 46120932267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242810880 243138560 145326080 146718720 ⟨⟨45197924987, 45197924992⟩, ⟨44384075088, 46014758040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 242483200 242810880 146718720 148111360 ⟨⟨45724683176, 45724683182⟩, ⟨44908894609, 46543462239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242810880 243138560 146718720 148111360 ⟨⟨45618587100, 45618587105⟩, ⟨44803805304, 46436353461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243138560 243466240 145326080 146718720 ⟨⟨45092904246, 45092904247⟩, ⟨44280057451, 45908728273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243466240 243793920 145326080 146718720 ⟨⟨44988025189, 44988025194⟩, ⟨44176179284, 45802842431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243466240 146718720 148111360 ⟨⟨45512634213, 45512634217⟩, ⟨44698856964, 46329390115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243466240 243793920 146718720 148111360 ⟨⟨45406823977, 45406823982⟩, ⟨44594049057, 46222571660⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 242483200 243793920 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242810880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243466240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243138560) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 242810880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 243466240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/128 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
