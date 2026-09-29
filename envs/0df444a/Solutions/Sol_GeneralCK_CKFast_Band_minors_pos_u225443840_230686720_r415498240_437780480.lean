-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r415498240_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:29:03.674921+00:00
-- url     : https://prove2.me/submissions/37461fc3-be48-49d0-afd7-170581fe18c1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [317/640, 167/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 415498240 421068800 ⟨⟨138632682178, 138632682182⟩, ⟨134427074434, 142893325301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226754560 228065280 415498240 421068800 ⟨⟨137507482417, 137507482424⟩, ⟨133322864335, 141746821193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226754560 421068800 426639360 ⟨⟨140357520874, 140357520878⟩, ⟨136137186231, 144632903217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 421068800 426639360 ⟨⟨139220164018, 139220164025⟩, ⟨135020855634, 143474208656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228065280 229376000 415498240 421068800 ⟨⟨136386692370, 136386692378⟩, ⟨132222914056, 140604879171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 229376000 230686720 415498240 421068800 ⟨⟨135270257044, 135270257050⟩, ⟨131127170357, 139467442464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228065280 229376000 421068800 426639360 ⟨⟨138087222734, 138087222741⟩, ⟨133908791654, 142320081028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229376000 230686720 421068800 426639360 ⟨⟨136958642153, 136958642161⟩, ⟨132800941149, 141170463712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226754560 426639360 432209920 ⟨⟨142079971145, 142079971148⟩, ⟨137844929694, 146370071469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226754560 228065280 426639360 432209920 ⟨⟨140930508990, 140930508998⟩, ⟨136716529504, 145199239164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226754560 432209920 437780480 ⟨⟨143800059579, 143800059581⟩, ⟨139550331139, 148104856921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226754560 228065280 432209920 437780480 ⟨⟨142638543238, 142638543244⟩, ⟨138409911583, 146921938885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 426639360 432209920 ⟨⟨139785467444, 139785467452⟩, ⟨135592401918, 144032977802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229376000 230686720 426639360 432209920 ⟨⟨138644791771, 138644791779⟩, ⟨134472493905, 142871230923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 229376000 432209920 437780480 ⟨⟨141481451732, 141481451740⟩, ⟨137273769826, 145743594979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 432209920 437780480 ⟨⟨140328730470, 140328730478⟩, ⟨136141852957, 144569768910⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 415498240 437780480 t = true :=
  ⟨_, (join_sr (m := 426639360) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 421068800) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226754560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 421068800) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 229376000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 228065280) (by decide) (join_sr (m := 432209920) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226754560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 432209920) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 229376000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (317/640 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
