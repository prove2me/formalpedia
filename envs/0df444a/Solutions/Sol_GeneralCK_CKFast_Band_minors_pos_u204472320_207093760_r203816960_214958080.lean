-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_207093760_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:18:51.138627+00:00
-- url     : https://prove2.me/submissions/2242ea71-c0c3-4060-a258-19d30bd784ca

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 79/320]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205127680 203816960 206602240 ⟨⟨81064435379, 81064435381⟩, ⟨79078900395, 83065325735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 205127680 205783040 203816960 206602240 ⟨⟨80725800231, 80725800237⟩, ⟨78745800441, 82721089661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 204472320 205127680 206602240 209387520 ⟨⟨82107912557, 82107912560⟩, ⟨80118117797, 84113063289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205127680 205783040 206602240 209387520 ⟨⟨81765350919, 81765350925⟩, ⟨79781101058, 83764891263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 205783040 206438400 203816960 206602240 ⟨⟨80388251902, 80388251908⟩, ⟨78413759498, 82377968656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 206438400 207093760 203816960 206602240 ⟨⟨80051782127, 80051782133⟩, ⟨78082769529, 82035954231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205783040 206438400 206602240 209387520 ⟨⟨81423883824, 81423883830⟩, ⟨79445151079, 83417842006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 206438400 207093760 206602240 209387520 ⟨⟨81083502974, 81083502980⟩, ⟨79110259784, 83071906995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 205127680 209387520 212172800 ⟨⟨83150078195, 83150078198⟩, ⟨81156031437, 85159481421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205127680 205783040 209387520 212172800 ⟨⟨82803604779, 82803604786⟩, ⟨80815112496, 84807388292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 204472320 205127680 212172800 214958080 ⟨⟨84190939691, 84190939695⟩, ⟨82192648669, 86204587583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 205127680 205783040 212172800 214958080 ⟨⟨83840569105, 83840569111⟩, ⟨81847841996, 85848588093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 205783040 206438400 209387520 212172800 ⟨⟨82458233493, 82458233501⟩, ⟨80475267922, 84456425493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 206438400 207093760 209387520 212172800 ⟨⟨82113956001, 82113956009⟩, ⟨80136489604, 84106584461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 205783040 206438400 212172800 214958080 ⟨⟨83491308095, 83491308103⟩, ⟨81504117163, 85493726350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 206438400 207093760 212172800 214958080 ⟨⟨83143148293, 83143148299⟩, ⟨81161466020, 85139993762⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 207093760 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 205783040) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 205127680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 205127680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 206438400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 206438400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 205783040) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 205127680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 205127680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 206438400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 206438400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (79/320 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
