-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r414187520_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:06:53.983262+00:00
-- url     : https://prove2.me/submissions/1cf681a9-e3f1-4671-84e7-9e660efe0b1a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [79/160, 167/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 414187520 420085760 ⟨⟨215579310147, 215579310158⟩, ⟨205930720865, 225448472556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 149422080 420085760 425984000 ⟨⟨218173882556, 218173882565⟩, ⟨208496770138, 228070618905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 149422080 152043520 414187520 420085760 ⟨⟨212547142948, 212547142953⟩, ⟨203001358913, 222310986766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 420085760 425984000 ⟨⟨215116390034, 215116390039⟩, ⟨205541805920, 224908147975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 149422080 425984000 431882240 ⟨⟨220760256554, 220760256564⟩, ⟨211054796844, 230684386316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 149422080 431882240 437780480 ⟨⟨223338562059, 223338562070⟩, ⟨213604927383, 233289908260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 152043520 425984000 431882240 ⟨⟨217677701541, 217677701546⟩, ⟨208074487516, 227497198445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 149422080 152043520 431882240 437780480 ⟨⟨220231201801, 220231201806⟩, ⟨210599524698, 230078265875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 154664960 414187520 420085760 ⟨⟨209553271005, 209553271015⟩, ⟨200108279349, 219213853305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 152043520 154664960 420085760 425984000 ⟨⟨212097105122, 212097105132⟩, ⟨202623062390, 221785913204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 157286400 414187520 420085760 ⟨⟨206596604090, 206596604100⟩, ⟨197250452646, 216155920467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 154664960 157286400 420085760 425984000 ⟨⟨209114946099, 209114946109⟩, ⟨199739517258, 218702772772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152043520 154664960 425984000 431882240 ⟨⟨214633260411, 214633260418⟩, ⟨205130331058, 224350124555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 152043520 154664960 431882240 437780480 ⟨⟨217161855825, 217161855835⟩, ⟨207630201154, 226906609511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 157286400 425984000 431882240 ⟨⟨211625860000, 211625860010⟩, ⟨202221312492, 221242032751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 154664960 157286400 431882240 437780480 ⟨⟨214129459586, 214129459594⟩, ⟨204695949148, 223773817224⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 414187520 437780480 t = true :=
  ⟨_, (join_su (m := 152043520) (by decide) (join_sr (m := 425984000) (by decide) (join_su (m := 149422080) (by decide) (join_sr (m := 420085760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 420085760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 149422080) (by decide) (join_sr (m := 431882240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 431882240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 425984000) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 420085760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 420085760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 154664960) (by decide) (join_sr (m := 431882240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 431882240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (79/160 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
