-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u234618880_235929600_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:22:05.935354+00:00
-- url     : https://prove2.me/submissions/3e7d6226-b708-473f-928f-dd65556ae04b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [179/640, 9/32]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 234618880 234946560 125829120 127221760 ⟨⟨41628459789, 41628459794⟩, ⟨40802390619, 42457648373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 234946560 235274240 125829120 127221760 ⟨⟨41533263663, 41533263667⟩, ⟨40708234420, 42361405810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 234618880 234946560 127221760 128614400 ⟨⟨42075776374, 42075776381⟩, ⟨41248732746, 42905940735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 234946560 235274240 127221760 128614400 ⟨⟨41979603643, 41979603647⟩, ⟨41153601502, 42808720010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235274240 235601920 125829120 127221760 ⟨⟨41438207853, 41438207858⟩, ⟨40614216128, 42265305994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235601920 235929600 125829120 127221760 ⟨⟨41343291822, 41343291827⟩, ⟨40520335220, 42169348373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 235274240 235601920 127221760 128614400 ⟨⟨41883572374, 41883572380⟩, ⟨41058609312, 42711643182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235601920 235929600 127221760 128614400 ⟨⟨41787682027, 41787682033⟩, ⟨40963755646, 42614709693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 234618880 234946560 128614400 130007040 ⟨⟨42522873278, 42522873283⟩, ⟨41694855627, 43354012974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 234946560 235274240 128614400 130007040 ⟨⟨42425725347, 42425725351⟩, ⟨41598750739, 43255815500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 234946560 130007040 131399680 ⟨⟨42969751025, 42969751030⟩, ⟨42140759785, 43801865618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234946560 235274240 130007040 131399680 ⟨⟨42871629298, 42871629302⟩, ⟨42043682652, 43702692804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 235274240 235601920 128614400 130007040 ⟨⟨42328720019, 42328720024⟩, ⟨41502786043, 43157763064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235601920 235929600 128614400 130007040 ⟨⟨42231856748, 42231856754⟩, ⟨41406961006, 43059855107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 235274240 235601920 130007040 131399680 ⟨⟨42773651305, 42773651310⟩, ⟨41946746840, 43603666162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235601920 235929600 130007040 131399680 ⟨⟨42675816499, 42675816504⟩, ⟨41849951811, 43504785128⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 234618880 235929600 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 235274240) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 234946560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235601920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 235274240) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 234946560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235601920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (179/640 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
