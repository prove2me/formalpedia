-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_207093760_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:51:29.141163+00:00
-- url     : https://prove2.me/submissions/2c1cab0a-f20e-445a-9273-65541eff9c39

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 79/320]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205127680 142540800 143933440 ⟨⟨57491787198, 57491787201⟩, ⟨55916784621, 59077151506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 204472320 205127680 143933440 145326080 ⟨⟨58029305797, 58029305800⟩, ⟨56452283982, 59616692942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 205127680 205783040 142540800 143933440 ⟨⟨57244560565, 57244560571⟩, ⟨55673329622, 58826111391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205127680 205783040 143933440 145326080 ⟨⟨57779935094, 57779935100⟩, ⟨56206690287, 59363503447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 205127680 145326080 146718720 ⟨⟨58566451429, 58566451431⟩, ⟨56987412016, 60155859753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 204472320 205127680 146718720 148111360 ⟨⟨59103225150, 59103225153⟩, ⟨57522169773, 60694652996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205127680 205783040 145326080 146718720 ⟨⟨58314941013, 58314941019⟩, ⟨56739683948, 59900525262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 205127680 205783040 146718720 148111360 ⟨⟨58849579362, 58849579368⟩, ⟨57272311644, 60437177886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 205783040 206438400 142540800 143933440 ⟨⟨56998209240, 56998209245⟩, ⟨55430728879, 58575967944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205783040 206438400 143933440 145326080 ⟨⟨57531445355, 57531445362⟩, ⟨55961956495, 59111216282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 206438400 207093760 142540800 143933440 ⟨⟨56752726169, 56752726175⟩, ⟨55188975518, 58326713934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 206438400 207093760 143933440 145326080 ⟨⟨57283829493, 57283829500⟩, ⟨55718075701, 58859824182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 205783040 206438400 145326080 146718720 ⟨⟨58064317174, 58064317179⟩, ⟨56492821391, 59646098724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 205783040 206438400 146718720 148111360 ⟨⟨58596825718, 58596825724⟩, ⟨57023324584, 60180616302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 206438400 207093760 145326080 146718720 ⟨⟨57814572787, 57814572793⟩, ⟨56246817398, 59392572835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 206438400 207093760 146718720 148111360 ⟨⟨58344957059, 58344957065⟩, ⟨56775201614, 59924960906⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 207093760 142540800 148111360 t = true :=
  ⟨_, (join_su (m := 205783040) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 205127680) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 143933440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 205127680) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 146718720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 145326080) (by decide) (join_su (m := 206438400) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 143933440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 206438400) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 146718720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (79/320 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
