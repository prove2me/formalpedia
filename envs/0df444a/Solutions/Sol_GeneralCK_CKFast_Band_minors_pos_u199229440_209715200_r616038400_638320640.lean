-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r616038400_638320640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:02:45.592456+00:00
-- url     : https://prove2.me/submissions/cfba4df3-c82b-4007-beed-9fb359e9c562

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [47/64, 487/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 616038400 621608960 ⟨⟨230239069328, 230239069337⟩, ⟨221406097394, 239240674709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 201850880 621608960 627179520 ⟨⟨232098064629, 232098064639⟩, ⟨223238297114, 241126229718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 204472320 616038400 621608960 ⟨⟨226990945015, 226990945019⟩, ⟨218228227344, 235921569200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 621608960 627179520 ⟨⟨228829315022, 228829315028⟩, ⟨220039749663, 237786579538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 201850880 627179520 632750080 ⟨⟨233954838610, 233954838618⟩, ⟨225068310047, 243009523746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 201850880 632750080 638320640 ⟨⟨235809423792, 235809423801⟩, ⟨226896168094, 244890589928⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 204472320 627179520 632750080 ⟨⟨230665541781, 230665541783⟩, ⟨221849161001, 239649409302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201850880 204472320 632750080 638320640 ⟨⟨232499656471, 232499656476⟩, ⟨223656491957, 241510090253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 207093760 616038400 621608960 ⟨⟨223763460404, 223763460413⟩, ⟨215070241815, 232623853894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 204472320 207093760 621608960 627179520 ⟨⟨225581114838, 225581114847⟩, ⟨216861007599, 234468217323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 209715200 616038400 621608960 ⟨⟨220556158286, 220556158296⟩, ⟨211931698075, 229347057541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207093760 209715200 621608960 627179520 ⟨⟨222353010261, 222353010271⟩, ⟨213701631249, 231170675569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 627179520 632750080 ⟨⟨227396702349, 227396702356⟩, ⟨218649736488, 236310478825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 204472320 207093760 632750080 638320640 ⟨⟨229210252826, 229210252835⟩, ⟨220436457821, 238150668833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 209715200 627179520 632750080 ⟨⟨224147869904, 224147869912⟩, ⟨215469599907, 232992268562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 209715200 632750080 638320640 ⟨⟨225940765853, 225940765862⟩, ⟨217235632164, 234811865670⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 616038400 638320640 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 627179520) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 621608960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 621608960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 201850880) (by decide) (join_sr (m := 632750080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 632750080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 627179520) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 621608960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 621608960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 207093760) (by decide) (join_sr (m := 632750080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 632750080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (47/64 : ℝ) (487/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  have e3 : (((638320640 : ℤ) : ℝ) / (D : ℝ)) = (487/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
