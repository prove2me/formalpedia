-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r526909440_549191680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:00:56.004349+00:00
-- url     : https://prove2.me/submissions/c60abddd-0bd8-4a9c-98d4-f9ea25cc2dd0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [201/320, 419/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 526909440 532480000 ⟨⟨200165581136, 200165581145⟩, ⟨191766561559, 208736320713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 201850880 532480000 538050560 ⟨⟨202064737863, 202064737873⟩, ⟨193638281612, 210662758734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 204472320 526909440 532480000 ⟨⟨197259228790, 197259228794⟩, ⟨188930959600, 205758045060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 532480000 538050560 ⟨⟨199136316665, 199136316670⟩, ⟨190780599968, 207662452350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 201850880 538050560 543621120 ⟨⟨203961119360, 203961119369⟩, ⟨195507271583, 212586371409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 201850880 543621120 549191680 ⟨⟨205854762257, 205854762266⟩, ⟨197373567400, 214507196065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 204472320 538050560 543621120 ⟨⟨201010730933, 201010730937⟩, ⟨192627608994, 209564138880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201850880 204472320 543621120 549191680 ⟨⟨202882506621, 202882506625⟩, ⟨194472021049, 211463140329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 207093760 526909440 532480000 ⟨⟨194374685694, 194374685702⟩, ⟨186116237555, 202802517142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 204472320 207093760 532480000 538050560 ⟨⟨196229648806, 196229648815⟩, ⟨187943752916, 204684826289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 209715200 526909440 532480000 ⟨⟨191511442173, 191511442182⟩, ⟨183321905990, 199869207119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207093760 209715200 532480000 538050560 ⟨⟨193344227735, 193344227744⟩, ⟨185127253762, 201729354244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 538050560 543621120 ⟨⟨198082037389, 198082037398⟩, ⟨189768733179, 206564516678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 204472320 207093760 543621120 549191680 ⟨⟨199931884924, 199931884933⟩, ⟨191591211209, 208441622395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 209715200 538050560 543621120 ⟨⟨195174535329, 195174535336⟩, ⟨186930160214, 203586982049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 209715200 543621120 549191680 ⟨⟨197002396944, 197002396953⟩, ⟨188730656759, 205442123090⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 526909440 549191680 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 538050560) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 532480000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 532480000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 201850880) (by decide) (join_sr (m := 543621120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 543621120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 538050560) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 532480000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 532480000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 207093760) (by decide) (join_sr (m := 543621120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 543621120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (201/320 : ℝ) (419/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  have e3 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
