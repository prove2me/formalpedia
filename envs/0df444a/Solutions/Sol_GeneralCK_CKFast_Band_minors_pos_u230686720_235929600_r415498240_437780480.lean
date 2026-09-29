-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r415498240_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:08:22.381829+00:00
-- url     : https://prove2.me/submissions/528d4c2b-8ff0-4023-8c05-cedc41761398

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [317/640, 167/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 415498240 421068800 ⟨⟨134158122152, 134158122160⟩, ⟨130035580676, 138334455039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231997440 233308160 415498240 421068800 ⟨⟨133050234103, 133050234106⟩, ⟨128948093114, 137205861580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231997440 421068800 426639360 ⟨⟨135834368109, 135834368117⟩, ⟨131697251657, 140025300819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 421068800 426639360 ⟨⟨134714347123, 134714347127⟩, ⟨130597671366, 138884537169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233308160 234618880 415498240 421068800 ⟨⟨131946539974, 131946539982⟩, ⟨127864656433, 136081607466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234618880 235929600 415498240 421068800 ⟨⟨130846987520, 130846987527⟩, ⟨126785220026, 134961638782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 234618880 421068800 426639360 ⟨⟨133598526378, 133598526386⟩, ⟨129502149126, 137748118275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234618880 235929600 421068800 426639360 ⟨⟨132486853734, 132486853742⟩, ⟨128410634409, 136615990341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231997440 426639360 432209920 ⟨⟨137508427931, 137508427938⟩, ⟨133356753108, 141713942786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 233308160 426639360 432209920 ⟨⟨136376322566, 136376322570⟩, ⟨132245127815, 140561058359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231997440 432209920 437780480 ⟨⟨139180325548, 139180325554⟩, ⟨135014108728, 143400405101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231997440 233308160 432209920 437780480 ⟨⟨138036183737, 138036183739⟩, ⟨133890485538, 142235448670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 426639360 432209920 ⟨⟨135248422979, 135248422987⟩, ⟨131137566967, 139412523291⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234618880 235929600 426639360 432209920 ⟨⟨134124677135, 134124677143⟩, ⟨130034020127, 138268283927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233308160 234618880 432209920 437780480 ⟨⟨136896252463, 136896252469⟩, ⟨132770932430, 141074845418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 432209920 437780480 ⟨⟨135760479812, 135760479820⟩, ⟨131655399063, 139918541828⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 415498240 437780480 t = true :=
  ⟨_, (join_sr (m := 426639360) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 421068800) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231997440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 421068800) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234618880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233308160) (by decide) (join_sr (m := 432209920) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231997440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 432209920) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 234618880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (317/640 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
