-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_193986560_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:25:35.038805+00:00
-- url     : https://prove2.me/submissions/48445ba5-1a33-4337-b6e5-4d0263553974

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 37/160]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 190054400 248381440 251166720 ⟨⟨107367435297, 107367435304⟩, ⟨103723361685, 111057542641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 190054400 251166720 253952000 ⟨⟨108479502984, 108479502992⟩, ⟨104827520340, 112177518491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 190054400 191365120 248381440 251166720 ⟨⟨106507793613, 106507793621⟩, ⟨102882124172, 110179157110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 190054400 191365120 251166720 253952000 ⟨⟨107612183428, 107612183434⟩, ⟨103978627487, 111291434255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 190054400 253952000 256737280 ⟨⟨109590028940, 109590028946⟩, ⟨105930152540, 113295936961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 190054400 256737280 259522560 ⟨⟨110699022593, 110699022601⟩, ⟨107031267605, 114412807589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 190054400 191365120 253952000 256737280 ⟨⟨108715063666, 108715063672⟩, ⟨105073636028, 112402186657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 190054400 191365120 256737280 259522560 ⟨⟨109816443499, 109816443507⟩, ⟨106167158868, 113511423583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 191365120 192675840 248381440 251166720 ⟨⟨105653802867, 105653802875⟩, ⟨102046341067, 109306623607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 191365120 192675840 251166720 253952000 ⟨⟨106750539111, 106750539119⟩, ⟨103135213745, 110411225906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 192675840 193986560 248381440 251166720 ⟨⟨104805378010, 104805378014⟩, ⟨101215930479, 108439853836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 192675840 193986560 251166720 253952000 ⟨⟨105894484846, 105894484851⟩, ⟨102297197070, 109536805019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 191365120 192675840 253952000 256737280 ⟨⟨107845797367, 107845797375⟩, ⟨104222622776, 111514335513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 191365120 192675840 256737280 259522560 ⟨⟨108939586556, 108939586564⟩, ⟨105308576982, 112615961448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 192675840 193986560 253952000 256737280 ⟨⟨106982144726, 106982144731⟩, ⟨103377030593, 110632295002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 192675840 193986560 256737280 259522560 ⟨⟨108068366325, 108068366328⟩, ⟨104455439626, 111726332551⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 193986560 248381440 259522560 t = true :=
  ⟨_, (join_su (m := 191365120) (by decide) (join_sr (m := 253952000) (by decide) (join_su (m := 190054400) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 251166720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 190054400) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 256737280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 253952000) (by decide) (join_su (m := 192675840) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 251166720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 192675840) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 256737280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
