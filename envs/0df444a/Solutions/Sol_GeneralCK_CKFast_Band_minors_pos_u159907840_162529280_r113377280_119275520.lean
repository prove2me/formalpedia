-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_162529280_r113377280_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:29:45.65416+00:00
-- url     : https://prove2.me/submissions/ffc0e4fb-8caa-488c-bc43-a72ae1e2dedb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 31/160]`, `ρ ∈ [173/1280, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 159907840 160563200 113377280 114851840 ⟨⟨62021667516, 62021667522⟩, ⟨60154589820, 63903409715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 160563200 114851840 116326400 ⟨⟨62780175775, 62780175783⟩, ⟨60910427372, 64664584641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 160563200 161218560 113377280 114851840 ⟨⟨61750548348, 61750548356⟩, ⟨59889231247, 63626449583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160563200 161218560 114851840 116326400 ⟨⟨62506065784, 62506065792⟩, ⟨60642085462, 64384626402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159907840 160563200 116326400 117800960 ⟨⟨63537705726, 63537705732⟩, ⟨61665293034, 65424774793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 159907840 160563200 117800960 119275520 ⟨⟨64294261328, 64294261336⟩, ⟨62419190732, 66183984165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 160563200 161218560 116326400 117800960 ⟨⟨63260616034, 63260616042⟩, ⟨61393978812, 65141829671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 160563200 161218560 117800960 119275520 ⟨⟨64014202999, 64014203006⟩, ⟨62144915162, 65898063317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 161218560 161873920 113377280 114851840 ⟨⟨61480807257, 61480807263⟩, ⟨59625209881, 63350909161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 161218560 161873920 114851840 116326400 ⟨⟨62233345429, 62233345436⟩, ⟨60375092316, 64106099436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161873920 162529280 113377280 114851840 ⟨⟨61212430726, 61212430729⟩, ⟨59362512650, 63076774482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161873920 162529280 114851840 116326400 ⟨⟨61962001106, 61962001110⟩, ⟨60109434769, 63828989685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 161873920 116326400 117800960 ⟨⟨62984927413, 62984927421⟩, ⟨61124024785, 64860327254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161218560 161873920 117800960 119275520 ⟨⟨63735557048, 63735557054⟩, ⟨61872011095, 65613596483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161873920 162529280 116326400 117800960 ⟨⟨62710626174, 62710626177⟩, ⟨60855417704, 64580253403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161873920 162529280 117800960 119275520 ⟨⟨63458309705, 63458309709⟩, ⟨61600465198, 65330569440⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 162529280 113377280 119275520 t = true :=
  ⟨_, (join_su (m := 161218560) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 160563200) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114851840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 160563200) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 117800960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 116326400) (by decide) (join_su (m := 161873920) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114851840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 161873920) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 117800960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (173/1280 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
