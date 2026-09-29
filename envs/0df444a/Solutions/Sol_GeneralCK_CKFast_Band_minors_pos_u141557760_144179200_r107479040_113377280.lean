-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_144179200_r107479040_113377280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:19:13.161678+00:00
-- url     : https://prove2.me/submissions/ec8bfe95-0e62-4d44-81f6-97be1bf3d87a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 11/64]`, `ρ ∈ [41/320, 173/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142213120 107479040 108953600 ⟨⟨66830574104, 66830574111⟩, ⟨64795210842, 68883256118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 141557760 142213120 108953600 110428160 ⟨⟨67683351714, 67683351720⟩, ⟨65645069659, 69738941186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 142213120 142868480 107479040 108953600 ⟨⟨66528143924, 66528143928⟩, ⟨64499863495, 68573635033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142213120 142868480 108953600 110428160 ⟨⟨67377505866, 67377505869⟩, ⟨65346314511, 69425896905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 142213120 110428160 111902720 ⟨⟨68534756153, 68534756161⟩, ⟨66493565337, 70593242996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 141557760 142213120 111902720 113377280 ⟨⟨69384793843, 69384793851⟩, ⟨67340704230, 71446168033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 142213120 142868480 110428160 111902720 ⟨⟨68225510429, 68225510432⟩, ⟨66191418030, 70276791459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 142213120 142868480 111902720 113377280 ⟨⟨69072163926, 69072163928⟩, ⟨67035180300, 71126325072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 142868480 143523840 107479040 108953600 ⟨⟨66227495044, 66227495052⟩, ⟨64206241071, 68265852786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 142868480 143523840 108953600 110428160 ⟨⟨67073456389, 67073456398⟩, ⟨65049299372, 69114706515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 143523840 144179200 107479040 108953600 ⟨⟨65928608140, 65928608147⟩, ⟨63914324919, 67959889352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 143523840 144179200 108953600 110428160 ⟨⟨66771183841, 66771183850⟩, ⟨64754005472, 68805349872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 142868480 143523840 110428160 111902720 ⟨⟨67918075960, 67918075969⟩, ⟨65891025633, 69962208678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 142868480 143523840 111902720 113377280 ⟨⟨68761359964, 68761359972⟩, ⟨66731425999, 70808365542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 143523840 144179200 110428160 111902720 ⟨⟨67612433188, 67612433194⟩, ⟨65592369255, 69649474387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 143523840 144179200 111902720 113377280 ⟨⟨68452362280, 68452362288⟩, ⟨66429422318, 70492269063⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 144179200 107479040 113377280 t = true :=
  ⟨_, (join_su (m := 142868480) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 142213120) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 108953600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 142213120) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 111902720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 110428160) (by decide) (join_su (m := 143523840) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 108953600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 143523840) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 111902720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (11/64 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (173/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
