-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:53:17.10727+00:00
-- url     : https://prove2.me/submissions/01f29353-9c3a-4cd3-9436-e040149d8d0d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 270663680 273448960 ⟨⟨92406822075, 92406822078⟩, ⟨89155711212, 95696201925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 225443840 226754560 273448960 276234240 ⟨⟨93306094205, 93306094207⟩, ⟨90047854087, 96602634421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226754560 228065280 270663680 273448960 ⟨⟨91621784412, 91621784419⟩, ⟨88384808738, 94896797804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 273448960 276234240 ⟨⟨92514152220, 92514152226⟩, ⟨89270074426, 95796299670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 225443840 226754560 276234240 279019520 ⟨⟨94204571350, 94204571353⟩, ⟨90939206819, 97508266867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225443840 226754560 279019520 281804800 ⟨⟨95102257614, 95102257617⟩, ⟨91829773484, 98413103392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 228065280 276234240 279019520 ⟨⟨93405743383, 93405743390⟩, ⟨90154568061, 96695020085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 226754560 228065280 279019520 281804800 ⟨⟨94296561890, 94296561897⟩, ⟨91038293602, 97592963059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 229376000 270663680 273448960 ⟨⟨90840650741, 90840650748⟩, ⟨87617682816, 94101427766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228065280 229376000 273448960 276234240 ⟨⟨91726131303, 91726131309⟩, ⟨88496088552, 94994015902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 230686720 270663680 273448960 ⟨⟨90063367161, 90063367166⟩, ⟨86854281304, 93310036117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229376000 230686720 273448960 276234240 ⟨⟨90941977432, 90941977437⟩, ⟨87725844194, 94195727305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 276234240 279019520 ⟨⟨92610853229, 92610853236⟩, ⟨89373739997, 95885840845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 228065280 229376000 279019520 281804800 ⟨⟨93494820389, 93494820395⟩, ⟨90250640993, 96776906489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230686720 276234240 279019520 ⟨⟨91819846743, 91819846749⟩, ⟨88596670226, 95080673223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 279019520 281804800 ⟨⟨92696978855, 92696978862⟩, ⟨89466763136, 95964877651⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 270663680 281804800 t = true :=
  ⟨_, (join_su (m := 228065280) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 273448960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 226754560) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 279019520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 276234240) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 273448960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 229376000) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 279019520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
