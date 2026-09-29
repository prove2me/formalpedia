-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r326369280_337510400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:10:34.695002+00:00
-- url     : https://prove2.me/submissions/519b6052-badf-4a73-b39a-fa9834ac9212

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [249/640, 103/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 326369280 329154560 ⟨⟨110245811766, 110245811769⟩, ⟨106853004641, 113677467351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 225443840 226754560 329154560 331939840 ⟨⟨111129944418, 111129944420⟩, ⟨107730099714, 114568664182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226754560 228065280 326369280 329154560 ⟨⟨109326042257, 109326042263⟩, ⟨105947866747, 112742852479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 329154560 331939840 ⟨⟨110203615933, 110203615939⟩, ⟨106818425202, 113627468902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 225443840 226754560 331939840 334725120 ⟨⟨112013360973, 112013360976⟩, ⟨108606482992, 115459140385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225443840 226754560 334725120 337510400 ⟨⟨112896065209, 112896065212⟩, ⟨109482158231, 116348899764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 228065280 331939840 334725120 ⟨⟨111080489637, 111080489645⟩, ⟨107688287766, 114511381052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 226754560 228065280 334725120 337510400 ⟨⟨111956667049, 111956667056⟩, ⟨108557458088, 115394592632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 229376000 326369280 329154560 ⟨⟨108410458004, 108410458010⟩, ⟨105046790791, 111812548391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228065280 229376000 329154560 331939840 ⟨⟨109281483628, 109281483636⟩, ⟨105910823810, 112690595053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 230686720 326369280 329154560 ⟨⟨107499003508, 107499003516⟩, ⟨104149722886, 110886497951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229376000 230686720 329154560 331939840 ⟨⟨108363491975, 108363491982⟩, ⟨105007241610, 111757985471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 331939840 334725120 ⟨⟨110151825133, 110151825139⟩, ⟨106774176566, 113567953515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 228065280 229376000 334725120 337510400 ⟨⟨111021486087, 111021486095⟩, ⟨107636852608, 114444627376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230686720 331939840 334725120 ⟨⟨109227311891, 109227311899⟩, ⟨105864095426, 112628800585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 334725120 337510400 ⟨⟨110090466732, 110090466740⟩, ⟨106720287787, 113498946790⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 326369280 337510400 t = true :=
  ⟨_, (join_su (m := 228065280) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 329154560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 226754560) (by decide) (join_sr (m := 334725120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 334725120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 331939840) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 329154560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 229376000) (by decide) (join_sr (m := 334725120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 334725120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (103/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
