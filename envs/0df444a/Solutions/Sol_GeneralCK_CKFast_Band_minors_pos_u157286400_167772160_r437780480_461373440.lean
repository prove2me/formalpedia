-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r437780480_461373440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:08:41.448838+00:00
-- url     : https://prove2.me/submissions/9f18bc04-715e-4ecc-8880-2d00595c57c4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [167/320, 11/20]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 437780480 443678720 ⟨⟨213604540513, 213604540523⟩, ⟨204238321130, 223178662772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 159907840 443678720 449576960 ⟨⟨216069232867, 216069232876⟩, ⟨206674128489, 225671506343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 162529280 437780480 443678720 ⟨⟨210618076862, 210618076870⟩, ⟨201346210042, 220095718731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 443678720 449576960 ⟨⟨213058069449, 213058069458⟩, ⟨203757115169, 222564117935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 159907840 449576960 455475200 ⟨⟨218527168335, 218527168344⟩, ⟨209103320966, 228157445476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 159907840 455475200 461373440 ⟨⟨220978449947, 220978449957⟩, ⟨211525998964, 230636585858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 162529280 449576960 455475200 ⟨⟨215491525495, 215491525505⟩, ⟨206161620642, 225025838005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159907840 162529280 455475200 461373440 ⟨⟨217918543629, 217918543639⟩, ⟨208559822602, 227480980080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 165150720 437780480 443678720 ⟨⟨207665518167, 207665518170⟩, ⟨198486304781, 217048411412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 162529280 165150720 443678720 449576960 ⟨⟨210080732100, 210080732105⟩, ⟨200872250104, 219492264001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 167772160 437780480 443678720 ⟨⟨204745949074, 204745949082⟩, ⟨195657737600, 214035777447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 165150720 167772160 443678720 449576960 ⟨⟨207136312298, 207136312307⟩, ⟨198018671398, 216454989060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 162529280 165150720 449576960 455475200 ⟨⟨212489624723, 212489624728⟩, ⟨203252005886, 221929657669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 162529280 165150720 455475200 461373440 ⟨⟨214892290430, 214892290435⟩, ⟨205625664170, 224360689191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 167772160 449576960 455475200 ⟨⟨209520564376, 209520564386⟩, ⟨200373620718, 218867956921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 165150720 167772160 455475200 461373440 ⟨⟨211898795629, 211898795638⟩, ⟨202722673656, 221274773594⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 437780480 461373440 t = true :=
  ⟨_, (join_su (m := 162529280) (by decide) (join_sr (m := 449576960) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 443678720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 443678720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 159907840) (by decide) (join_sr (m := 455475200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 455475200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 449576960) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 443678720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 443678720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 165150720) (by decide) (join_sr (m := 455475200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 455475200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (11/20 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
