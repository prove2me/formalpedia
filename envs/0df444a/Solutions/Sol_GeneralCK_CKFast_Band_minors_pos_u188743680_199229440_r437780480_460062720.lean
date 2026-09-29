-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r437780480_460062720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:51:46.320411+00:00
-- url     : https://prove2.me/submissions/81eb05e0-2125-44f7-ad5f-f8beb6415cde

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [167/320, 351/640]` by 17 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 437780480 443351040 ⟨⟨179757438283, 179757438289⟩, ⟨171510696450, 188184358886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 191365120 443351040 448921600 ⟨⟨181801838260, 181801838266⟩, ⟨173526774260, 190256890371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 193986560 437780480 443351040 ⟨⟨177124302062, 177124302071⟩, ⟨168952700915, 185474381775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 443351040 448921600 ⟨⟨179144824399, 179144824406⟩, ⟨170944900160, 187523066820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 191365120 448921600 454492160 ⟨⟨183842275146, 183842275152⟩, ⟨175538961716, 192325380778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 191365120 454492160 460062720 ⟨⟨185878799572, 185878799578⟩, ⟨177547308389, 194389881803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 193986560 448921600 454492160 ⟨⟨181161529081, 181161529090⟩, ⟨172933350494, 189567860289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 191365120 193986560 454492160 460062720 ⟨⟨183174464428, 183174464437⟩, ⟨174918099242, 191608811496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 196608000 437780480 443351040 ⟨⟨174515855491, 174515855500⟩, ⟨166418188694, 182790326938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 193986560 196608000 443351040 448921600 ⟨⟨176512482602, 176512482611⟩, ⟨168386503179, 184815135400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 197918720 437780480 443351040 ⟨⟨172575348028, 172575348037⟩, ⟨167805436033, 177407569356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197918720 199229440 437780480 443351040 ⟨⟨171289070610, 171289070619⟩, ⟨166543976605, 176096118846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 199229440 443351040 448921600 ⟨⟨173904193538, 173904193547⟩, ⟨165850993906, 182132446456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193986560 196608000 448921600 454492160 ⟨⟨178505433597, 178505433605⟩, ⟨170351206373, 186836197820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 193986560 196608000 454492160 460062720 ⟨⟨180494754572, 180494754579⟩, ⟨172312343442, 188853561220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 448921600 454492160 ⟨⟨175873372516, 175873372523⟩, ⟨167791942597, 184129747410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 196608000 199229440 454492160 460062720 ⟨⟨177839057039, 177839057048⟩, ⟨169729456957, 186123488773⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 437780480 460062720 t = true :=
  ⟨_, (join_su (m := 193986560) (by decide) (join_sr (m := 448921600) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 443351040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 443351040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 191365120) (by decide) (join_sr (m := 454492160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 454492160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 448921600) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 443351040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 443351040) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 196608000) (by decide) (join_sr (m := 454492160) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 454492160) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (351/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
