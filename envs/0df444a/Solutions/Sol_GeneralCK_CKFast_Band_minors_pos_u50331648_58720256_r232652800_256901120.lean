-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_58720256_r232652800_256901120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:15:30.89476+00:00
-- url     : https://prove2.me/submissions/5e1895cf-9848-44cb-b83f-4a67e373436b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 7/100]`, `ρ ∈ [71/256, 49/160]` by 14 cells of the computing
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
theorem cell0 : cellOK 50331648 52428800 232652800 238714880 ⟨⟨254805688482, 254805688498⟩, ⟨240428688535, 269659530398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 52428800 238714880 244776960 ⟨⟨259268421325, 259268421341⟩, ⟨244914373061, 274089066945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 52428800 54525952 232652800 238714880 ⟨⟨250379506619, 250379506634⟩, ⟨236292800432, 264929877887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 52428800 54525952 238714880 244776960 ⟨⟨254818245655, 254818245668⟩, ⟨240750212068, 269340321686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 52428800 244776960 256901120 ⟨⟨265860343764, 265860343777⟩, ⟨246694772086, 285825698078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 52428800 54525952 244776960 256901120 ⟨⟨261376735131, 261376735144⟩, ⟨242597079806, 280934602290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 54525952 56623104 232652800 238714880 ⟨⟨246090016696, 246090016712⟩, ⟨232281813553, 260349254527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 54525952 56623104 238714880 244776960 ⟨⟨250503473177, 250503473192⟩, ⟨236709995330, 264738942239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 56623104 58720256 232652800 238714880 ⟨⟨241929958757, 241929958772⟩, ⟨228389193735, 255909647584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 56623104 58720256 238714880 244776960 ⟨⟨246316988009, 246316988025⟩, ⟨232787304886, 260277091273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 54525952 56623104 244776960 250839040 ⟨⟨254864866250, 254864866263⟩, ⟨241086654692, 269076235652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 54525952 56623104 250839040 256901120 ⟨⟨259175902647, 259175902662⟩, ⟨245413445892, 273362887303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 56623104 58720256 244776960 250839040 ⟨⟨250653304557, 250653304573⟩, ⟨237135290214, 264593424636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 56623104 58720256 250839040 256901120 ⟨⟨254940540582, 254940540598⟩, ⟨241434730258, 268860325752⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 58720256 232652800 256901120 t = true :=
  ⟨_, (join_su (m := 54525952) (by decide) (join_sr (m := 244776960) (by decide) (join_su (m := 52428800) (by decide) (join_sr (m := 238714880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 238714880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 52428800) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 244776960) (by decide) (join_su (m := 56623104) (by decide) (join_sr (m := 238714880) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 238714880) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 56623104) (by decide) (join_sr (m := 250839040) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 250839040) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (71/256 : ℝ) (49/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  have e3 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
