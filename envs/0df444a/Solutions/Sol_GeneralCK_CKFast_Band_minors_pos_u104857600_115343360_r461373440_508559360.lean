-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r461373440_508559360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:44:29.488777+00:00
-- url     : https://prove2.me/submissions/7001f048-3c8a-480e-84f3-3e8fa7234243

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [11/20, 97/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 461373440 473169920 ⟨⟨295295477794, 295295477805⟩, ⟨280701639652, 310266374329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 107479040 110100480 461373440 473169920 ⟨⟨291281951725, 291281951735⟩, ⟨276874406217, 306062499910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 107479040 473169920 484966400 ⟨⟨301031107121, 301031107134⟩, ⟨286406633054, 316024747231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 107479040 110100480 473169920 484966400 ⟨⟨296979049494, 296979049506⟩, ⟨282538392097, 311785176454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 110100480 112721920 461373440 473169920 ⟨⟨287328886851, 287328886857⟩, ⟨273103751480, 301922989447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112721920 115343360 461373440 473169920 ⟨⟨283434330512, 283434330523⟩, ⟨269387852768, 297845763411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110100480 112721920 473169920 484966400 ⟨⟨292986709330, 292986709338⟩, ⟨278726128740, 307609069784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 112721920 115343360 473169920 484966400 ⟨⟨289052178378, 289052178390⟩, ⟨274968057823, 303494399504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 107479040 484966400 496762880 ⟨⟨306722673805, 306722673818⟩, ⟨292068393068, 321738316924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 110100480 484966400 496762880 ⟨⟨302633182948, 302633182960⟩, ⟨288160254005, 317464126284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 107479040 496762880 508559360 ⟨⟨312371850055, 312371850067⟩, ⟨297688537212, 327408807177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 107479040 110100480 496762880 508559360 ⟨⟨308245963975, 308245963987⟩, ⟨293741550526, 323101011887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 110100480 112721920 484966400 496762880 ⟨⟨298602655138, 298602655146⟩, ⟨284307477102, 313252493703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112721920 115343360 484966400 496762880 ⟨⟨294629225548, 294629225560⟩, ⟨280508314054, 309101441896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 110100480 112721920 496762880 508559360 ⟨⟨304178277542, 304178277548⟩, ⟨289849297974, 318854863988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112721920 115343360 496762880 508559360 ⟨⟨300166968353, 300166968364⟩, ⟨286010067439, 314668435266⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 461373440 508559360 t = true :=
  ⟨_, (join_sr (m := 484966400) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 473169920) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 107479040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 473169920) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 112721920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 110100480) (by decide) (join_sr (m := 496762880) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 107479040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 496762880) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 112721920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (11/20 : ℝ) (97/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  have e3 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
