-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r315228160_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:01:14.861836+00:00
-- url     : https://prove2.me/submissions/cd006d2c-e1b2-4feb-b5b0-76ffc4a9a6cf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [481/1280, 249/640]` by 15 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 315228160 318013440 ⟨⟨114004912386, 114004912392⟩, ⟨110519298645, 117531092087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 214958080 216268800 318013440 320798720 ⟨⟨114945383787, 114945383795⟩, ⟨111452538400, 118478814512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 216268800 217579520 315228160 318013440 ⟨⟨113076340315, 113076340322⟩, ⟨109606323480, 116586686066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 318013440 320798720 ⟨⟨114010089023, 114010089030⟩, ⟨110532861601, 117527665843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 216268800 320798720 326369280 ⟨⟨116354452366, 116354452373⟩, ⟨112234655490, 120531976724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 216268800 217579520 320798720 323584000 ⟨⟨114942982068, 114942982076⟩, ⟨111458550211, 118467783543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 217579520 323584000 326369280 ⟨⟨115875024113, 115875024121⟩, ⟨112383393940, 119407043869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 217579520 218890240 315228160 318013440 ⟨⟨112152380112, 112152380118⟩, ⟨108697821673, 115647032998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218890240 318013440 320798720 ⟨⟨113079418532, 113079418538⟩, ⟨109617670874, 116581282198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 218890240 220200960 315228160 318013440 ⟨⟨111232969480, 111232969482⟩, ⟨107793732817, 114712068662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 220200960 318013440 320798720 ⟨⟨112153309982, 112153309985⟩, ⟨108706905766, 115639599333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 218890240 320798720 323584000 ⟨⟨114005619981, 114005619988⟩, ⟨110536688994, 117514688285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 323584000 326369280 ⟨⟨114930988998, 114930989004⟩, ⟨111454880534, 118447255828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218890240 220200960 320798720 323584000 ⟨⟨113072831889, 113072831892⟩, ⟨109619265752, 116566305525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 220200960 323584000 326369280 ⟨⟨113991539611, 113991539615⟩, ⟨110530817150, 117492191688⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 315228160 326369280 t = true :=
  ⟨_, (join_su (m := 217579520) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 318013440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 216268800) (by decide) (leaf_ok cell4) (join_sr (m := 323584000) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 320798720) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 318013440) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 218890240) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 323584000) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (481/1280 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
