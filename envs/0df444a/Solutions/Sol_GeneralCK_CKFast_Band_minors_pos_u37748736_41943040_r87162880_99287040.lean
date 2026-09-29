-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:39:35.435788+00:00
-- url     : https://prove2.me/submissions/ef2e242e-8212-4af5-885d-c9ebe7cc006d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/200, 1/20]`, `ρ ∈ [133/1280, 303/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 37748736 38797312 87162880 90193920 ⟨⟨145634604751, 145634604766⟩, ⟨136616538204, 154950560997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 37748736 38797312 90193920 93224960 ⟨⟨149393984233, 149393984251⟩, ⟨140382306595, 158698581900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 38797312 39845888 87162880 90193920 ⟨⟨143464654553, 143464654557⟩, ⟨134608232622, 152609782888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 38797312 39845888 90193920 93224960 ⟨⟨147193205041, 147193205047⟩, ⟨138341644824, 156328781130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 37748736 38797312 93224960 96256000 ⟨⟨153099732268, 153099732286⟩, ⟨144095274184, 162392247026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 37748736 38797312 96256000 99287040 ⟨⟨156753509143, 156753509162⟩, ⟨147757041692, 166033273800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 38797312 39845888 93224960 96256000 ⟨⟨150869560781, 150869560788⟩, ⟨142023686989, 159994856995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 38797312 39845888 96256000 99287040 ⟨⟨154495309566, 154495309573⟩, ⟨145655889886, 163609653188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 39845888 40894464 87162880 90193920 ⟨⟨141359602416, 141359602431⟩, ⟨132658776512, 150340392254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 39845888 40894464 90193920 93224960 ⟨⟨145057439052, 145057439070⟩, ⟨136360065687, 154030345598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 40894464 41943040 87162880 90193920 ⟨⟨139316361871, 139316361885⟩, ⟨130765417362, 148138940458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 40894464 41943040 90193920 93224960 ⟨⟨142983627616, 142983627630⟩, ⟨134434834700, 151799865884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 39845888 40894464 93224960 96256000 ⟨⟨148704472482, 148704472500⟩, ⟨140011368659, 157668767451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 39845888 40894464 96256000 99287040 ⟨⟨152302221702, 152302221720⟩, ⟨143614149856, 161257229559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 40894464 41943040 93224960 96256000 ⟨⟨146601437891, 146601437905⟩, ⟨138055604379, 155410609182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 40894464 41943040 96256000 99287040 ⟨⟨150171246392, 150171246407⟩, ⟨141629127895, 158972674670⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 37748736 41943040 87162880 99287040 t = true :=
  ⟨_, (join_su (m := 39845888) (by decide) (join_sr (m := 93224960) (by decide) (join_su (m := 38797312) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 90193920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 38797312) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 96256000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 93224960) (by decide) (join_su (m := 40894464) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 90193920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 40894464) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 96256000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/200 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
