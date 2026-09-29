-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_242483200_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:49.628014+00:00
-- url     : https://prove2.me/submissions/80c4e9c9-fb21-40b1-b853-ab6c90abbf7a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 37/128]`, `ρ ∈ [243/1280, 503/2560]` by 13 cells of the computing
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
theorem cell0 : cellOK 241172480 241500160 159252480 160645120 ⟨⟨49970194527, 49970194532⟩, ⟨49141918389, 50801497403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241500160 241827840 159252480 160645120 ⟨⟨49855141308, 49855141309⟩, ⟨49027893754, 50685409638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241500160 160645120 162037760 ⟨⟨50393683748, 50393683753⟩, ⟨49564471598, 51225923989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241500160 241827840 160645120 162037760 ⟨⟨50277705483, 50277705486⟩, ⟨49449523322, 51108909783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241827840 242155520 159252480 160645120 ⟨⟨49740241978, 49740241983⟩, ⟨48914020740, 50569478060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 242155520 242483200 159252480 160645120 ⟨⟨49625495972, 49625495978⟩, ⟨48800298787, 50453702084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242155520 160645120 162037760 ⟨⟨50161882027, 50161882033⟩, ⟨49334727579, 50992052684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242155520 242483200 160645120 162037760 ⟨⟨50046212809, 50046212814⟩, ⟨49220083813, 50875352103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241827840 162037760 163430400 ⟨⟨50758519939, 50758519945⟩, ⟨49342354402, 52183192850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241172480 241827840 163430400 164823040 ⟨⟨51181183204, 51181183209⟩, ⟨49763289719, 52607589806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241827840 242155520 162037760 163430400 ⟨⟨50583341965, 50583341971⟩, ⟨49755254606, 51414446895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242155520 242483200 162037760 163430400 ⟨⟨50466750700, 50466750706⟩, ⟨49639690186, 51296822878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 241827840 242483200 163430400 164823040 ⟨⟨50945846666, 50945846671⟩, ⟨49530842919, 52369335674⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 242483200 159252480 164823040 t = true :=
  ⟨_, (join_sr (m := 162037760) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 160645120) (by decide) (join_su (m := 241500160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241500160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 160645120) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 242155520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 241827840) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 163430400) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (37/128 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
