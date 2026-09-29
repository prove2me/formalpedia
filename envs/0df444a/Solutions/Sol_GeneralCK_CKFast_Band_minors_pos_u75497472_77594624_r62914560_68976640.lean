-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_77594624_r62914560_68976640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:30:12.364549+00:00
-- url     : https://prove2.me/submissions/4f1a81e4-ce57-40ea-b2ec-bce7a85d746d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 37/400]`, `ρ ∈ [3/40, 421/5120]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 76021760 62914560 64430080 ⟨⟨70223700969, 70223700978⟩, ⟨67496764475, 72983934179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 75497472 76021760 64430080 65945600 ⟨⟨71730080875, 71730080886⟩, ⟨68999135861, 74494204846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 76021760 76546048 62914560 64430080 ⟨⟨69850692208, 69850692219⟩, ⟨67138256619, 72596091944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 76021760 76546048 64430080 65945600 ⟨⟨71350405682, 71350405691⟩, ⟨68633964974, 74099695281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 76021760 65945600 67461120 ⟨⟨73229912011, 73229912020⟩, ⟨70495023127, 75997862334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 75497472 76021760 67461120 68976640 ⟨⟨74723259106, 74723259118⟩, ⟨71984489915, 77494972475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 76021760 76546048 65945600 67461120 ⟨⟨72843650634, 72843650643⟩, ⟨70123268490, 75596766645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 76021760 76546048 67461120 68976640 ⟨⟨74330490579, 74330490588⟩, ⟨71606229620, 77087370620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 76546048 77070336 62914560 64430080 ⟨⟨69481288823, 69481288832⟩, ⟨66783183198, 72212031367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 76546048 77070336 64430080 65945600 ⟨⟨70974383797, 70974383808⟩, ⟨68272276829, 73709014876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 77070336 77594624 62914560 64430080 ⟨⟨69115433710, 69115433722⟩, ⟨66431490167, 71831692173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 77070336 77594624 64430080 65945600 ⟨⟨70601957598, 70601957607⟩, ⟨67914016847, 73322102840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 76546048 77070336 65945600 67461120 ⟨⟨72461089280, 72461089289⟩, ⟨69755043701, 75199546375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 76546048 77070336 67461120 68976640 ⟨⟨73941467595, 73941467607⟩, ⟨71231545101, 76683689243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 77070336 77594624 65945600 67461120 ⟨⟨72082169823, 72082169834⟩, ⟨69390293663, 74806140258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 77070336 77594624 67461120 68976640 ⟨⟨73556131553, 73556131563⟩, ⟨70860380768, 76283866606⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 77594624 62914560 68976640 t = true :=
  ⟨_, (join_su (m := 76546048) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 76021760) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 64430080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 76021760) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 67461120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 65945600) (by decide) (join_su (m := 77070336) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 64430080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 77070336) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 67461120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (37/400 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (421/5120 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((77594624 : ℤ) : ℝ) / (D : ℝ)) = (37/400 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
