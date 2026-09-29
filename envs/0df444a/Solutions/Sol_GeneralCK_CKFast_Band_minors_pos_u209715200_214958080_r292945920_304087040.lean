-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_214958080_r292945920_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:43:18.694986+00:00
-- url     : https://prove2.me/submissions/99cde539-6bb1-41e5-9019-3660d34a505a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 41/160]`, `ρ ∈ [447/1280, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 211025920 292945920 295731200 ⟨⟨109991708240, 109991708247⟩, ⟨106501061024, 113523768636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 211025920 295731200 298516480 ⟨⟨110967023123, 110967023131⟩, ⟨107469001212, 114506475150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 211025920 212336640 292945920 295731200 ⟨⟨109098977444, 109098977450⟩, ⟨105624332297, 112614778423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 211025920 212336640 295731200 298516480 ⟨⟨110067351595, 110067351602⟩, ⟨106585353867, 113590523274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 211025920 298516480 301301760 ⟨⟨111941340254, 111941340261⟩, ⟨108435951576, 115488175696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 211025920 301301760 304087040 ⟨⟨112914665184, 112914665190⟩, ⟨109401917622, 116468875876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 211025920 212336640 298516480 301301760 ⟨⟨111034749531, 111034749539⟩, ⟨107545406846, 114565284005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 211025920 212336640 301301760 304087040 ⟨⟨112001176653, 112001176659⟩, ⟨108504496586, 115539066066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 212336640 213647360 292945920 295731200 ⟨⟨108211004631, 108211004634⟩, ⟨104752212529, 111710698188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 212336640 213647360 295731200 298516480 ⟨⟨109172453433, 109172453436⟩, ⟨105706331170, 112679496421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 213647360 214958080 292945920 295731200 ⟨⟨107327723904, 107327723911⟩, ⟨103884637949, 110811459868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 213647360 214958080 295731200 298516480 ⟨⟨108282262673, 108282262681⟩, ⟨104831869274, 111773326478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 212336640 213647360 298516480 301301760 ⟨⟨110132947185, 110132947189⟩, ⟨106659502083, 113647332008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 212336640 213647360 301301760 304087040 ⟨⟨111092491142, 111092491144⟩, ⟨107611730481, 114614210244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 213647360 214958080 298516480 301301760 ⟨⟨109235867194, 109235867201⟩, ⟨105778173376, 112734251541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 213647360 214958080 301301760 304087040 ⟨⟨110188542575, 110188542581⟩, ⟨106723555325, 113694240209⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 214958080 292945920 304087040 t = true :=
  ⟨_, (join_su (m := 212336640) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 211025920) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 295731200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 211025920) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 301301760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 298516480) (by decide) (join_su (m := 213647360) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 295731200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 213647360) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 301301760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (447/1280 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
