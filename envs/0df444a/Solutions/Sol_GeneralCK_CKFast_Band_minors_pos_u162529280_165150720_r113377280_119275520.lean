-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_165150720_r113377280_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:30:08.859256+00:00
-- url     : https://prove2.me/submissions/9e73d20a-7f83-44ba-93e3-c939048e3f0a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 63/320]`, `ρ ∈ [173/1280, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163184640 113377280 114851840 ⟨⟨60945405408, 60945405415⟩, ⟨59101126640, 62804031762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162529280 163184640 114851840 116326400 ⟨⟨61692019383, 61692019389⟩, ⟨59845099826, 63553283282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163184640 163840000 113377280 114851840 ⟨⟨60679718137, 60679718143⟩, ⟨58841039109, 62532667391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163184640 163840000 114851840 116326400 ⟨⟨61423387005, 61423387011⟩, ⟨59582074655, 63278966529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 163184640 116326400 117800960 ⟨⟨62437698797, 62437698805⟩, ⟨60588144485, 64301594163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 163184640 117800960 119275520 ⟨⟨63182447369, 63182447377⟩, ⟨61330264304, 65048968151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163184640 163840000 116326400 117800960 ⟨⟨62166131947, 62166131955⟩, ⟨60322192216, 64024335754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163184640 163840000 117800960 119275520 ⟨⟨62907956620, 62907956627⟩, ⟨61061395416, 64768778753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 163840000 164495360 113377280 114851840 ⟨⟨60415355903, 60415355911⟩, ⟨58582237472, 62262667932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 164495360 114851840 116326400 ⟨⟨61156090882, 61156090890⟩, ⟨59320346588, 63006025906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 164495360 165150720 113377280 114851840 ⟨⟨60152305871, 60152305877⟩, ⟨58324709308, 61994020121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 164495360 165150720 114851840 116326400 ⟨⟨60890118091, 60890118098⟩, ⟨59059903117, 62734448069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163840000 164495360 116326400 117800960 ⟨⟨61895912449, 61895912456⟩, ⟨60057548141, 63748464576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 163840000 164495360 117800960 119275520 ⟨⟨62634824202, 62634824208⟩, ⟨60793845697, 64489987566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 164495360 165150720 116326400 117800960 ⟨⟨61627027296, 61627027302⟩, ⟨59794199669, 63473967197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 164495360 165150720 117800960 119275520 ⟨⟨62363037024, 62363037031⟩, ⟨60527602475, 64212581076⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 165150720 113377280 119275520 t = true :=
  ⟨_, (join_su (m := 163840000) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 163184640) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114851840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 163184640) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 117800960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 116326400) (by decide) (join_su (m := 164495360) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114851840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 164495360) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 117800960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (173/1280 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
