-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u239861760_241172480_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:39:42.299769+00:00
-- url     : https://prove2.me/submissions/1d1519e9-0a2c-43f5-8457-925d13862390

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [183/640, 23/80]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 239861760 240189440 131399680 132792320 ⟨⟨41847981273, 41847981275⟩, ⟨41034470396, 42664515602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 240189440 240517120 131399680 132792320 ⟨⟨41751139707, 41751139714⟩, ⟨40938637415, 42566659309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239861760 240189440 132792320 134184960 ⟨⟨42279018267, 42279018270⟩, ⟨41464559049, 43096502336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 240189440 240517120 132792320 134184960 ⟨⟨42181223142, 42181223149⟩, ⟨41367774014, 42997690982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 240517120 240844800 131399680 132792320 ⟨⟨41654434414, 41654434420⟩, ⟨40842938433, 42468941576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240844800 241172480 131399680 132792320 ⟨⟨41557864873, 41557864879⟩, ⟨40747372937, 42371361882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 240517120 240844800 132792320 134184960 ⟨⟨42083565350, 42083565355⟩, ⟨41271124037, 42899019251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240844800 241172480 132792320 134184960 ⟨⟨41986044366, 41986044371⟩, ⟨41174608602, 42800486616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240189440 134184960 135577600 ⟨⟨42709859048, 42709859051⟩, ⟨41894451832, 43528292508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 240189440 240517120 134184960 135577600 ⟨⟨42611111641, 42611111646⟩, ⟨41796716014, 43428527374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 240189440 135577600 136970240 ⟨⟨43140504074, 43140504076⟩, ⟨42324149202, 43959886579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240189440 240517120 135577600 136970240 ⟨⟨43040805654, 43040805659⟩, ⟨42225463870, 43859168942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 240517120 240844800 134184960 135577600 ⟨⟨42512502617, 42512502622⟩, ⟨41699116307, 43328902919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240844800 241172480 134184960 135577600 ⟨⟨42414031452, 42414031457⟩, ⟨41601652188, 43229418610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 240844800 135577600 136970240 ⟨⟨42941246665, 42941246670⟩, ⟨42126915692, 43758593032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240844800 241172480 135577600 136970240 ⟨⟨42841826578, 42841826583⟩, ⟨42028504143, 43658158314⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 239861760 241172480 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 240189440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240844800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 240517120) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 240189440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240844800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (183/640 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
