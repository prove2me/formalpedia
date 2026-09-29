-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:26:20.312016+00:00
-- url     : https://prove2.me/submissions/f55a60ff-8a15-43aa-adda-009a9653d298

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 3/100]`, `ρ ∈ [207/1280, 61/320]` by 17 cells of the computing
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
theorem cell0 : cellOK 16777216 18874368 135659520 141721600 ⟨⟨269064221794, 269064221821⟩, ⟨243772239029, 295960200769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 16777216 18874368 141721600 147783680 ⟨⟨275380054660, 275380054686⟩, ⟨250361279216, 301923430910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 18874368 20971520 135659520 141721600 ⟨⟨259999125134, 259999125159⟩, ⟨235844477599, 285655371236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 18874368 20971520 141721600 147783680 ⟨⟨266336076217, 266336076242⟩, ⟨242415237824, 291688219996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 16777216 18874368 147783680 153845760 ⟨⟨281516832162, 281516832188⟩, ⟨256764436343, 307719730401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 16777216 18874368 153845760 159907840 ⟨⟨287486597887, 287486597913⟩, ⟨262993791254, 313360639095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 18874368 20971520 147783680 153845760 ⟨⟨272497986597, 272497986618⟩, ⟨248806164949, 297555257255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 18874368 20971520 153845760 159907840 ⟨⟨278496252928, 278496252948⟩, ⟨255028566435, 303267599571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 20971520 23068672 135659520 141721600 ⟨⟨251577243815, 251577243839⟩, ⟨228455654726, 276107292599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 20971520 23068672 141721600 147783680 ⟨⟨257918691570, 257918691593⟩, ⟨234997130479, 282186236471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 23068672 24117248 135659520 141721600 ⟨⟨245637565676, 245637565700⟩, ⟨230100030832, 261798438576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 24117248 25165824 135659520 141721600 ⟨⟨241841927212, 241841927231⟩, ⟨226620746966, 257667300994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 23068672 25165824 141721600 147783680 ⟨⟨250056396973, 250056396992⟩, ⟨228049082483, 273331659714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 20971520 23068672 147783680 153845760 ⟨⟨264089693033, 264089693057⟩, ⟨241364975819, 288101651434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 20971520 23068672 153845760 159907840 ⟨⟨270100994591, 270100994610⟩, ⟨247569760403, 293864166900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 23068672 25165824 147783680 153845760 ⟨⟨256223366026, 256223366045⟩, ⟨234385053810, 279277054358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 23068672 25165824 153845760 159907840 ⟨⟨262234967234, 262234967253⟩, ⟨240563510130, 285072148146⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 25165824 135659520 159907840 t = true :=
  ⟨_, (join_su (m := 20971520) (by decide) (join_sr (m := 147783680) (by decide) (join_su (m := 18874368) (by decide) (join_sr (m := 141721600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 141721600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 18874368) (by decide) (join_sr (m := 153845760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 153845760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 147783680) (by decide) (join_su (m := 23068672) (by decide) (join_sr (m := 141721600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 141721600) (by decide) (join_su (m := 24117248) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 23068672) (by decide) (join_sr (m := 153845760) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 153845760) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
