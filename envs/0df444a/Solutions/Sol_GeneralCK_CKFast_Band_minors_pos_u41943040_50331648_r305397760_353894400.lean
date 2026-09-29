-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r305397760_353894400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:52:40.999564+00:00
-- url     : https://prove2.me/submissions/e4224ec6-ac2a-4b83-91c3-c47a4cfafa1f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 3/50]`, `ρ ∈ [233/640, 27/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 41943040 44040192 305397760 317521920 ⟨⟨326986065372, 326986065389⟩, ⟨306803944879, 347860259181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 44040192 46137344 305397760 317521920 ⟨⟨321793679331, 321793679347⟩, ⟨301995305459, 342269965642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 41943040 44040192 317521920 329646080 ⟨⟨334794431302, 334794431316⟩, ⟨314745595881, 355501289438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 44040192 46137344 317521920 329646080 ⟨⟨329592521804, 329592521817⟩, ⟨309914924723, 349915650408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 46137344 48234496 305397760 317521920 ⟨⟨316749308279, 316749308295⟩, ⟨297320686256, 336841986438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 48234496 50331648 305397760 317521920 ⟨⟨311845177959, 311845177976⟩, ⟨292773145681, 331567722312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 46137344 48234496 317521920 329646080 ⟨⟨324535026764, 324535026780⟩, ⟨305215481134, 344487827764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 48234496 50331648 317521920 329646080 ⟨⟨319614471219, 319614471235⟩, ⟨300640563717, 339209586045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 41943040 44040192 329646080 341770240 ⟨⟨342451804831, 342451804847⟩, ⟨322533962666, 362995425066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 44040192 46137344 329646080 341770240 ⟨⟨337242584526, 337242584543⟩, ⟨317684003043, 357415979606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 41943040 44040192 341770240 353894400 ⟨⟨349967543105, 349967543122⟩, ⟨330178308556, 370351981688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 44040192 46137344 341770240 353894400 ⟨⟨344752948479, 344752948495⟩, ⟨325311500824, 364780033720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 46137344 48234496 329646080 341770240 ⟨⟨332174280188, 332174280204⟩, ⟨312962523805, 351990022547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 48234496 50331648 329646080 341770240 ⟨⟨327239697822, 327239697838⟩, ⟨308363051067, 346709657331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 46137344 48234496 341770240 353894400 ⟨⟨339675874071, 339675874087⟩, ⟨320570477114, 359357410711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 48234496 50331648 341770240 353894400 ⟨⟨334729389775, 334729389791⟩, ⟨315948978969, 354076532123⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 50331648 305397760 353894400 t = true :=
  ⟨_, (join_sr (m := 329646080) (by decide) (join_su (m := 46137344) (by decide) (join_sr (m := 317521920) (by decide) (join_su (m := 44040192) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 44040192) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 317521920) (by decide) (join_su (m := 48234496) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 48234496) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 46137344) (by decide) (join_sr (m := 341770240) (by decide) (join_su (m := 44040192) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 44040192) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 341770240) (by decide) (join_su (m := 48234496) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 48234496) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  have e3 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
