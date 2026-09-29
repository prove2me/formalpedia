-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u46137344_50331648_r111411200_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:45:45.518924+00:00
-- url     : https://prove2.me/submissions/99d2c3e8-b057-48b8-ac9b-cc7d7200323a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/200, 3/50]`, `ρ ∈ [17/128, 207/1280]` by 20 cells of the computing
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
theorem cell0 : cellOK 46137344 47185920 111411200 114442240 ⟨⟨156920272758, 156920272775⟩, ⟨149037773808, 165013946904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 46137344 47185920 114442240 117473280 ⟨⟨160121474856, 160121474869⟩, ⟨152240897184, 168210428138⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 47185920 48234496 111411200 114442240 ⟨⟨154987330015, 154987330032⟩, ⟨147219436140, 162961245223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 47185920 48234496 114442240 117473280 ⟨⟨158166909452, 158166909465⟩, ⟨150400058093, 166137113106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 46137344 47185920 117473280 123535360 ⟨⟨164857806373, 164857806389⟩, ⟨154121488747, 175970419274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 47185920 48234496 117473280 123535360 ⟨⟨162872277502, 162872277515⟩, ⟨152292609785, 173819116938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 48234496 49283072 111411200 114442240 ⟨⟨153100543964, 153100543981⟩, ⟨145443782368, 160958370310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 48234496 49283072 114442240 117473280 ⟨⟨156258535978, 156258535991⟩, ⟨148601994719, 164113596125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 49283072 50331648 111411200 114442240 ⟨⟨151258132759, 151258132775⟩, ⟨143709186529, 159003374348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 49283072 50331648 114442240 117473280 ⟨⟨154394587040, 154394587052⟩, ⟨146845091712, 162137948170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 48234496 49283072 117473280 123535360 ⟨⟨160932956604, 160932956617⟩, ⟨150505362305, 171718937609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 49283072 50331648 117473280 123535360 ⟨⟨159038098773, 159038098786⟩, ⟨148758200335, 169667920689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 46137344 47185920 123535360 129597440 ⟨⟨171055210552, 171055210565⟩, ⟨160335057728, 182141134259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 47185920 48234496 123535360 129597440 ⟨⟨169030978070, 169030978087⟩, ⟨158464939024, 179954132171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 46137344 47185920 129597440 135659520 ⟨⟨177124049451, 177124049468⟩, ⟨166422156970, 188181557139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 47185920 48234496 129597440 135659520 ⟨⟨175063851389, 175063851402⟩, ⟨164513540047, 185961564492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 48234496 49283072 123535360 129597440 ⟨⟨167052913048, 167052913062⟩, ⟨156636564571, 177818034001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 49283072 50331648 123535360 129597440 ⟨⟨165119301757, 165119301770⟩, ⟨154848409637, 175730921924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 48234496 49283072 129597440 135659520 ⟨⟨173049718029, 173049718045⟩, ⟨162646713395, 183792200858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 49283072 50331648 129597440 135659520 ⟨⟨171079967840, 171079967856⟩, ⟨160820175048, 181671591500⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 46137344 50331648 111411200 135659520 t = true :=
  ⟨_, (join_sr (m := 123535360) (by decide) (join_su (m := 48234496) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 47185920) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114442240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 47185920) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 117473280) (by decide) (join_su (m := 49283072) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 114442240) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 49283072) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 48234496) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 47185920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 47185920) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 129597440) (by decide) (join_su (m := 49283072) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 49283072) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/200 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((46137344 : ℤ) : ℝ) / (D : ℝ)) = (11/200 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
