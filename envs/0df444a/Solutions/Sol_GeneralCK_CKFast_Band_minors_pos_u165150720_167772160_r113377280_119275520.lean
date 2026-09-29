-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_167772160_r113377280_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:30:36.791585+00:00
-- url     : https://prove2.me/submissions/4bdc64c2-2c75-4d11-8d53-9f7b4dc97e81

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 1/5]`, `ρ ∈ [173/1280, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 165150720 165806080 113377280 114851840 ⟨⟨59890555361, 59890555366⟩, ⟨58068442346, 61726710862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165150720 165806080 114851840 116326400 ⟨⟨60625455870, 60625455875⟩, ⟨58800731889, 62464219833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165806080 166461440 113377280 114851840 ⟨⟨59630091853, 59630091859⟩, ⟨57813424471, 61460727224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165806080 166461440 114851840 116326400 ⟨⟨60362091616, 60362091624⟩, ⟨58542820707, 62195328190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 165806080 116326400 117800960 ⟨⟨61359463645, 61359463649⟩, ⟨59532134367, 63200830357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 165806080 117800960 119275520 ⟨⟨62092582167, 62092582172⟩, ⟨60262653234, 63936545945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165806080 166461440 116326400 117800960 ⟨⟨61093208811, 61093208817⟩, ⟨59271339954, 62929040962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165806080 166461440 117800960 119275520 ⟨⟨61823446864, 61823446872⟩, ⟨59998985613, 63661868998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 166461440 167116800 113377280 114851840 ⟨⟨59370902988, 59370902996⟩, ⟨57559643723, 61196056437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 166461440 167116800 114851840 116326400 ⟨⟨60100012890, 60100012896⟩, ⟨58286157525, 61927760286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167116800 167772160 113377280 114851840 ⟨⟨59112976560, 59112976568⟩, ⟨57307088285, 60932685895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 167116800 167772160 114851840 116326400 ⟨⟨59839207401, 59839207407⟩, ⟨58030730446, 61661503435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 166461440 167116800 116326400 117800960 ⟨⟨60828250275, 60828250281⟩, ⟨59011804305, 62658586082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166461440 167116800 117800960 119275520 ⟨⟨61555618518, 61555618524⟩, ⟨59736587408, 63388537225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 167116800 167772160 116326400 117800960 ⟨⟨60564575666, 60564575674⟩, ⟨58753515441, 62389452950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 167116800 167772160 117800960 119275520 ⟨⟨61289084677, 61289084683⟩, ⟨59475446562, 63116537783⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 167772160 113377280 119275520 t = true :=
  ⟨_, (join_su (m := 166461440) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 165806080) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114851840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 165806080) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 117800960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 116326400) (by decide) (join_su (m := 167116800) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114851840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 167116800) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 117800960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (173/1280 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
