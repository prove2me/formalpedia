-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_162529280_r107479040_113377280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:26:19.734982+00:00
-- url     : https://prove2.me/submissions/ca2ac28e-176b-4442-a4f2-321bf11c1ec8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 31/160]`, `ρ ∈ [41/320, 173/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 159907840 160563200 107479040 108953600 ⟨⟨58977771408, 58977771415⟩, ⟨57121441389, 60848781612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 160563200 108953600 110428160 ⟨⟨59740232942, 59740232950⟩, ⟨57881206210, 61613936012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 160563200 161218560 107479040 108953600 ⟨⟨58718728059, 58718728067⟩, ⟨56868127692, 60583927424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160563200 161218560 108953600 110428160 ⟨⟨59478153630, 59478153638⟩, ⟨57624864436, 61346038181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159907840 160563200 110428160 111902720 ⟨⟨60501700113, 60501700119⟩, ⟨58639983217, 62378089449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 159907840 160563200 111902720 113377280 ⟨⟨61262176962, 61262176970⟩, ⟨59397776425, 63141245997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 160563200 161218560 110428160 111902720 ⟨⟨60236596220, 60236596227⟩, ⟨58380624649, 62107159453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 160563200 161218560 111902720 113377280 ⟨⟨60994059806, 60994059814⟩, ⟨59135412278, 62867295257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 161218560 161873920 107479040 108953600 ⟨⟨58461015275, 58461015283⟩, ⟨56616103724, 60320445423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 161218560 161873920 108953600 110428160 ⟨⟨59217416954, 59217416961⟩, ⟨57369824453, 61079524609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161873920 162529280 107479040 108953600 ⟨⟨58204619908, 58204619912⟩, ⟨56365356777, 60058322003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161873920 162529280 108953600 110428160 ⟨⟨58958009671, 58958009674⟩, ⟨57116073455, 60814381601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 161873920 110428160 111902720 ⟨⟨59972846905, 59972846911⟩, ⟨58122579802, 61837625665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161218560 161873920 111902720 113377280 ⟨⟨60727309040, 60727309048⟩, ⟨58874373658, 62594752539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161873920 162529280 110428160 111902720 ⟨⟨59710438830, 59710438834⟩, ⟨57865835784, 61569474295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161873920 162529280 111902720 113377280 ⟨⟨60461911239, 60461911241⟩, ⟨58614647581, 62323603968⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 162529280 107479040 113377280 t = true :=
  ⟨_, (join_su (m := 161218560) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 160563200) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 108953600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 160563200) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 111902720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 110428160) (by decide) (join_su (m := 161873920) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 108953600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 161873920) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 111902720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (173/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
