-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r175964160_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:01:01.195738+00:00
-- url     : https://prove2.me/submissions/80468d99-fd07-4562-bfc8-5d321f8d715d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [537/2560, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 175964160 177356800 ⟨⟨53973665415, 53973665417⟩, ⟨52551876148, 55403909626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 243793920 244449280 177356800 178749440 ⟨⟨54387275121, 54387275124⟩, ⟨52963779200, 55819231739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 244449280 245104640 175964160 177356800 ⟨⟨53724429663, 53724429670⟩, ⟨52305516481, 55151770869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 177356800 178749440 ⟨⟨54136232134, 54136232139⟩, ⟨52715616741, 55565281328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 244449280 178749440 180142080 ⟨⟨54800716898, 54800716900⟩, ⟨53375514609, 56234385626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243793920 244449280 180142080 181534720 ⟨⟨55213991133, 55213991134⟩, ⟨53787082760, 56649371680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 245104640 178749440 180142080 ⟨⟨54547868846, 54547868852⟩, ⟨53125551514, 55978625748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244449280 245104640 180142080 181534720 ⟨⟨54959340182, 54959340187⟩, ⟨53535321183, 56391804512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245760000 175964160 177356800 ⟨⟨53475829344, 53475829350⟩, ⟨52059778858, 54900281097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245104640 245760000 177356800 178749440 ⟨⟨53885827864, 53885827869⟩, ⟨52468079606, 55311983194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245760000 246415360 175964160 177356800 ⟨⟨53227859809, 53227859815⟩, ⟨51814658729, 54649435567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245760000 246415360 177356800 178749440 ⟨⟨53636057645, 53636057652⟩, ⟨52221163223, 55059332574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 178749440 180142080 ⟨⟨54295662775, 54295662780⟩, ⟨52876217002, 55723521413⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 245760000 180142080 181534720 ⟨⟨54705334451, 54705334457⟩, ⟨53284191422, 56134896132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246415360 178749440 180142080 ⟨⟨54044093998, 54044094003⟩, ⟨52627506480, 55469067842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 180142080 181534720 ⟨⟨54451969238, 54451969243⟩, ⟨53033688869, 55878641744⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 175964160 181534720 t = true :=
  ⟨_, (join_su (m := 245104640) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 177356800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 244449280) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 180142080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 178749440) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 177356800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245760000) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 180142080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (537/2560 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
