-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r571473920_593756160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:43:51.207983+00:00
-- url     : https://prove2.me/submissions/03fd2072-0efb-416b-863f-aefc793e64a1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [109/160, 453/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 571473920 577044480 ⟨⟨163429132159, 163429132167⟩, ⟨159151572567, 167758219201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247726080 249036800 571473920 577044480 ⟨⟨162044324604, 162044324613⟩, ⟨157786695680, 166353272454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247726080 577044480 582615040 ⟨⟨164920145100, 164920145108⟩, ⟨160628705639, 169263143335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 577044480 582615040 ⟨⟨163524228215, 163524228223⟩, ⟨159252752202, 167847057219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 250347520 571473920 577044480 ⟨⟨160663099772, 160663099780⟩, ⟨156425298574, 164952011970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250347520 251658240 571473920 577044480 ⟨⟨159285416192, 159285416200⟩, ⟨155067340688, 163554395371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249036800 250347520 577044480 582615040 ⟨⟨162131885702, 162131885710⟩, ⟨157880271122, 166434648036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250347520 251658240 577044480 582615040 ⟨⟨160743076295, 160743076303⟩, ⟨156511222026, 165025873627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247726080 582615040 588185600 ⟨⟨166409954298, 166409954306⟩, ⟨162104638835, 170766858919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 249036800 582615040 588185600 ⟨⟨165002955732, 165002955740⟩, ⟨160717635995, 169339661605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247726080 588185600 593756160 ⟨⟨167898574685, 167898574692⟩, ⟨163579386957, 172269381012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247726080 249036800 588185600 593756160 ⟨⟨166480521705, 166480521712⟩, ⟨162181361490, 170831100276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 582615040 588185600 ⟨⟨163599522758, 163599522766⟩, ⟨159334097671, 167916131449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251658240 582615040 588185600 ⟨⟨162199614314, 162199614322⟩, ⟨157953983674, 166496226523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249036800 250347520 588185600 593756160 ⟨⟨165066025114, 165066025122⟩, ⟨160786792277, 169396476499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 588185600 593756160 ⟨⟨163655044056, 163655044064⟩, ⟨159395639324, 167965467974⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 571473920 593756160 t = true :=
  ⟨_, (join_sr (m := 582615040) (by decide) (join_su (m := 249036800) (by decide) (join_sr (m := 577044480) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 247726080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 577044480) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250347520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249036800) (by decide) (join_sr (m := 588185600) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 247726080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 588185600) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250347520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (453/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
