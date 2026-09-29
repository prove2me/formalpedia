-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u144179200_146800640_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:19:37.558128+00:00
-- url     : https://prove2.me/submissions/cfc8385e-0130-43b3-8f02-efa565dcdbc1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/64, 7/40]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 144179200 144834560 119275520 122224640 ⟨⟨72723325034, 72723325041⟩, ⟨70175910453, 75297444504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 144834560 145489920 119275520 122224640 ⟨⟨72399851475, 72399851482⟩, ⟨69862011510, 74964221656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 144179200 144834560 122224640 125173760 ⟨⟨74378562481, 74378562487⟩, ⟨71824784420, 76958994562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 144834560 145489920 122224640 125173760 ⟨⟨74048640692, 74048640698⟩, ⟨71504453055, 76619308849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 145489920 146145280 119275520 122224640 ⟨⟨72078202064, 72078202067⟩, ⟨69549864854, 74632896624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146145280 146800640 119275520 122224640 ⟨⟨71758357631, 71758357638⟩, ⟨69239452165, 74303449374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 145489920 146145280 122224640 125173760 ⟨⟨73720569166, 73720569168⟩, ⟨71185900174, 76281546960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 146145280 146800640 122224640 125173760 ⟨⟨73394328538, 73394328545⟩, ⟨70869107261, 75945688674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 144179200 144834560 125173760 128122880 ⟨⟨76028777982, 76028777990⟩, ⟨73468683736, 78615475174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 144834560 145489920 125173760 128122880 ⟨⟨75692464544, 75692464553⟩, ⟨73141975853, 78269383852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 144179200 144834560 128122880 131072000 ⟨⟨77674016859, 77674016867⟩, ⟨75107653113, 80266932274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 144834560 145489920 128122880 131072000 ⟨⟨77331367623, 77331367630⟩, ⟨74774623898, 79914491856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 145489920 146145280 125173760 128122880 ⟨⟨75358026836, 75358026839⟩, ⟨72817072013, 77925241706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 146145280 146800640 125173760 128122880 ⟨⟨75025445307, 75025445314⟩, ⟨72493953512, 77583028336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 145489920 146145280 128122880 131072000 ⟨⟨76990618944, 76990618948⟩, ⟨74443423659, 79564025320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 146145280 146800640 128122880 131072000 ⟨⟨76651751101, 76651751109⟩, ⟨74114033510, 79215512096⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 144179200 146800640 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 145489920) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 144834560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 144834560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 146145280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 146145280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 145489920) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 144834560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 144834560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 146145280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 146145280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/64 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
