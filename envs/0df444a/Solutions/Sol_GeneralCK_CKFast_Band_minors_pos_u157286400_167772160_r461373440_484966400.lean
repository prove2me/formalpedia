-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r461373440_484966400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:08:58.568255+00:00
-- url     : https://prove2.me/submissions/bb44fabc-eae4-4d75-a425-806cec427b52

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [11/20, 37/64]` by 15 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 461373440 467271680 ⟨⟨223423179354, 223423179364⟩, ⟨213942261557, 233109031744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 159907840 467271680 473169920 ⟨⟨225861456865, 225861456873⟩, ⟨216352206516, 235574885996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 162529280 461373440 467271680 ⟨⟨220339221189, 220339221199⟩, ⟨210951815946, 229929643968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 467271680 473169920 ⟨⟨222753654251, 222753654259⟩, ⟨213337694347, 232371928169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 159907840 473169920 484966400 ⟨⟨229506991999, 229506992009⟩, ⟨217965100174, 241348096295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 159907840 162529280 473169920 479068160 ⟨⟨225161937651, 225161937661⟩, ⟨215717550282, 234807929902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 162529280 479068160 484966400 ⟨⟨227564165018, 227564165026⟩, ⟨218091475055, 237237745132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 162529280 165150720 461373440 467271680 ⟨⟨217288822405, 217288822409⟩, ⟨207993315828, 226785454087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 165150720 467271680 473169920 ⟨⟨219679312650, 219679312653⟩, ⟨210355050590, 229204046653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165150720 167772160 461373440 467271680 ⟨⟨214271095242, 214271095252⟩, ⟨205065917215, 223675530477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 167772160 467271680 473169920 ⟨⟨216637551296, 216637551304⟩, ⟨207403437321, 226070317819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 162529280 165150720 473169920 479068160 ⟨⟨222063852004, 222063852009⟩, ⟨212710957059, 231616559986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 162529280 165150720 479068160 484966400 ⟨⟨224442530172, 224442530177⟩, ⟨215061122739, 234023086008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 167772160 473169920 479068160 ⟨⟨218998250779, 218998250789⟩, ⟨209735318850, 228459224747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 167772160 479068160 484966400 ⟨⟨221353279618, 221353279628⟩, ⟨212061645643, 230842339286⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 461373440 484966400 t = true :=
  ⟨_, (join_su (m := 162529280) (by decide) (join_sr (m := 473169920) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 467271680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 467271680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 159907840) (by decide) (leaf_ok cell4) (join_sr (m := 479068160) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 473169920) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 467271680) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 467271680) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 165150720) (by decide) (join_sr (m := 479068160) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 479068160) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (11/20 : ℝ) (37/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  have e3 : (((484966400 : ℤ) : ℝ) / (D : ℝ)) = (37/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
