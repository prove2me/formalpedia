-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u123207680_125829120_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:19:59.81658+00:00
-- url     : https://prove2.me/submissions/ce3258e4-3c96-4bcc-aeef-1030fdbcaed1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/320, 3/20]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 123207680 123863040 107479040 110428160 ⟨⟨76587996769, 76587996777⟩, ⟨73718367242, 79491466626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 123863040 124518400 107479040 110428160 ⟨⟨76224577712, 76224577720⟩, ⟨73367309209, 79115428496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 123207680 123863040 110428160 113377280 ⟨⟨78494321566, 78494321575⟩, ⟨75617586780, 81404794414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 123863040 124518400 110428160 113377280 ⟨⟨78123163673, 78123163680⟩, ⟨75258804563, 81021004974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 124518400 125173760 107479040 110428160 ⟨⟨75863628549, 75863628556⟩, ⟨73018612456, 78741971985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 125173760 125829120 107479040 110428160 ⟨⟨75505119446, 75505119453⟩, ⟨72672248627, 78371065730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 124518400 125173760 110428160 113377280 ⟨⟨77754513017, 77754513024⟩, ⟨74902421198, 80639834224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 125173760 125829120 110428160 113377280 ⟨⟨77388339459, 77388339468⟩, ⟨74548408016, 80261250506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 123207680 123863040 113377280 116326400 ⟨⟨80393094182, 80393094191⟩, ⟨77509333623, 83310490425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 123863040 124518400 113377280 116326400 ⟨⟨80014285564, 80014285573⟩, ⟨77142914191, 82919038919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 123207680 123863040 116326400 119275520 ⟨⟨82284396161, 82284396169⟩, ⟨79393688009, 85208637512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 123863040 124518400 116326400 119275520 ⟨⟨81898023532, 81898023539⟩, ⟨79019716963, 84809611761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 124518400 125173760 113377280 116326400 ⟨⟨79638020422, 79638020431⟩, ⟨76778930094, 82530242055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 125173760 125829120 113377280 116326400 ⟨⟨79264268331, 79264268338⟩, ⟨76417352367, 82144067901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 124518400 125173760 116326400 119275520 ⟨⟨81514229541, 81514229548⟩, ⟨78648216670, 84413275514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 125173760 125829120 116326400 119275520 ⟨⟨81132983491, 81132983498⟩, ⟨78279157888, 84019596572⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 123207680 125829120 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 124518400) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 123863040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 123863040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 125173760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 125173760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 124518400) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 123863040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 123863040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 125173760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 125173760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/320 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((123207680 : ℤ) : ℝ) / (D : ℝ)) = (47/320 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
