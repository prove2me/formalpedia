-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:44:00.298484+00:00
-- url     : https://prove2.me/submissions/aa555785-8bb6-4101-89bd-f6f541d21595

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [113/320, 61/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 296222720 302120960 ⟨⟨182980304729, 182980304738⟩, ⟨172987517742, 193246633555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 125829120 128450560 302120960 308019200 ⟨⟨186027882035, 186027882043⟩, ⟨176004214106, 196323540066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 128450560 131072000 296222720 302120960 ⟨⟨180161174709, 180161174720⟩, ⟨170299216088, 190291828298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 302120960 308019200 ⟨⟨183176298878, 183176298887⟩, ⟨173283076906, 193336770493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 125829120 128450560 308019200 313917440 ⟨⟨189060441593, 189060441601⟩, ⟨179006249709, 199385070480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 125829120 128450560 313917440 319815680 ⟨⟨192078252836, 192078252845⟩, ⟨181993885002, 202431503342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 128450560 131072000 308019200 313917440 ⟨⟨186176922376, 186176922385⟩, ⟨176252782214, 196366864556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 128450560 131072000 313917440 319815680 ⟨⟨189163301443, 189163301452⟩, ⟨179208579784, 199382375324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 133693440 296222720 302120960 ⟨⟨177392514957, 177392514967⟩, ⟨167657957847, 187391063392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 131072000 133693440 302120960 308019200 ⟨⟨180375211673, 180375211683⟩, ⟨170609050719, 190404019347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133693440 136314880 296222720 302120960 ⟨⟨174672556961, 174672556971⟩, ⟨165062108738, 184542430615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 133693440 136314880 302120960 308019200 ⟨⟨177622863557, 177622863567⟩, ⟨167980510148, 187523393149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131072000 133693440 308019200 313917440 ⟨⟨183343909774, 183343909784⟩, ⟨173546478328, 193402640209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 131072000 133693440 313917440 319815680 ⟨⟨186298852937, 186298852947⟩, ⟨176470476385, 196387177751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 133693440 136314880 308019200 313917440 ⟨⟨180559658905, 180559658915⟩, ⟨170885721916, 190490518986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 136314880 313917440 319815680 ⟨⟨183483174719, 183483174730⟩, ⟨173777968266, 193444047463⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 296222720 319815680 t = true :=
  ⟨_, (join_su (m := 131072000) (by decide) (join_sr (m := 308019200) (by decide) (join_su (m := 128450560) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 302120960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 128450560) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 313917440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 308019200) (by decide) (join_su (m := 133693440) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 302120960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 133693440) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 313917440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
