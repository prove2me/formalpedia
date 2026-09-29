-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_247726080_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:51:16.116643+00:00
-- url     : https://prove2.me/submissions/b43a2928-b951-48a9-8f58-2b6a9ffffe8d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 189/640]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 246743040 136970240 138362880 ⟨⟨41584084416, 41584084419⟩, ⟨40786650031, 42384429030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246743040 247070720 136970240 138362880 ⟨⟨41486147127, 41486147134⟩, ⟨40689683283, 42285515465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 246743040 138362880 139755520 ⟨⟨41995562213, 41995562215⟩, ⟨41197210232, 42796825907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 246743040 247070720 138362880 139755520 ⟨⟨41896696479, 41896696484⟩, ⟨41099316489, 42696982451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247070720 247398400 136970240 138362880 ⟨⟨41388340088, 41388340093⟩, ⟨40592844666, 42186734279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247398400 247726080 136970240 138362880 ⟨⟨41290662805, 41290662810⟩, ⟨40496133694, 42088084982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247398400 138362880 139755520 ⟨⟨41797961962, 41797961967⟩, ⟨41001551842, 42597272346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247398400 247726080 138362880 139755520 ⟨⟨41699358166, 41699358171⟩, ⟨40903915805, 42497695095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 246743040 139755520 141148160 ⟨⟨42406869598, 42406869601⟩, ⟨41607600269, 43209052125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 246743040 247070720 139755520 141148160 ⟨⟨42307076551, 42307076557⟩, ⟨41508780658, 43108279917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 246743040 141148160 142540800 ⟨⟨42818006958, 42818006960⟩, ⟨42017820523, 43621108069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 246743040 247070720 141148160 142540800 ⟨⟨42717287728, 42717287733⟩, ⟨41918076169, 43519408242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247070720 247398400 139755520 141148160 ⟨⟨42207415683, 42207415689⟩, ⟨41410091103, 43007642022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247398400 247726080 139755520 141148160 ⟨⟨42107886496, 42107886502⟩, ⟨41311531115, 42907137942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247070720 247398400 141148160 142540800 ⟨⟨42616701632, 42616701637⟩, ⟨41818462827, 43417843685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 247398400 247726080 141148160 142540800 ⟨⟨42516248169, 42516248175⟩, ⟨41718980001, 43316413896⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 247726080 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 246743040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 247398400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 247070720) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 246743040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 247398400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (189/640 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
