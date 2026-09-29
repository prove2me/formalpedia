-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_239861760_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:38.252002+00:00
-- url     : https://prove2.me/submissions/b93c2023-842e-4934-af3a-20d7a6dab3c2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 183/640]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 238878720 125829120 127221760 ⟨⟨40495249682, 40495249689⟩, ⟨39681502804, 41312039283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238878720 239206400 125829120 127221760 ⟨⟨40401702271, 40401702276⟩, ⟨39588967040, 41217473970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 238878720 127221760 128614400 ⟨⟨40930921882, 40930921887⟩, ⟨40116219143, 41748668728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 238878720 239206400 127221760 128614400 ⟨⟨40836411382, 40836411387⟩, ⟨40022721828, 41653138797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239206400 239534080 125829120 127221760 ⟨⟨40308288855, 40308288860⟩, ⟨39496562973, 41123044974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239534080 239861760 125829120 127221760 ⟨⟨40215008923, 40215008929⟩, ⟨39404290097, 41028751775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239534080 127221760 128614400 ⟨⟨40742035981, 40742035986⟩, ⟨39929357309, 41557746286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239534080 239861760 127221760 128614400 ⟨⟨40647795162, 40647795167⟩, ⟨39836125079, 41462490675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 238878720 128614400 130007040 ⟨⟨41366390792, 41366390799⟩, ⟨40550732564, 42185094514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238878720 239206400 128614400 130007040 ⟨⟨41270918524, 41270918529⟩, ⟨40456275012, 42088601288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 238878720 130007040 131399680 ⟨⟨41801656893, 41801656898⟩, ⟨40985043542, 42621317117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 238878720 239206400 130007040 131399680 ⟨⟨41705224169, 41705224176⟩, ⟨40889627060, 42523861918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239206400 239534080 128614400 130007040 ⟨⟨41175582449, 41175582454⟩, ⟨40361951347, 41992246582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239534080 239861760 128614400 130007040 ⟨⟨41080382048, 41080382054⟩, ⟨40267761062, 41896029866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239206400 239534080 130007040 131399680 ⟨⟨41608928729, 41608928735⟩, ⟨40794345554, 42426546329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239534080 239861760 130007040 131399680 ⟨⟨41512770048, 41512770053⟩, ⟨40699198508, 42329369816⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 239861760 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 238878720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239534080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239206400) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 238878720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239534080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (183/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
