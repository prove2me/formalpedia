-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_110100480_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:26:28.075406+00:00
-- url     : https://prove2.me/submissions/b2c6f1fe-74c8-435d-be17-ed3b250bfbe7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 21/160]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 106168320 154664960 157614080 ⟨⟨120654313343, 120654313354⟩, ⟨115399742791, 126006127920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 106168320 157614080 160563200 ⟨⟨122636406950, 122636406960⟩, ⟨117371241473, 127998446313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 106168320 107479040 154664960 157614080 ⟨⟨119511104300, 119511104311⟩, ⟨114302755248, 124815272789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 106168320 107479040 157614080 160563200 ⟨⟨121478953318, 121478953327⟩, ⟨116259971003, 126793400261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 106168320 160563200 163512320 ⟨⟨124609900345, 124609900356⟩, ⟨119334271378, 129982033382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 106168320 163512320 166461440 ⟨⟨126574895618, 126574895626⟩, ⟨121288932179, 131956993658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 106168320 107479040 160563200 163512320 ⟨⟨123438388507, 123438388516⟩, ⟨118208901259, 128762985802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 106168320 107479040 163512320 166461440 ⟨⟨125389508651, 125389508661⟩, ⟨120149642478, 130724130545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 107479040 108789760 154664960 157614080 ⟨⟨118384067588, 118384067594⟩, ⟨113221060078, 123641504595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 108789760 157614080 160563200 ⟨⟨120337770306, 120337770312⟩, ⟨115164095913, 125605534109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 108789760 110100480 154664960 157614080 ⟨⟨117272802480, 117272802490⟩, ⟨112154281573, 122484396463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 108789760 110100480 157614080 160563200 ⟨⟨119212456779, 119212456789⟩, ⟨114083239831, 124434420862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 107479040 108789760 160563200 163512320 ⟨⟨122283241337, 122283241343⟩, ⟨117099025341, 127561206800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 107479040 108789760 163512320 166461440 ⟨⟨124220576280, 124220576287⟩, ⟨119025941727, 129508620517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 108789760 110100480 160563200 163512320 ⟨⟨121144057403, 121144057411⟩, ⟨116004266699, 126376269355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 108789760 110100480 163512320 166461440 ⟨⟨123067696872, 123067696880⟩, ⟨117917452553, 128310036636⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 110100480 154664960 166461440 t = true :=
  ⟨_, (join_su (m := 107479040) (by decide) (join_sr (m := 160563200) (by decide) (join_su (m := 106168320) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 157614080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 106168320) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163512320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 160563200) (by decide) (join_su (m := 108789760) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 157614080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 108789760) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163512320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
