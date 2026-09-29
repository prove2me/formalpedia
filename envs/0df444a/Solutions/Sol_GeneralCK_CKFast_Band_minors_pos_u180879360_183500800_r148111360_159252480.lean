-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u180879360_183500800_r148111360_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:30:08.685966+00:00
-- url     : https://prove2.me/submissions/ccfda680-759e-4e7b-81cc-798caf3d2768

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [69/320, 7/32]`, `ρ ∈ [113/640, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 180879360 181534720 148111360 150896640 ⟨⟨69820891523, 69820891530⟩, ⟨67710278162, 71949762179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 181534720 182190080 148111360 150896640 ⟨⟨69526157311, 69526157313⟩, ⟨67422040977, 71648437529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 181534720 150896640 153681920 ⟨⟨71052883852, 71052883858⟩, ⟨68937383688, 73186632754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 181534720 182190080 150896640 153681920 ⟨⟨70753464553, 70753464557⟩, ⟨68644474163, 72880610680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 182190080 182845440 148111360 150896640 ⟨⟨69232638768, 69232638776⟩, ⟨67134980993, 71348367793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182845440 183500800 148111360 150896640 ⟨⟨68940325423, 68940325430⟩, ⟨66849088093, 71049542121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 182190080 182845440 150896640 153681920 ⟨⟨70455274536, 70455274543⟩, ⟨68352755460, 72575857112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182845440 183500800 150896640 153681920 ⟨⟨70158303241, 70158303247⟩, ⟨68062217377, 72272361114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180879360 181534720 153681920 156467200 ⟨⟨72282660218, 72282660224⟩, ⟨70162289439, 74421271037⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 181534720 182190080 153681920 156467200 ⟨⟨71978580536, 71978580540⟩, ⟨69864732025, 74110576492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 180879360 181534720 156467200 159252480 ⟨⟨73510235058, 73510235066⟩, ⟨71385009720, 75653691600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 181534720 182190080 156467200 159252480 ⟨⟨73201519478, 73201519482⟩, ⟨71082828655, 75338349315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 182190080 182845440 153681920 156467200 ⟨⟨71675743494, 71675743500⟩, ⟨69568378807, 73801163788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182845440 183500800 153681920 156467200 ⟨⟨71374138446, 71374138453⟩, ⟨69273219496, 73493021909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182190080 182845440 156467200 159252480 ⟨⟨72894059643, 72894059649⟩, ⟨70781864910, 75024301954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182845440 183500800 156467200 159252480 ⟨⟨72587844831, 72587844837⟩, ⟨70482108118, 74711538421⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 180879360 183500800 148111360 159252480 t = true :=
  ⟨_, (join_sr (m := 153681920) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 181534720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 181534720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 150896640) (by decide) (join_su (m := 182845440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182845440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 182190080) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 181534720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 181534720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 156467200) (by decide) (join_su (m := 182845440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 182845440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (69/320 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
