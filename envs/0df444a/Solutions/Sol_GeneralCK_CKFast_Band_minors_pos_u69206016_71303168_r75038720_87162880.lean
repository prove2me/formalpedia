-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u69206016_71303168_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:26:37.51067+00:00
-- url     : https://prove2.me/submissions/b34f95d7-9d20-442c-9bc5-e792f180cff1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/400, 17/200]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 69206016 69730304 75038720 78069760 ⟨⟨88284089282, 88284089292⟩, ⟨84272664201, 92362675610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 69730304 70254592 75038720 78069760 ⟨⟨87803925686, 87803925696⟩, ⟨83816223454, 91858065933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 69206016 69730304 78069760 81100800 ⟨⟨91333332021, 91333332031⟩, ⟨87314115035, 95419093511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69730304 70254592 78069760 81100800 ⟨⟨90840232596, 90840232608⟩, ⟨86844697454, 94901601902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 70254592 70778880 75038720 78069760 ⟨⟨87328580337, 87328580350⟩, ⟨83364309693, 91358577851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 70778880 71303168 75038720 78069760 ⟨⟨86857974209, 86857974219⟩, ⟨82916849326, 90864126624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 70254592 70778880 78069760 81100800 ⟨⟨90352035599, 90352035609⟩, ⟨86379893302, 94389313476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 70778880 71303168 78069760 81100800 ⟨⟨89868661277, 89868661287⟩, ⟨85919628181, 93882142872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 69206016 69730304 81100800 84131840 ⟨⟨94355026007, 94355026020⟩, ⟨90328379241, 98447606061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 69730304 70254592 81100800 84131840 ⟨⟨93849322520, 93849322533⟩, ⟨89846311640, 97917569025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 69206016 69730304 84131840 87162880 ⟨⟨97349735344, 97349735357⟩, ⟨93316007443, 101448790848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 69730304 70254592 84131840 87162880 ⟨⟨96831749064, 96831749074⟩, ⟨92821606440, 100906534108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 70254592 70778880 81100800 84131840 ⟨⟨93348600712, 93348600723⟩, ⟨89368939050, 97392811788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 70778880 71303168 81100800 84131840 ⟨⟨92852780203, 92852780216⟩, ⟨88896186366, 96873248441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 70254592 70778880 84131840 87162880 ⟨⟨96318819021, 96318819031⟩, ⟨92331977394, 100369629026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 70778880 71303168 84131840 87162880 ⟨⟨95810864293, 95810864305⟩, ⟨91847044583, 99837989246⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 69206016 71303168 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 70254592) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 69730304) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 69730304) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 70778880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 70778880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 70254592) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 69730304) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 69730304) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 84131840) (by decide) (join_su (m := 70778880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 70778880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/400 : ℝ) (17/200 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((69206016 : ℤ) : ℝ) / (D : ℝ)) = (33/400 : ℝ) := by norm_num [D]
  have e1 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
