-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u56623104_58720256_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:59:44.953625+00:00
-- url     : https://prove2.me/submissions/bfff87d3-ba90-48b3-9b52-8bf2b0c8ff0c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/400, 7/100]`, `ρ ∈ [229/2560, 133/1280]` by 12 cells of the computing
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
theorem cell0 : cellOK 56623104 57147392 75038720 78069760 ⟨⟨101495588133, 101495588145⟩, ⟨96810436102, 106269761551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 57147392 57671680 75038720 78069760 ⟨⟨100870443955, 100870443969⟩, ⟨96218077966, 105610710141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 56623104 57147392 78069760 81100800 ⟨⟨104882399353, 104882399365⟩, ⟨100191389429, 109661375380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 57147392 57671680 78069760 81100800 ⟨⟨104242087265, 104242087280⟩, ⟨99583734056, 108987310098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 57671680 58195968 75038720 78069760 ⟨⟨100252707247, 100252707258⟩, ⟨95632650940, 104959564442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 58195968 58720256 75038720 78069760 ⟨⟨99642236171, 99642236182⟩, ⟨95054023639, 104316171597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 57671680 58195968 78069760 81100800 ⟨⟨103609283239, 103609283251⟩, ⟨98983115853, 108321244947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 58195968 58720256 78069760 81100800 ⟨⟨102983844860, 102983844871⟩, ⟨98389402653, 107663026716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 56623104 57671680 81100800 84131840 ⟨⟨107903489394, 107903489405⟩, ⟨101102854736, 114890509847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 56623104 57671680 84131840 87162880 ⟨⟨111209556873, 111209556885⟩, ⟨104398759110, 118204742308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 57671680 58720256 81100800 84131840 ⟨⟨106608661723, 106608661737⟩, ⟨99897937584, 113501359444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 57671680 58720256 84131840 87162880 ⟨⟨109886460095, 109886460110⟩, ⟨103165234150, 116787753968⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 56623104 58720256 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 57671680) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 57147392) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 57147392) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 58195968) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 58195968) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 57671680) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 84131840) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/400 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((56623104 : ℤ) : ℝ) / (D : ℝ)) = (27/400 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
