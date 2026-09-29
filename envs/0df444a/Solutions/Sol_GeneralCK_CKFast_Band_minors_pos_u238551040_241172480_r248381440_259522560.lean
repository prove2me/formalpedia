-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:44:12.488392+00:00
-- url     : https://prove2.me/submissions/ad6a1666-51e7-47f5-aab7-d50e9d9afdb5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 248381440 251166720 ⟨⟨78229036032, 78229036039⟩, ⟨76439276518, 80031392781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 239206400 239861760 248381440 251166720 ⟨⟨77881284133, 77881284140⟩, ⟨76096017698, 79679102643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 239206400 251166720 253952000 ⟨⟨79066857074, 79066857080⟩, ⟨77273395508, 80872924532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 251166720 253952000 ⟨⟨78715668489, 78715668496⟩, ⟨76926708947, 80517188885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239861760 240517120 248381440 251166720 ⟨⟨77534356454, 77534356461⟩, ⟨75753564393, 79327655683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240517120 241172480 248381440 251166720 ⟨⟨77188247252, 77188247255⟩, ⟨75411910988, 78977046027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239861760 240517120 251166720 253952000 ⟨⟨78365308704, 78365308711⟩, ⟨76580832493, 80162300987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240517120 241172480 251166720 253952000 ⟨⟨78015771955, 78015771958⟩, ⟨76235760504, 79808254940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239206400 253952000 256737280 ⟨⟨79904023169, 79904023175⟩, ⟨78106861834, 81713799001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239206400 239861760 253952000 256737280 ⟨⟨79549405954, 79549405959⟩, ⟨77756755519, 81354625968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 239206400 256737280 259522560 ⟨⟨80740537493, 80740537500⟩, ⟨78939678653, 82554019374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239206400 239861760 256737280 259522560 ⟨⟨80382499651, 80382499658⟩, ⟨78586160527, 82191417027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239861760 240517120 253952000 256737280 ⟨⟨79195622039, 79195622046⟩, ⟨77407463825, 80996305172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240517120 241172480 253952000 256737280 ⟨⟨78842665643, 78842665646⟩, ⟨77058981090, 80638830698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 240517120 256737280 259522560 ⟨⟨80025299538, 80025299545⟩, ⟨78233461458, 81829671328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240517120 241172480 256737280 259522560 ⟨⟨79668931347, 79668931350⟩, ⟨77881575763, 81468776346⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 248381440 259522560 t = true :=
  ⟨_, (join_sr (m := 253952000) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 251166720) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 239206400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 251166720) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240517120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239861760) (by decide) (join_sr (m := 256737280) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 239206400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 256737280) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240517120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
