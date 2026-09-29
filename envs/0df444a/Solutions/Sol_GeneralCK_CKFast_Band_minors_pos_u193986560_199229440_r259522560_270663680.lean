-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:33:33.267984+00:00
-- url     : https://prove2.me/submissions/702fd8cf-2140-4169-958a-963fcfee7971

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 259522560 262307840 ⟨⟨108279976202, 108279976209⟩, ⟨104677166756, 111927508276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 193986560 195297280 262307840 265093120 ⟨⟨109355862168, 109355862174⟩, ⟨105745289401, 113011161828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 195297280 196608000 259522560 262307840 ⟨⟨107412286883, 107412286891⟩, ⟨103827207787, 111041772823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 262307840 265093120 ⟨⟨108480709726, 108480709732⟩, ⟨104887889631, 112117942478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 195297280 265093120 267878400 ⟨⟨110430365103, 110430365109⟩, ⟨106812042102, 114093418915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193986560 195297280 267878400 270663680 ⟨⟨111503493245, 111503493253⟩, ⟨107877433014, 115174287862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 196608000 265093120 267878400 ⟨⟨109547778559, 109547778567⟩, ⟨105947230132, 113192745115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195297280 196608000 267878400 270663680 ⟨⟨110613501399, 110613501405⟩, ⟨107005237221, 114266188831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197918720 259522560 262307840 ⟨⟨106550009297, 106550009305⟩, ⟨102982477697, 110161636038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 196608000 197918720 262307840 265093120 ⟨⟨107610990663, 107610990671⟩, ⟨104035740761, 111230343026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 197918720 199229440 259522560 262307840 ⟨⟨105693063884, 105693063891⟩, ⟨102142899774, 109287015438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197918720 199229440 262307840 265093120 ⟨⟨106746625306, 106746625314⟩, ⟨103188765951, 110348280893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 265093120 267878400 ⟨⟨108670646537, 108670646543⟩, ⟨105087690584, 112297711929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 197918720 267878400 270663680 ⟨⟨109728984710, 109728984717⟩, ⟨106138334879, 113363750625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 199229440 265093120 267878400 ⟨⟨107798889252, 107798889260⟩, ⟨104233346497, 111408236690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 267878400 270663680 ⟨⟨108849863301, 108849863308⟩, ⟨105276648915, 112466890491⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 259522560 270663680 t = true :=
  ⟨_, (join_su (m := 196608000) (by decide) (join_sr (m := 265093120) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 262307840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 195297280) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 267878400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 265093120) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 262307840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 197918720) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 267878400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
