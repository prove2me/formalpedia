-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u224133120_225443840_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:48:33.561074+00:00
-- url     : https://prove2.me/submissions/1db71820-9b79-4b06-b810-a9b57f223659

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [171/640, 43/160]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 224133120 224460800 136970240 138362880 ⟨⟨48578265547, 48578265552⟩, ⟨47709403957, 49450475743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 224460800 224788480 136970240 138362880 ⟨⟨48470202825, 48470202832⟩, ⟨47602476163, 49341270886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 224133120 224460800 138362880 139755520 ⟨⟨49055330543, 49055330548⟩, ⟨48185448492, 49928562246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 224460800 224788480 138362880 139755520 ⟨⟨48946265604, 48946265609⟩, ⟨48077520055, 49818353606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 224788480 225116160 136970240 138362880 ⟨⟨48362308973, 48362308978⟩, ⟨47495714494, 49232237666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225116160 225443840 136970240 138362880 ⟨⟨48254583335, 48254583337⟩, ⟨47389118308, 49123375416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 224788480 225116160 138362880 139755520 ⟨⟨48837370743, 48837370748⟩, ⟨47969758948, 49708317816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 225116160 225443840 138362880 139755520 ⟨⟨48728645299, 48728645301⟩, ⟨47862164527, 49598454198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 224133120 224460800 139755520 141148160 ⟨⟨49532132038, 49532132044⟩, ⟨48661230158, 50406384614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224460800 224788480 139755520 141148160 ⟨⟨49422066510, 49422066516⟩, ⟨48552302698, 50295173827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 224460800 141148160 142540800 ⟨⟨50008670705, 50008670711⟩, ⟨49136749626, 50883943518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224460800 224788480 141148160 142540800 ⟨⟨49897606207, 49897606212⟩, ⟨49026824754, 50771732209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224788480 225116160 139755520 141148160 ⟨⟨49312172256, 49312172262⟩, ⟨48443543764, 50184137087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225116160 225443840 139755520 141148160 ⟨⟨49202448615, 49202448618⟩, ⟨48334952706, 50073273717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224788480 225116160 141148160 142540800 ⟨⟨49786714172, 49786714177⟩, ⟨48917069596, 50659696141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 225116160 225443840 141148160 142540800 ⟨⟨49675993936, 49675993939⟩, ⟨48807483501, 50547834629⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 224133120 225443840 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 224788480) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 224460800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 224460800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 225116160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 225116160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 224788480) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 224460800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 224460800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 225116160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 225116160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (171/640 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((224133120 : ℤ) : ℝ) / (D : ℝ)) = (171/640 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
