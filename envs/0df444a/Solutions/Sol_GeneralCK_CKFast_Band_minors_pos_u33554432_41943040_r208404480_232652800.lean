-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r208404480_232652800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:50:32.170724+00:00
-- url     : https://prove2.me/submissions/f3153018-93f2-4c6a-9585-9ce4d10e35a6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 1/20]`, `ρ ∈ [159/640, 71/256]` by 14 cells of the computing
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
theorem cell0 : cellOK 33554432 35651584 208404480 214466560 ⟨⟨277194407819, 277194407835⟩, ⟨259654140630, 295416028126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 33554432 35651584 214466560 220528640 ⟨⟨282070248441, 282070248456⟩, ⟨264606212918, 300195567338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 35651584 37748736 208404480 214466560 ⟨⟨271361209870, 271361209888⟩, ⟨254278538796, 289101374448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 35651584 37748736 214466560 220528640 ⟨⟨276224957455, 276224957470⟩, ⟨259209108731, 293879668172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 33554432 35651584 220528640 232652800 ⟨⟨289239494190, 289239494210⟩, ⟨265870343203, 313746477675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 35651584 37748736 220528640 232652800 ⟨⟨283379289046, 283379289062⟩, ⟨260603882558, 307254379866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 37748736 39845888 208404480 214466560 ⟨⟨265765796224, 265765796240⟩, ⟨249116391037, 283050034122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 37748736 39845888 214466560 220528640 ⟨⟨270613981563, 270613981581⟩, ⟨254022846365, 287822634473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 39845888 41943040 208404480 214466560 ⟨⟨260391666138, 260391666153⟩, ⟨244153189558, 277243450825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 39845888 41943040 214466560 220528640 ⟨⟨265221246201, 265221246216⟩, ⟨249033254807, 282006437705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 37748736 39845888 220528640 226590720 ⟨⟨275388071817, 275388071831⟩, ⟨258855135623, 292521798233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 37748736 39845888 226590720 232652800 ⟨⟨280091065542, 280091065560⟩, ⟨263616188157, 297150566126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 39845888 41943040 220528640 226590720 ⟨⟨269978543267, 269978543285⟩, ⟨253841152449, 286697550171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 39845888 41943040 226590720 232652800 ⟨⟨274666420604, 274666420621⟩, ⟨258579673000, 291319701143⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 41943040 208404480 232652800 t = true :=
  ⟨_, (join_su (m := 37748736) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 35651584) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 214466560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 35651584) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 220528640) (by decide) (join_su (m := 39845888) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 214466560) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 39845888) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 226590720) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (159/640 : ℝ) (71/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  have e3 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
