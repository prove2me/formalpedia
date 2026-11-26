-- Prove2me | solution 1 for GRH.dirichlet_grid_of_dyadic_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:45:53.344907+00:00
-- url     : https://prove2.me/submissions/8f6a55cb-f118-43a3-ba7e-ec86807b0eb2

import Definitions.Def_GRH_DyadicCharacterGrid
import Theorems.Thm_GRH_dirichlet_rectangle_nonzero_iff_finite_grid
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

open GRH.DyadicCharacterGrid GRH.DirichletGrid Set Complex

/-- It suffices to test the nested rectangles of heights 1, 2, 4 and so on.
Every intermediate rectangle lies in the first dyadic rectangle above it. -/
theorem solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ≠1)
    (b : ℝ) (hb : (1/2:ℝ)<b) (hb1 : b≤1) :
    (∀ h : ℕ, ∃ m : ℕ, Passes χ (left b h) b ((h:ℝ)+1) m) ↔
      ∀ k : ℕ, ∃ m : ℕ, Passes χ (left b (index k)) b ((index k:ℝ)+1) m := by
  refine ⟨fun all k => all (index k),?_⟩
  intro dy h
  let k := Nat.clog 2 (h+1)
  have above : h ≤ index k := by
    have e := Nat.le_pow_clog (by decide : 1<2) (h+1)
    change h≤2^Nat.clog 2 (h+1)-1
    omega
  have bottom (n : ℕ) : (1/2:ℝ) ≤ left b n := le_add_of_nonneg_right
    (div_nonneg (sub_nonneg.mpr hb.le) (by positivity))
  have top (n : ℕ) : left b n≤b := by
    have e := div_le_self (sub_nonneg.mpr hb.le) (show 1≤(n:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    dsimp [left];linarith
  have mono : (h:ℝ)+1≤(index k:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ above
  have widen : left b (index k)≤left b h := add_le_add le_rfl
    (div_le_div_of_nonneg_left (sub_nonneg.mpr hb.le) (by positivity) mono)
  have big := (GRH.dirichlet_rectangle_nonzero_iff_finite_grid q χ hχ (left b (index k)) b _
    (bottom _) (top _) hb1 (by positivity)).2 (dy k)
  apply (GRH.dirichlet_rectangle_nonzero_iff_finite_grid q χ hχ (left b h) b _
    (bottom _) (top _) hb1 (by positivity)).1
  intro z hz
  exact big z ⟨⟨widen.trans hz.1.1,hz.1.2⟩,⟨(neg_le_neg mono).trans hz.2.1,hz.2.2.trans mono⟩⟩
