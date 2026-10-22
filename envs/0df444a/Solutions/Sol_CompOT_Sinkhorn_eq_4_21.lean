-- Prove2me | solution 1 for CompOT.Sinkhorn.eq_4_21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:26:08.582771+00:00
-- url     : https://prove2.me/submissions/b0303f82-4356-432d-b916-04c4d8a0441c

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

set_option autoImplicit false
open CompOT.Sinkhorn

theorem solution {n : ℕ} (hn : 0 < n) (u u' : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hu' : ∀ i, 0 < u' i) :
    hilbertMetric u u' = varNorm (fun i => Real.log (u i) - Real.log (u' i)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set f : Fin n → ℝ := fun i => Real.log (u i) - Real.log (u' i) with hf
  obtain ⟨i0, hi0⟩ := Finite.exists_max f
  obtain ⟨j0, hj0⟩ := Finite.exists_min f
  set r : Fin n → ℝ := fun i => u i / u' i with hr
  have hrpos : ∀ i, 0 < r i := fun i => div_pos (hu i) (hu' i)
  have hlogr : ∀ i, Real.log (r i) = f i := fun i => by
    simp only [hr, hf]; rw [Real.log_div (hu i).ne' (hu' i).ne']
  have hrle : ∀ i j, f i ≤ f j → r i ≤ r j := by
    intro i j h
    rw [← hlogr, ← hlogr] at h
    exact (Real.log_le_log_iff (hrpos i) (hrpos j)).1 h
  set g : Fin n → Fin n → ℝ := fun i j => u i * u' j / (u j * u' i) with hg
  have hgr : ∀ i j, g i j = r i / r j := by
    intro i j
    simp only [hg, hr]
    have := (hu i).ne'; have := (hu' i).ne'; have := (hu j).ne'; have := (hu' j).ne'
    field_simp
  have hsup : (⨆ i, ⨆ j, g i j) = g i0 j0 := by
    apply le_antisymm
    · refine ciSup_le (fun i => ciSup_le (fun j => ?_))
      rw [hgr, hgr]
      have h1 := hrle _ _ (hi0 i)
      have h2 := hrle _ _ (hj0 j)
      have := hrpos i; have := hrpos j; have := hrpos i0; have := hrpos j0
      rw [div_le_div_iff₀ (hrpos j) (hrpos j0)]
      nlinarith [mul_le_mul h1 h2 (hrpos j0).le (hrpos i0).le]
    · exact le_trans (le_ciSup (f := fun j => g i0 j) (Set.finite_range _).bddAbove j0)
        (le_ciSup (f := fun i => ⨆ j, g i j) (Set.finite_range _).bddAbove i0)
  have hmax : (⨆ i, f i) = f i0 :=
    le_antisymm (ciSup_le hi0) (le_ciSup (Set.finite_range f).bddAbove i0)
  have hmin : (⨅ i, f i) = f j0 :=
    le_antisymm (ciInf_le (Set.finite_range f).bddBelow j0) (le_ciInf hj0)
  unfold hilbertMetric varNorm
  rw [hsup, hmax, hmin]
  simp only [hg]
  rw [Real.log_div (mul_pos (hu i0) (hu' j0)).ne' (mul_pos (hu j0) (hu' i0)).ne',
    Real.log_mul (hu i0).ne' (hu' j0).ne', Real.log_mul (hu j0).ne' (hu' i0).ne']
  simp only [hf]
  ring
