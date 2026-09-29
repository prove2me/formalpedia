-- Prove2me | solution 1 for BookProof.RitzPerturbation.neg_norm_le_minmaxLevel
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:33:15.923689+00:00
-- url     : https://prove2.me/submissions/1fa39265-b58e-461e-bf9c-fbc651793ccb

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.neg_norm_le_minmaxLevel
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option autoImplicit false

private theorem ritzR_abs (T : F →L[ℂ] F) (x : F) :
    |rayleighVal T x| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc
    |rayleighVal T x| ≤ ‖x‖ * ‖T x‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm x (T x))
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg x)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

private theorem ritzR_unit (T : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    |rayleighVal T x| ≤ ‖T‖ := by
  simpa only [hx, one_pow, mul_one] using ritzR_abs T x

private theorem ritzR_bddAbove (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    BddAbove (rayleighSetOn T S) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨x, hxS, hx, rfl⟩
  exact (abs_le.mp (ritzR_unit T hx)).2

private theorem ritzR_sup_le (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    rayleighSup T S ≤ ‖T‖ := by
  by_cases hne : (rayleighSetOn T S).Nonempty
  · apply csSup_le hne
    rintro r ⟨x, hxS, hx, rfl⟩
    exact (abs_le.mp (ritzR_unit T hx)).2
  · have he := Set.not_nonempty_iff_eq_empty.mp hne
    simpa only [rayleighSup, he, Real.sSup_empty] using norm_nonneg T

private theorem ritzR_le_sup (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    -‖T‖ ≤ rayleighSup T S := by
  by_cases hne : (rayleighSetOn T S).Nonempty
  · obtain ⟨r, hr⟩ := hne
    obtain ⟨x, hxS, hx, rfl⟩ := hr
    exact (abs_le.mp (ritzR_unit T hx)).1.trans
      (le_csSup (ritzR_bddAbove T S) ⟨x, hxS, hx, rfl⟩)
  · have he := Set.not_nonempty_iff_eq_empty.mp hne
    simpa only [rayleighSup, he, Real.sSup_empty] using neg_nonpos.mpr (norm_nonneg T)

private theorem ritzR_bddBelow (T : F →L[ℂ] F) (k : ℕ) :
    BddBelow (minmaxSet T k) := by
  refine ⟨-‖T‖, ?_⟩
  rintro r ⟨S, hd, rfl⟩
  exact ritzR_le_sup T S

theorem solution (T : F →L[ℂ] F) (k : ℕ) (hne : (minmaxSet T k).Nonempty) :
    -‖T‖ ≤ minmaxLevel T k := by
  apply le_csInf hne
  rintro r ⟨S, hd, rfl⟩
  exact ritzR_le_sup T S

#print axioms solution
