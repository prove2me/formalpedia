-- Prove2me | solution 1 for BookProof.RitzPerturbation.minmaxGap_shiftOp
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:46:27.204666+00:00
-- url     : https://prove2.me/submissions/531c99bf-b588-49dc-b2e9-540e18582df3

import Definitions.Def_ChapterSirkRitzPerturbation

noncomputable section
open BookProof.RitzMinMax BookProof.RitzPerturbation BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
set_option autoImplicit false
set_option linter.unusedSectionVars false

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
private theorem ritzP_ne (T : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : (rayleighSetOn T S).Nonempty := by
  letI : Nontrivial S := Module.nontrivial_of_finrank_pos hS
  obtain ⟨x, hx⟩ := exists_norm_eq (E := S) (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨rayleighVal T (x : F), (x : F), x.property, hx, rfl⟩

private theorem ritzP_ne_congr (T T' : F →L[ℂ] F) {k : ℕ}
    (h : (minmaxSet T k).Nonempty) : (minmaxSet T' k).Nonempty := by
  obtain ⟨r, S, hd, hr⟩ := h
  exact ⟨rayleighSup T' S, S, hd, rfl⟩

private theorem ritzP_neIn_congr (T T' : F →L[ℂ] F) {W : Submodule ℂ F} {k : ℕ}
    (h : (minmaxSetIn T W k).Nonempty) : (minmaxSetIn T' W k).Nonempty := by
  obtain ⟨r, S, hSW, hd, hr⟩ := h
  exact ⟨rayleighSup T' S, S, hSW, hd, rfl⟩

private theorem ritzP_val (T T' : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    |rayleighVal T x - rayleighVal T' x| ≤ ‖T - T'‖ := by
  simpa only [rayleighVal, ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    using ritzR_unit (T - T') hx

private theorem ritzP_sup (T T' : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : rayleighSup T S ≤ rayleighSup T' S + ‖T - T'‖ := by
  apply csSup_le (ritzP_ne T hS)
  rintro r ⟨x, hxS, hx, rfl⟩
  have hm : rayleighVal T' x ≤ rayleighSup T' S :=
    le_csSup (ritzR_bddAbove T' S) ⟨x, hxS, hx, rfl⟩
  have hb := (abs_le.mp (ritzP_val T T' hx)).2
  linarith

private theorem ritzP_bddIn (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    BddBelow (minmaxSetIn T W k) := by
  refine ⟨-‖T‖, ?_⟩
  rintro r ⟨S, hSW, hd, rfl⟩
  exact ritzR_le_sup T S

private theorem ritzP_level (T T' : F →L[ℂ] F) (k : ℕ)
    (hne : (minmaxSet T' k).Nonempty) :
    minmaxLevel T k ≤ minmaxLevel T' k + ‖T - T'‖ := by
  have hh : minmaxLevel T k - ‖T - T'‖ ≤ minmaxLevel T' k := by
    apply le_csInf hne
    rintro r ⟨S, hd, rfl⟩
    have ha : minmaxLevel T k ≤ rayleighSup T S :=
      csInf_le (ritzR_bddBelow T k) ⟨S, hd, rfl⟩
    have hb := ritzP_sup T T' (show 0 < Module.finrank ℂ S by omega)
    linarith
  linarith

private theorem ritzP_levelIn (T T' : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (minmaxSetIn T' W k).Nonempty) :
    minmaxLevelIn T W k ≤ minmaxLevelIn T' W k + ‖T - T'‖ := by
  have hh : minmaxLevelIn T W k - ‖T - T'‖ ≤ minmaxLevelIn T' W k := by
    apply le_csInf hne
    rintro r ⟨S, hSW, hd, rfl⟩
    have ha : minmaxLevelIn T W k ≤ rayleighSup T S :=
      csInf_le (ritzP_bddIn T W k) ⟨S, hSW, hd, rfl⟩
    have hb := ritzP_sup T T' (show 0 < Module.finrank ℂ S by omega)
    linarith
  linarith

private theorem ritzP_absLevel (T T' : F →L[ℂ] F) (k : ℕ)
    (hne : (minmaxSet T k).Nonempty) :
    |minmaxLevel T k - minmaxLevel T' k| ≤ ‖T - T'‖ := by
  have ha := ritzP_level T T' k (ritzP_ne_congr T T' hne)
  have hb := ritzP_level T' T k hne
  rw [norm_sub_rev] at hb
  apply abs_le.mpr
  constructor <;> linarith

private theorem ritzP_absGap (T T' : F →L[ℂ] F)
    (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) :
    |minmaxGap T - minmaxGap T'| ≤ 2 * ‖T - T'‖ := by
  obtain ⟨ha0, hb0⟩ := abs_le.mp (ritzP_absLevel T T' 0 hne0)
  obtain ⟨ha1, hb1⟩ := abs_le.mp (ritzP_absLevel T T' 1 hne1)
  unfold minmaxGap
  apply abs_le.mpr
  constructor <;> linarith
private theorem ritzP_shiftVal (T : F →L[ℂ] F) (c : ℝ) {x : F} (hx : ‖x‖ = 1) :
    rayleighVal (shiftOp T c) x = rayleighVal T x + c := by
  simp [rayleighVal, shiftOp, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]

private theorem ritzP_shiftSup (T : F →L[ℂ] F) (c : ℝ) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) :
    rayleighSup (shiftOp T c) S = rayleighSup T S + c := by
  apply le_antisymm
  · apply csSup_le (ritzP_ne _ hS)
    rintro r ⟨x, hxS, hx, rfl⟩
    rw [ritzP_shiftVal T c hx]
    have hh : rayleighVal T x ≤ rayleighSup T S := le_csSup (ritzR_bddAbove T S) ⟨x, hxS, hx, rfl⟩
    linarith
  · have ha : rayleighSup T S ≤ rayleighSup (shiftOp T c) S - c := by
      apply csSup_le (ritzP_ne _ hS)
      rintro r ⟨x, hxS, hx, rfl⟩
      have hb : rayleighVal (shiftOp T c) x ≤ rayleighSup (shiftOp T c) S :=
        le_csSup (ritzR_bddAbove _ S) ⟨x, hxS, hx, rfl⟩
      rw [ritzP_shiftVal T c hx] at hb
      linarith
    linarith

private theorem ritzP_shiftLevel (T : F →L[ℂ] F) (c : ℝ) (k : ℕ)
    (hne : (minmaxSet T k).Nonempty) :
    minmaxLevel (shiftOp T c) k = minmaxLevel T k + c := by
  apply le_antisymm
  · have ha : minmaxLevel (shiftOp T c) k - c ≤ minmaxLevel T k := by
      apply le_csInf hne
      rintro r ⟨S, hd, rfl⟩
      have hb : minmaxLevel (shiftOp T c) k ≤ rayleighSup (shiftOp T c) S :=
        csInf_le (ritzR_bddBelow _ k) ⟨S, hd, rfl⟩
      rw [ritzP_shiftSup T c (show 0 < Module.finrank ℂ S by omega)] at hb
      linarith
    linarith
  · apply le_csInf (ritzP_ne_congr T (shiftOp T c) hne)
    rintro r ⟨S, hd, rfl⟩
    rw [ritzP_shiftSup T c (show 0 < Module.finrank ℂ S by omega)]
    have hh : minmaxLevel T k ≤ rayleighSup T S := csInf_le (ritzR_bddBelow T k) ⟨S, hd, rfl⟩
    linarith

theorem solution (T : F →L[ℂ] F) (c : ℝ)
    (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) :
    minmaxGap (shiftOp T c) = minmaxGap T := by
  unfold minmaxGap
  rw [ritzP_shiftLevel T c 1 hne1, ritzP_shiftLevel T c 0 hne0]
  ring

#print axioms solution
