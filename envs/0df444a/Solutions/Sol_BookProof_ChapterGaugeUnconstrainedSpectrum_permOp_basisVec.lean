-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_basisVec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:24:12.98289+00:00
-- url     : https://prove2.me/submissions/98ed7dfd-ac07-448a-aabe-a45b8ade081e

import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterE4
-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_basisVec
open BookProof.ChapterE4
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}
open BookProof.ChapterGaugeUnconstrainedSpectrum in
theorem h44g_perm_basis {X : Type*} [DecidableEq X] (σ : Equiv.Perm X) (y : X) :
    permOp σ (basisVec y) = basisVec (σ y) := by
  funext x
  change basisVec y (σ.symm x) = basisVec (σ y) x
  simp only [BookProof.ChapterGaugeUnconstrainedSpectrum.basisVec]
  by_cases h : x = σ y
  · subst h; simp
  · rw [if_neg, if_neg h]; intro h'; apply h; rw [← h']; simp

open BookProof.ChapterGaugeUnconstrainedSpectrum in
theorem h44g_diag_basis {X : Type*} [DecidableEq X] (d : X → ℂ) (y : X) :
    diagOp d (basisVec y) = d y • basisVec y := by
  funext x
  change d x * basisVec y x = d y * basisVec y x
  simp only [BookProof.ChapterGaugeUnconstrainedSpectrum.basisVec]
  by_cases h : x = y
  · subst h; rfl
  · simp [h]

open BookProof.ChapterGaugeUnconstrainedSpectrum in
theorem h44g_eig {X : Type*} [DecidableEq X] {T : Op X} (hT : IsFunctionOfSpectrum T) (y : X) :
    ∃ c : ℂ, T (basisVec y) = c • basisVec y := by
  obtain ⟨d, rfl⟩ := hT
  exact ⟨d y, h44g_diag_basis d y⟩

open BookProof.ChapterGaugeUnconstrainedSpectrum in
theorem h44g_perm_iff {X : Type*} (σ : Equiv.Perm X) :
    IsFunctionOfSpectrum (permOp σ) ↔ σ = 1 := by
  classical
  constructor
  · rintro ⟨d, hd⟩
    ext y
    by_contra hne
    have h1 := h44g_perm_basis σ y
    rw [hd, h44g_diag_basis] at h1
    have h2 := congrFun h1 (σ y)
    simp only [BookProof.ChapterGaugeUnconstrainedSpectrum.basisVec, Pi.smul_apply, smul_eq_mul, if_pos rfl] at h2
    rw [if_neg (by simpa using hne)] at h2
    simp at h2
  · rintro rfl
    refine ⟨fun _ => 1, ?_⟩
    ext f x
    change f ((1 : Equiv.Perm X).symm x) = 1 * f x
    rw [one_mul]; rfl

open BookProof.ChapterGaugeUnconstrainedSpectrum in
theorem h44g_of_inj {G X : Type*} [Group G] {ρ : G →* Equiv.Perm X} (hρ : Function.Injective ρ) :
    IsUnconstrainedGaugeFixing (fun g => permOp (ρ g)) := by
  intro g hg h
  rw [h44g_perm_iff] at h
  exact hg (hρ (by rw [h, map_one]))

open BookProof.ChapterGaugeUnconstrainedSpectrum in
theorem h44g_univ {G X : Type*} [Group G] {U : G → Op X}
    (hU : IsUnconstrainedGaugeFixing U) (hU1 : U 1 = LinearMap.id) :
    constrainedSpectrum U = Set.univ := by
  classical
  ext x
  simp only [Set.mem_univ, iff_true]
  intro g d hd
  by_cases hg : g = 1
  · subst hg
    rw [hU1] at hd
    have h := congrFun (congrArg (fun T => T (basisVec x)) hd) x
    simp only [LinearMap.id_apply] at h
    rw [h44g_diag_basis] at h
    simpa [BookProof.ChapterGaugeUnconstrainedSpectrum.basisVec] using h.symm
  · exact absurd ⟨d, hd⟩ (hU g hg)

open BookProof.ChapterGaugeUnconstrainedSpectrum in
theorem h44g_shift_inj : Function.Injective shiftPerm := by
  intro m n h
  have := congrArg (fun σ : Equiv.Perm ℤ => σ 0) h
  simp [shiftPerm] at this
  exact this

open BookProof.ChapterGaugeUnconstrainedSpectrum in
theorem h44g_shift_unc :
    IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m)) :=
  h44g_of_inj h44g_shift_inj

open BookProof.ChapterGaugeUnconstrainedSpectrum in
theorem h44g_perm_one {X : Type*} : permOp (1 : Equiv.Perm X) = LinearMap.id := by
  ext f x; rfl

theorem solution [DecidableEq X] (σ : Equiv.Perm X) (y : X) :
    permOp σ (basisVec y) = basisVec (σ y) := by
  exact h44g_perm_basis σ y

