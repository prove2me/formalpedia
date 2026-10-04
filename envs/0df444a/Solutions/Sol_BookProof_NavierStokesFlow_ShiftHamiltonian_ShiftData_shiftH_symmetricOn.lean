-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:00:04.601573+00:00
-- url     : https://prove2.me/submissions/62145040-e1a2-4a0f-b784-4ca3ab9263e8

import Mathlib
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian

variable {ι : Type*} (S : ShiftData ι)

open scoped ENNReal

open LpNat BookProof.FarisLavine IkebeKato

theorem f4a591c6_left_pt (X Y : ι → ℂ) (β : ι) :
    (starRingEnd ℂ) (S.hFun X β) * Y β
      = -Complex.I * S.hop (S.crossA X Y) β + Complex.I * S.crossB X Y β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    simp only [ShiftData.hFun, ShiftData.hop_shift, ShiftData.crossA, ShiftData.crossB, map_mul,
      map_sub, Complex.conj_I, Complex.conj_ofReal]
    ring
  · simp only [ShiftData.hFun, ShiftData.hop_eq_zero S _ hb, ShiftData.crossB, map_mul, map_sub,
      map_zero, Complex.conj_I, Complex.conj_ofReal]
    ring

theorem f4a591c6_right_pt (X Y : ι → ℂ) (β : ι) :
    (starRingEnd ℂ) (X β) * S.hFun Y β
      = Complex.I * S.hop (S.crossB X Y) β - Complex.I * S.crossA X Y β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    simp only [ShiftData.hFun, ShiftData.hop_shift, ShiftData.crossA, ShiftData.crossB]
    ring
  · simp only [ShiftData.hFun, ShiftData.hop_eq_zero S _ hb, ShiftData.crossA]
    ring

theorem f4a591c6_summable_crossA (x y : maxDom S.sym) :
    Summable (S.crossA ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ)) := by
  have hYs : Summable fun β => ‖((y : L2I ι) : ι → ℂ) (S.shift β)‖ ^ 2 :=
    (ShiftData.hasSum_normSq (y : L2I ι)).summable.comp_injective S.shift_injective
  refine Summable.of_norm_bounded (((S.summable_ampSeq_sq x).add hYs).mul_left (1 / 2))
    (fun β => ?_)
  have h : ‖S.crossA ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ) β‖
      = S.ampSeq ((x : L2I ι) : ι → ℂ) β * ‖((y : L2I ι) : ι → ℂ) (S.shift β)‖ := by
    simp only [ShiftData.crossA, ShiftData.ampSeq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (S.amp_nonneg β), Complex.norm_conj]
  rw [h]
  nlinarith [sq_nonneg (S.ampSeq ((x : L2I ι) : ι → ℂ) β - ‖((y : L2I ι) : ι → ℂ) (S.shift β)‖)]

theorem f4a591c6_summable_crossB (x y : maxDom S.sym) :
    Summable (S.crossB ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ)) := by
  have hXs : Summable fun β => ‖((x : L2I ι) : ι → ℂ) (S.shift β)‖ ^ 2 :=
    (ShiftData.hasSum_normSq (x : L2I ι)).summable.comp_injective S.shift_injective
  refine Summable.of_norm_bounded (((S.summable_ampSeq_sq y).add hXs).mul_left (1 / 2))
    (fun β => ?_)
  have h : ‖S.crossB ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ) β‖
      = S.ampSeq ((y : L2I ι) : ι → ℂ) β * ‖((x : L2I ι) : ι → ℂ) (S.shift β)‖ := by
    simp only [ShiftData.crossB, ShiftData.ampSeq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (S.amp_nonneg β), Complex.norm_conj]
    ring
  rw [h]
  nlinarith [sq_nonneg (S.ampSeq ((y : L2I ι) : ι → ℂ) β - ‖((x : L2I ι) : ι → ℂ) (S.shift β)‖)]

open BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData in
theorem solution {ι : Type*} (S : ShiftData ι) : SymmetricOn (maxDom S.sym) (shiftH S) := by
  intro x y
  have hA := f4a591c6_summable_crossA S x y
  have hB := f4a591c6_summable_crossB S x y
  have h1 : HasSum (fun β => (inner ℂ (((shiftH S x : L2I ι)) β) (((y : L2I ι)) β) : ℂ))
      (-Complex.I * ∑' β, S.crossA ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ) β
        + Complex.I * ∑' β, S.crossB ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ) β) := by
    have hfun : (fun β => (inner ℂ (((shiftH S x : L2I ι)) β) (((y : L2I ι)) β) : ℂ))
        = fun β => -Complex.I * S.hop (S.crossA ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ)) β
          + Complex.I * S.crossB ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ) β := by
      funext β
      rw [RCLike.inner_apply']
      exact f4a591c6_left_pt S _ _ β
    rw [hfun]
    exact ((((ShiftData.hasSum_hop_iff S).mpr hA.hasSum).mul_left _).add (hB.hasSum.mul_left _))
  have h2 : HasSum (fun β => (inner ℂ (((x : L2I ι)) β) (((shiftH S y : L2I ι)) β) : ℂ))
      (Complex.I * ∑' β, S.crossB ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ) β
        - Complex.I * ∑' β, S.crossA ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ) β) := by
    have hfun : (fun β => (inner ℂ (((x : L2I ι)) β) (((shiftH S y : L2I ι)) β) : ℂ))
        = fun β => Complex.I * S.hop (S.crossB ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ)) β
          - Complex.I * S.crossA ((x : L2I ι) : ι → ℂ) ((y : L2I ι) : ι → ℂ) β := by
      funext β
      rw [RCLike.inner_apply']
      exact f4a591c6_right_pt S _ _ β
    rw [hfun]
    exact ((((ShiftData.hasSum_hop_iff S).mpr hB.hasSum).mul_left _).sub (hA.hasSum.mul_left _))
  rw [(lp.hasSum_inner _ _).unique h1, (lp.hasSum_inner _ _).unique h2]
  ring
