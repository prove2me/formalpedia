-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.momFock_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:15:34.18717+00:00
-- url     : https://prove2.me/submissions/df96d805-4a23-41b5-ba23-9b6f6dca580b

import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_norm_bigState
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_bigState_mem_core
-- Generated from ChapterNavierStokesFockParcels.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.momFock_not_bounded
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]


theorem solution :
    ¬ ∃ C : ℝ, ∀ v : momFock.core,
      ‖((momFock.data.hFull v : momFock.core) : Lp ℂ 2 fockR)‖
        ≤ C * ‖((v : momFock.core) : Lp ℂ 2 fockR)‖ := by
  rintro ⟨C, hC⟩
  set K : ℝ := |C| + 1 with hKdef
  have hK : 0 ≤ K := by positivity
  set a : ℝ := (3 / 2) * K ^ 2
  let v : momFock.core := ⟨bigState K, bigState_mem_core hK⟩
  have h1 := hC v
  have hv : ((v : momFock.core) : Lp ℂ 2 fockR) = bigState K := rfl
  rw [hv, norm_bigState, mul_one] at h1
  have hlow : a ≤ ‖((momFock.data.hFull v : momFock.core) : Lp ℂ 2 fockR)‖ := by
    have ha : ‖(a : ℂ) • bigState K‖ = a := by
      rw [norm_smul, norm_bigState, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      positivity
    have h3 : (((momFock.data.hFull v : momFock.core) : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ)
        =ᵐ[fockR] fun x => (momFock.total x : ℂ) * (((v : momFock.core) : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ) x := by
      rw [LagSymbols.hFull_eq_mulD]
      exact mulD_coeFn fockR momFock.total_meas momFock.total_dom v
    rw [← ha]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul (a : ℂ) (bigState K), bigState_coeFn K, h3] with x hx1 hx2 hx3
    rw [hx1, hx3, Pi.smul_apply, hv, hx2]
    by_cases hS : x ∈ bigSet K
    · rw [Set.indicator_of_mem hS]
      obtain ⟨ξ, hξ, rfl⟩ := hS
      have hξ0 : ξ 0 ∈ Set.Icc K (K + 1) := hξ 0 (Set.mem_univ _)
      rw [momFock_total]
      simp only [parcelMk, Fin.sum_univ_one, smul_eq_mul, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      have : K ^ 2 ≤ (ξ 0) ^ 2 := by nlinarith [hξ0.1]
      erw [Fin.sum_univ_one]
      simp only [a]; nlinarith
    · rw [Set.indicator_of_notMem hS]; simp
  have : C < a := by
    simp only [a, hKdef]
    nlinarith [le_abs_self C, abs_nonneg C]
  linarith

