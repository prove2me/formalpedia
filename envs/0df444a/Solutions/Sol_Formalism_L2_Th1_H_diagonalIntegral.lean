-- Prove2me | solution 1 for Formalism.L2.Th1.H.diagonalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:36.779586+00:00
-- url     : https://prove2.me/submissions/a6cb8633-cd95-4037-a21b-30af2f3fc297

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionFiltrationStable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_DiagonalIntegral
import Theorems.Thm_Formalism_L2_Th1_H_continuous_altE
import Theorems.Thm_Formalism_L2_Th1_H_diag_expansion
import Theorems.Thm_Formalism_L2_Th1_H_norm_char
import Theorems.Thm_Formalism_L2_Th1_H_norm_diagCoef
import Theorems.Thm_Formalism_L2_Th1_H_characterIntegral
import Theorems.Thm_Formalism_L2_Th1_H_formNormEquiv
import Theorems.Thm_Formalism_L2_Th1_H_latticeGaussSummable
import Theorems.Thm_Formalism_L2_Th1_H_semicharacterBasic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : DiagIntegral := by
  classical
  intro V _ _ _ _ _ μ _ H Λ Λ₂ α hH hPos hL hS hS₂ hC hC₂ D' hD' hB y hy
  haveI : DiscreteTopology Λ := hL.1
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  set F : Λ → V → ℂ := fun x z => diagCoef H α y (x : V) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) with hF
  have hexp : ∀ z, α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) = ∑' x : Λ, F x z :=
    fun z => diag_expansion H hH α Λ y z
  simp only [hexp]
  have hαy : α y = 1 ∨ α y = -1 := hC₂.1 y hy
  obtain ⟨c, C, hc, hC', hcC⟩ := formNormEquiv V H hH hPos
  have hnorm : ∀ (x : Λ) (z : V), ‖F x z‖ = Real.exp (-(Real.pi / 2) * (H (y + (x : V)) (y + (x : V))).re) := by
    intro x z
    simp only [hF]
    rw [norm_mul, norm_char, mul_one, norm_diagCoef H α y x hαy (hC.1 x x.2)]
  set g : Λ → ℝ := fun x => Real.exp (-(Real.pi / 2) * (H (y + (x : V)) (y + (x : V))).re) with hg_def
  have hg : Summable g := by
    obtain ⟨u, hu, hub⟩ := latticeGaussSummable V Λ hL (Real.pi / 2 * c) ‖y‖ (by positivity)
    refine Summable.of_nonneg_of_le (fun x => (Real.exp_pos _).le) (fun x => ?_) hu
    have h1 := hub x (-y) (by simp)
    refine le_trans ?_ h1
    apply Real.exp_le_exp.mpr
    have h2 := (hcC (y + (x : V))).1
    have h3 : ‖(x : V) - -y‖ = ‖y + (x : V)‖ := by
      rw [sub_neg_eq_add, add_comm]
    rw [h3]
    nlinarith [Real.pi_pos]
  have hfin : μ D' < ⊤ := hB.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict D') := MeasureTheory.isFiniteMeasure_restrict.mpr hfin.ne
  have hcont : ∀ x : Λ, Continuous (F x) := by
    intro x
    simp only [hF]
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_altE H hH _))))
  have hint : ∀ x : Λ, Integrable (F x) (μ.restrict D') := by
    intro x
    exact (integrable_const (g x)).mono' (hcont x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => (hnorm x z).le)
  have hsum : Summable fun x => ∫ z, ‖F x z‖ ∂(μ.restrict D') := by
    have he : (fun x => ∫ z, ‖F x z‖ ∂(μ.restrict D')) = fun x => (μ D').toReal * g x := by
      funext x
      simp only [hnorm x]
      simp [hg_def, Measure.real]
    rw [he]
    exact hg.mul_left _
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have hd : diagCoef H α y (-y) = 1 := by
    have hneg : α (-y) = α y := (semicharacterBasic V H hH Λ₂ α hC₂).2.1 y hy
    have him : altE H y (-y) = 0 := by
      unfold altE
      rw [map_neg, Complex.neg_im, neg_eq_zero]
      have h := congrArg Complex.im (hH y y)
      rw [Complex.conj_im] at h
      linarith
    unfold diagCoef
    rw [hneg, him, add_neg_cancel]
    rcases hαy with h | h <;> simp [h]
  have hterm : ∀ x : Λ, ∫ z in D', F x z ∂μ = if (x : V) = -y then ((μ D').toReal : ℂ) else 0 := by
    intro x
    simp only [hF]
    rw [integral_const_mul]
    split_ifs with hx
    · rw [hx, add_neg_cancel, hd, one_mul]
      simp [altE, Measure.real]
    · have hne : y + (x : V) ≠ 0 := fun h => hx (eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h))
      have hy' : y ∈ dualLat H Λ₂ := by
        rw [hS₂]
        exact hy
      have hx' : (x : V) ∈ dualLat H Λ := by
        rw [hS]
        exact x.2
      have hmem : y + (x : V) ∈ dualLat H (Λ ⊓ Λ₂) := by
        refine add_mem ?_ ?_
        · exact fun w hw => hy' w (AddSubgroup.mem_inf.mp hw).2
        · exact fun w hw => hx' w (AddSubgroup.mem_inf.mp hw).1
      rw [characterIntegral V μ H hH hPos (Λ ⊓ Λ₂) D' hD' _ hmem hne, mul_zero]
  simp only [hterm]
  split_ifs with hyΛ
  · have hiff : ∀ x : Λ, ((x : V) = -y) ↔ x = ⟨-y, neg_mem hyΛ⟩ := fun x => by
      simp [Subtype.ext_iff]
    simp [hiff]
  · have hno : ∀ x : Λ, (x : V) ≠ -y := fun x h => hyΛ (by
      have hx2 := x.2
      rw [h] at hx2
      simpa using hx2)
    simp [hno]
end Formalism.L2.Th1.H
