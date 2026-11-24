-- Prove2me | solution 1 for Formalism.L2.Th1.F.eisensteinS2LimitFormula_of_hkLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:24:42.329922+00:00
-- url     : https://prove2.me/submissions/e39babe7-afe7-4ddc-9aa8-6201e3ff4202

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit
import Theorems.Thm_Formalism_L2_Th1_F_Hk4_hk_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_area_eq
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_area_pos
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_det_ne_zero
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_div_im
import Theorems.Thm_Formalism_L2_Th1_F_etaEisenstein
import Theorems.Thm_Formalism_L2_Th1_F_etaSplit
import Theorems.Thm_P2M_Formalism_L2_Th1_F_PeriodAreaSignLemmas____ne_zero_77e9ed9e316c


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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Hk4 PeriodAreaSignLemmas
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : HkLimit) : EisensteinS2LimitFormula := by
  intro L
  set u := L.ω₁ with hu_def
  have hu : u ≠ 0 := ω₁_ne_zero L
  set τ := L.ω₂ / u with hτ_def
  have hN : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have him : τ.im = det L / Complex.normSq u := div_im L
  have hτ : τ.im ≠ 0 := by
    rw [him]; exact div_ne_zero (det_ne_zero L) hN.ne'
  have hlin : ∀ m n : ℤ, (m : ℂ) * u + (n : ℂ) * L.ω₂ = u * ((m : ℂ) + (n : ℂ) * τ) := by
    intro m n
    rw [hτ_def]; field_simp
  have hsum : ∀ s : ℝ, ∑' ω : L.lattice, ((ω : ℂ) ^ 2)⁻¹ * ((‖(ω : ℂ)‖ ^ (-(2 * s)) : ℝ) : ℂ)
      = (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ) * ∑' p : ℤ × ℤ, hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ) := by
    intro s
    rw [← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    rw [← hk_mul, ← hlin]
    simp only [LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, hk]
    rfl
  simp only [hsum]
  have hc : Tendsto (fun s : ℝ => (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((u ^ 2)⁻¹ * 1)) := by
    refine Tendsto.const_mul _ ?_
    have h1 : ContinuousAt (fun s : ℝ => ‖u‖ ^ (-(2 * s))) 0 := by
      have : ContinuousAt (fun x : ℝ => ‖u‖ ^ x) (-(2 * (0 : ℝ))) :=
        Real.continuousAt_const_rpow (norm_ne_zero_iff.mpr hu)
      exact ContinuousAt.comp (f := fun s : ℝ => -(2 * s)) this (by fun_prop)
    have h2 : Tendsto (fun s : ℝ => ‖u‖ ^ (-(2 * s))) (𝓝[>] 0) (𝓝 1) := by
      have := h1.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have := (Complex.continuous_ofReal.tendsto 1).comp h2
    simpa [Function.comp_def] using this
  have hmain := hc.mul (h τ hτ)
  convert hmain using 2

  have hE := (etaEisenstein L).1
  have hSp := etaSplit L u
  have hT : ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2
      = (u ^ 2)⁻¹ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2 := by
    simp_rw [← tsum_mul_left]
    refine tsum_congr fun n => tsum_congr fun m => ?_
    rw [hlin, mul_pow]
    field_simp
  rw [hT, ← hu_def] at hE
  have hA : (area L : ℂ) ≠ 0 := by exact_mod_cast (area_pos L).ne'
  have habs : |τ.im| = area L / Complex.normSq u := by
    rw [him, abs_div, abs_of_pos hN, area_eq]
  have hNc : ((Complex.normSq u : ℝ) : ℂ) = u * conj u := (Complex.mul_conj u).symm
  have hcu : conj u ≠ 0 := by simpa using hu
  rw [habs]
  push_cast
  rw [hNc]
  rw [hE] at hSp
  have hs : s2 L = (u * ((u ^ 2)⁻¹ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2)
      - ((Real.pi : ℂ) / (area L : ℂ)) * conj u) / u := by
    rw [hSp]; field_simp; ring
  rw [hs]
  generalize (∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2) = T
  field_simp
end Formalism.L2.Th1.F
