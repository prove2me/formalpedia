-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.integral_kG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:54.812906+00:00
-- url     : https://prove2.me/submissions/01c37d28-3282-4b88-980f-1df888f6b598

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_rankOne_eq_smulRightL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] {σ : G → (HH →L[ℂ] HH)}
    (hσ : IsUnitRep σ) {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {ν : Measure G} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (W' : G → V') (γ : G) (hi : Integrable (kG σ d w W W' γ) (μ.prod μ)) :
    ∫ q, kG σ d w W W' γ q ∂(μ.prod μ) = ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ := by
  obtain ⟨-, hmul, hunit, -⟩ := hσ
  obtain ⟨-, -, -, -, -, hrep, -⟩ := hW
  have hF : ∀ x : G, Integrable (fun g => ((d : ℂ) * ⟪σ g w, σ x w⟫_ℂ) • W g) μ ∧
      ∫ g, ((d : ℂ) * ⟪σ g w, σ x w⟫_ℂ) • W g ∂μ = W x := by
    intro x
    obtain ⟨hI, hE⟩ := hrep x
    have hin : ∀ g, ⟪σ g w, σ x w⟫_ℂ = conj ⟪w, σ (x⁻¹ * g) w⟫_ℂ := by
      intro g
      rw [inner_conj_symm, ← hunit x (σ (x⁻¹ * g) w) w, ← ContinuousLinearMap.mul_apply, ← hmul,
        mul_inv_cancel_left]
    have heq : (fun g => ((d : ℂ) * ⟪σ g w, σ x w⟫_ℂ) • W g)
        = fun g => (fun y => ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y)) (x⁻¹ * g) := by
      funext g
      simp only [mul_inv_cancel_left, hin]
    rw [heq]
    exact ⟨hI.comp_mul_left x⁻¹,
      (integral_mul_left_eq_self (fun y => ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y)) x⁻¹).trans hE⟩
  rw [integral_prod_symm _ hi]
  have hin : ∀ g' : G, ∫ g, kG σ d w W W' γ (g, g') ∂μ = rk1A (W (γ * g')) (W' g') := by
    intro g'
    have hk : (fun g => kG σ d w W W' γ (g, g'))
        = fun g => (ContinuousLinearMap.smulRightL ℂ V' V (innerSL ℂ (W' g')))
          (((d : ℂ) * ⟪σ g w, σ (γ * g') w⟫_ℂ) • W g) := by
      funext g
      simp only [kG, map_smul, ← rankOne_eq_smulRightL, hmul, ContinuousLinearMap.mul_apply]
    rw [hk, ContinuousLinearMap.integral_comp_comm _ (hF _).1, (hF _).2, ← rankOne_eq_smulRightL]
  simp_rw [hin]
  have h := integral_mul_left_eq_self (μ := μ) (fun x => rk1A (W x) (W' (γ⁻¹ * x))) γ
  simp only [inv_mul_cancel_left] at h
  exact h
end Formalism.L2.S.Pv.EnergyAbs
