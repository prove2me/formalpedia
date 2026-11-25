-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.sigma_Yop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:55:19.776522+00:00
-- url     : https://prove2.me/submissions/918cf59e-1e3d-43e4-9d16-f2cf2fddedb8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEquiv
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Yop_apply_integral
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_prod_restrict_translate
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_integrable_fY
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_rep_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν] {S : Set G}
    (hS : IsHaarSub S μS) {d : ℝ} {w : HH} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S) (hAf : μS A < ⊤)
    {s0 : G} (hs0 : s0 ∈ S) (e : V) :
    σ s0⁻¹ (Yop μS ν σ w W A e) =
      Yop μS ν σ w W ((fun v => v * s0⁻¹) ⁻¹' A) (ContinuousLinearMap.adjoint (τ s0) e) := by
  obtain ⟨-, -, hmulS, hinvS, hsig, -, -, -, -, hright, -⟩ := hS
  have : SFinite μS := by have := hsig; infer_instance
  have hmap : μS.map (fun x => x * s0⁻¹) = μS := hright _ (hinvS s0 hs0)
  have hA'm : MeasurableSet ((fun v => v * s0⁻¹) ⁻¹' A) := measurable_mul_const s0⁻¹ hA
  have hA'S : (fun v => v * s0⁻¹) ⁻¹' A ⊆ S := by
    intro v hv
    have h1 := hmulS _ (hAS hv) s0 hs0
    simpa [mul_assoc] using h1
  have hA'f : μS ((fun v => v * s0⁻¹) ⁻¹' A) < ⊤ := by
    rw [← Measure.map_apply (measurable_mul_const s0⁻¹) hA, hmap]
    exact hAf
  have hemb : MeasurableEmbedding (Prod.map id (fun v : G => v * s0⁻¹)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl G) (MeasurableEquiv.mulRight s0⁻¹)).measurableEmbedding

  rw [Yop_apply_integral hσ hW hinvS hA hAS hAf, Yop_apply_integral hσ hW hinvS hA'm hA'S hA'f,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_fY hσ hW hinvS hA hAS hAf e),
    prod_restrict_translate ν hmap A, hemb.integral_map]
  congr 1
  funext p
  simp only [fY, Prod.map, id, map_smul]
  have hq : (p.2 * s0⁻¹)⁻¹ * p.1 = s0 * (p.2⁻¹ * p.1) := by group
  rw [hq, rep_mul_apply hσ, inv_mul_cancel_left, hW.2.2.2.1 s0 hs0,
    ContinuousLinearMap.adjoint_inner_right]
end Formalism.L2.S.Pv.EnergyAbs
