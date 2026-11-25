-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.sumsq_div_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:18.18028+00:00
-- url     : https://prove2.me/submissions/ce9590a4-c65e-46a6-884f-22cc83cb15f7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerSum
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolner
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_sumsq_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {μS ν : Measure G} (hS : IsHaarSub S μS) [SFinite ν] {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W) (hW1 : ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S)
    (hfin : μS Ω < ⊤)
    (hint : Integrable (fun x : G × G × G => rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    (((∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS Ω).toReal : ℝ) : ℂ) =
      ∫ x, rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) := by
  have : SigmaFinite μS := hS.2.2.2.2.1
  by_cases hm : (μS Ω).toReal = 0
  · simp [rat, hm]
  · have hI := ‹Integrable (fun x : G × G × G => rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2)
      (ν.prod (ν.prod μS))›
    have hfI : Integrable (fun x : G × G × G => (cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2)
        (ν.prod (ν.prod μS)) := by
      refine (hI.smul (μS Ω).toReal).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.smul_apply, rat, smul_smul]
      congr 1
      first
        | rw [mul_div_assoc', mul_div_cancel_left₀ _ hm]
        | field_simp
    have hprod : ∫ x, (cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) =
        ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
      rw [integral_prod _ hfI]
      refine integral_congr_ae ?_
      filter_upwards [hfI.prod_right_ae] with z hz
      exact integral_prod _ hz
    have hrhs : ∫ x, rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) =
        ∫ x, ((μS Ω).toReal⁻¹ : ℝ) • ((cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2)
          ∂(ν.prod (ν.prod μS)) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [rat, smul_smul, div_eq_inv_mul]
    rw [hrhs, integral_smul, hprod, ← sumsq_eq hσ hw hS hWeq hτu hWc hW1 hΩm hΩS hfin,
      Complex.real_smul]
    push_cast
    ring
end Formalism.L2.S.Pv.EnergyAbs
