-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.integrable_fY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:18.736304+00:00
-- url     : https://prove2.me/submissions/cb639452-ed74-4bb7-83f3-33cd49955202

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_continuous_fY
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_norm_fY_le
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_norm_W_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
private theorem ae_prod_restrict_snd_mem {ν μS : Measure G} [SFinite ν] [SFinite μS] {A : Set G} (hA : MeasurableSet A) :
    ∀ᵐ p ∂(ν.prod (μS.restrict A)), p.2 ∈ A := by
  rw [ae_iff]
  have hs : {p : G × G | ¬ p.2 ∈ A} = (Set.univ : Set G) ×ˢ Aᶜ := by
    ext p
    simp
  rw [hs, Measure.prod_prod, Measure.restrict_apply hA.compl, Set.compl_inter_self, measure_empty,
    mul_zero]
end Formalism.L2.S.Pv.EnergyAbs
end
end

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
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) : Integrable (fY σ w W e) (ν.prod (μS.restrict A)) := by
  have : IsFiniteMeasure (μS.restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hWc : Continuous W := hW.2.2.2.2.1
  have hWi : Integrable (fun z => ‖W z‖) ν := by
    refine ⟨hWc.norm.aestronglyMeasurable, ?_⟩
    simpa [HasFiniteIntegral, enorm_norm] using hW.2.2.2.2.2.2.1
  have hg : Integrable (fun p : G × G => ‖W p.1‖ * (‖e‖ * ‖w‖)) (ν.prod (μS.restrict A)) :=
    hWi.mul_prod (integrable_const (‖e‖ * ‖w‖))
  refine hg.mono' (continuous_fY hσ w hWc e).aestronglyMeasurable ?_
  filter_upwards [ae_prod_restrict_snd_mem (ν := ν) (μS := μS) hA] with p hp
  have h1 := norm_fY_le hσ w W e p
  rw [(norm_W_shift hW) hinv (hAS hp)] at h1
  exact h1.trans_eq (by ring)
end Formalism.L2.S.Pv.EnergyAbs
