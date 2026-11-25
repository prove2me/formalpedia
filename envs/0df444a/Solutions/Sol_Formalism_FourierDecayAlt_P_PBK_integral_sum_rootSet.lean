-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.integral_sum_rootSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:46:49.544149+00:00
-- url     : https://prove2.me/submissions/a34b1206-70a9-4f03-a99d-32c0040897ed

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_sum_rootSet_eq_range
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_rootBranch
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_A_disjoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_A_union
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_measurableSet_A


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (s : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (F : ℂ → E)
    (hF : Integrable (fun z => ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z)) :
    Integrable (fun c => ∑ z ∈ G.rootSet s (u * c), F z) ∧
      ∫ c, ∑ z ∈ G.rootSet s (u * c), F z = ∫ z, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
  have hae : ∀ᵐ c : ℂ, c ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)

  have hsum : (fun c => ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k (u * c))) =ᵐ[volume]
      fun c => ∑ z ∈ G.rootSet s (u * c), F z := by
    filter_upwards [hae] with c hc
    rw [Formalism.FourierDecayAlt.P.PBK.sum_rootSet_eq_range hs (mul_ne_zero hu hc)]
  have hbr := fun k => Formalism.FourierDecayAlt.P.PBK.rootBranch s k hs u hu F hF
  refine ⟨(integrable_finsetSum _ fun k _ => (hbr k).1).congr hsum, ?_⟩
  calc ∫ c, ∑ z ∈ G.rootSet s (u * c), F z
      = ∫ c, ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k (u * c)) := integral_congr_ae hsum.symm
    _ = ∑ k ∈ Finset.range s, ∫ c, F (NthRootMeasurability.R s k (u * c)) :=
        integral_finsetSum _ fun k _ => (hbr k).1
    _ = ∑ k ∈ Finset.range s, ∫ z in NthRootMeasurability.A s k, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z :=
        Finset.sum_congr rfl fun k _ => (hbr k).2
    _ = ∫ z in ⋃ k ∈ Finset.range s, NthRootMeasurability.A s k, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z :=
        (integral_biUnion_finset _ (fun k _ => Formalism.FourierDecayAlt.P.NthRootMeasurability.measurableSet_A s k)
          (Formalism.FourierDecayAlt.P.NthRootMeasurability.A_disjoint s hs) (fun k _ => hF.integrableOn)).symm
    _ = ∫ z in ({0}ᶜ : Set ℂ), ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
        rw [Formalism.FourierDecayAlt.P.NthRootMeasurability.A_union s hs]
    _ = ∫ z, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
        rw [MeasureTheory.restrict_compl_singleton]
end Formalism.FourierDecayAlt.P.PBK
