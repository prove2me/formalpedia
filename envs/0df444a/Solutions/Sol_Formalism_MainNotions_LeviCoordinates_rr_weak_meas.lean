-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_weak_meas
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:52.612633+00:00
-- url     : https://prove2.me/submissions/2fbd2c65-fe04-49be-8789-6600637e3d93

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_exists_meas_rep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_ae_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [MeasurableMul₂ G] [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ]
    (h : rr_FD μ Γ D) (hR : rr_IsReg μ Γ D R) (x y : Lp ℂ 2 (μ.restrict D)) :
    StronglyMeasurable fun g => ⟪x, R g y⟫_ℂ := by
  obtain ⟨r₀, hr₀, hr₀rep⟩ := rr_exists_meas_rep h
  have hΦ : StronglyMeasurable
      (fun p : G × G => ⟪(x : G → ℂ) p.2, (y : G → ℂ) (r₀ (p.2 * p.1))⟫_ℂ) :=
    ((Lp.stronglyMeasurable x).comp_measurable measurable_snd).inner
      ((Lp.stronglyMeasurable y).comp_measurable (hr₀.comp (measurable_snd.mul measurable_fst)))
  have hEq : (fun g => ⟪x, R g y⟫_ℂ) =
      fun g => ∫ z, ⟪(x : G → ℂ) z, (y : G → ℂ) (r₀ (z * g))⟫_ℂ ∂(μ.restrict D) := by
    funext g
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hR g y, ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr₀rep g)] with z e1 e2
    simp only [e1, e2]
  rw [hEq]
  exact hΦ.integral_prod_right'
end Formalism.MainNotions.LeviCoordinates
