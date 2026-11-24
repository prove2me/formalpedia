-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:33.990848+00:00
-- url     : https://prove2.me/submissions/ef924368-6f23-46f8-99f6-f2c9bcd2d836

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_map
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_comp

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
theorem _root_.solution [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D)
    (hR : rr_IsReg μ Γ D R) (g k : G) : R (g * k) = R g ∘L R k := by
  ext F : 1
  refine Lp.ext ?_
  rw [ContinuousLinearMap.comp_apply]
  obtain ⟨hae, hmap⟩ := rr_map h g
  have h3 : (fun x => ((R k F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) (rr_rep (Γ : Set G) D (x * g)))
      =ᵐ[μ.restrict D] fun x =>
        (F : G → ℂ) (rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k)) :=
    ae_eq_comp (f := fun x => rr_rep (Γ : Set G) D (x * g))
      (g := ((R k F : Lp ℂ 2 (μ.restrict D)) : G → ℂ))
      (g' := fun y => (F : G → ℂ) (rr_rep (Γ : Set G) D (y * k))) hae (by rw [hmap]; exact hR k F)
  filter_upwards [hR (g * k) F, hR g (R k F), h3,
    ae_restrict_of_ae (s := D) (rr_rep_comp h g k)] with x e1 e2 e3 e4
  simp only [e1, e2, e3, e4]
end Formalism.MainNotions.LeviCoordinates
