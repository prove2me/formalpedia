-- Prove2me | solution 1 for Formalism.DimensionVariation.fjProd_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:38.023383+00:00
-- url     : https://prove2.me/submissions/03c14491-ab00-4be0-883e-bfbd2ae1f8c8

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_fjOrth
import Theorems.Thm_Formalism_DimensionVariation_fjProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution {κ : Type} [Fintype κ] (N : ℕ) (a b : κ → ℕ) (hab : a ≠ b) :
    ∫ u : κ → ℂ, fjChiP N u * (mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ)) = 0 := by
  have h : ∀ u : κ → ℂ, fjChiP N u *
      (mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ)) =
      ∏ x, (fjChi N (u x) * fjW (a x) (b x) (u x)) := by
    intro u
    rw [fjProd, fjChiP, ← Finset.prod_mul_distrib]
  simp_rw [h]
  rw [show (∫ u : κ → ℂ, ∏ x, (fjChi N (u x) * fjW (a x) (b x) (u x))) =
      ∏ x, ∫ z : ℂ, fjChi N z * fjW (a x) (b x) z from
    integral_fintype_prod_volume_eq_prod
      (fun x (z : ℂ) => fjChi N z * fjW (a x) (b x) z)]
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hab
  exact Finset.prod_eq_zero (Finset.mem_univ x)
    (fjOrth N _ _ hx)
end Formalism.DimensionVariation
