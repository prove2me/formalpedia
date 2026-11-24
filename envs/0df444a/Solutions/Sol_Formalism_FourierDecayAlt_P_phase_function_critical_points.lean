-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_function_critical_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:53.094498+00:00
-- url     : https://prove2.me/submissions/c199cabf-9788-4624-8861-4eced2ffa13e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.PhaseFunctionCritical := by
  intro m D' hD
  constructor
  · intro x hx
    have hP0 : (∏ k, x k) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hx k)
    constructor
    · intro h
      have hxk : ∀ k, x k = D' / ∏ k, x k := by
        intro k
        have h1 := h k
        unfold dg0 at h1
        have h2 : D' / (∏ k, x k) / x k = 1 := by linear_combination -h1
        rw [div_eq_one_iff_eq (hx k)] at h2
        exact h2.symm
      refine ⟨D' / ∏ k, x k, ?_, funext hxk⟩
      have hprod : (∏ k, x k) = (D' / ∏ k, x k) ^ (m + 1) := by
        conv_lhs => rw [Finset.prod_congr rfl (fun k _ => hxk k)]
        simp [div_pow]
      rw [pow_succ, ← hprod]
      field_simp
    · rintro ⟨z, hz, rfl⟩ k
      have hz0 : z ≠ 0 := hx 0
      simp only [dg0, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hz]
      field_simp
      ring
  · intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      apply hD
      rw [← hz]; simp
    rw [← hz]
    simp [g0]; field_simp; ring
end Formalism.FourierDecayAlt.P
