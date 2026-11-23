-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FinitePointSets.rows_le_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:44.997474+00:00
-- url     : https://prove2.me/submissions/c3d58e83-ea06-4d8f-b853-5bd7a59778f6

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinitePointSets
import Theorems.Thm_Formalism_FourierDecayAlt_P_FinitePointSets_form_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_FinitePointSets_norm_sq_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FinitePointSets
open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P.FinitePointSets
theorem _root_.solution {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (k : α → α → ℂ) (V : α → H) (c : ℕ → α → ℂ) (R : Finset ℕ)
    (h : PSDOn Y (fun p q => k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q))) :
    ∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫).re := by
  have h0 := form_nonneg Y _ h V
  have e : ∑ p ∈ Y, ∑ q ∈ Y, (k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q)) * ⟪V q, V p⟫
      = ∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫
        - ((∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [norm_sq_comb]
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [sub_mul, Finset.sum_mul]
  rw [e, Complex.sub_re, Complex.ofReal_re] at h0
  linarith
end Formalism.FourierDecayAlt.P.FinitePointSets
