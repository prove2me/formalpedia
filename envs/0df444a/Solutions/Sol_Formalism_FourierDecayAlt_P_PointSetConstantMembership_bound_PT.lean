-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PointSetConstantMembership.bound_PT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:19.243931+00:00
-- url     : https://prove2.me/submissions/98b27cf1-5141-46b5-acfd-766d38340253

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointSetConstantMembership
import Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_gram_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_norm_sq_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PointSetConstantMembership
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P.PointSetConstantMembership
theorem _root_.solution {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Kn : Pt E → Pt E → ℂ) (V : Pt E → H) {ρ : Type}
    (c : ρ → Pt E → ℂ) (P : Finset (Pt E)) (R : Finset ρ)
    (h : PSDOn P (fun p p' => Kn p p' - ∑ x ∈ R, conj (c x p) * c x p')) :
    ∑ x ∈ R, ‖∑ p ∈ P, c x p • V p‖ ^ 2 ≤ (gram Kn V P).re := by
  have h0 := gram_nonneg P _ V h.2
  have e : ∑ p ∈ P, ∑ p' ∈ P, (Kn p p' - ∑ x ∈ R, conj (c x p) * c x p') * ⟪V p, V p'⟫_ℂ
      = gram Kn V P - ((∑ x ∈ R, ‖∑ p ∈ P, c x p • V p‖ ^ 2 : ℝ) : ℂ) := by
    unfold gram
    rw [Complex.ofReal_sum]
    simp_rw [norm_sq_comb]
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [sub_mul, Finset.sum_mul]
  rw [e, Complex.sub_re, Complex.ofReal_re] at h0
  linarith
end Formalism.FourierDecayAlt.P.PointSetConstantMembership
