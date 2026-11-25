-- Prove2me | solution 1 for Formalism.DivisionValues.kappa_normalise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:48:03.157848+00:00
-- url     : https://prove2.me/submissions/99cc570b-b91e-4d41-a2b1-a069f93f6fe7

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Theorems.Thm_Formalism_DivisionValues_kappa_invariance
import Theorems.Thm_Formalism_DivisionValues_meanLog_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : KappaNormalise := by
  intro K _ _ _ _ D hD XE hXE κ hκ
  obtain ⟨h1, h2, -, h4, h5⟩ := kappa_invariance K D hD XE hXE (fun v => (κ v)⁻¹)
    (fun v => inv_pos.mpr (hκ v))
  rw [meanLog_inv] at h4 h5
  refine ⟨fun v => (h1 v).1, ?_, ?_, by simp [meanLog], ?_⟩
  · intro XS φ v ρ P h
    rw [h2 D XS φ v, h, mul_pow, mul_pow, one_pow, inv_pow]
    have : κ v ^ D ≠ 0 := pow_ne_zero _ (hκ v).ne'
    field_simp
  · intro XS φ v P h
    rw [h2 D XS φ v, h, one_pow, inv_pow]
    have : κ v ^ D ≠ 0 := pow_ne_zero _ (hκ v).ne'
    field_simp
  · intro R hR
    obtain ⟨-, e2, -, e4⟩ := h4 R hR
    refine ⟨by rw [e2]; ring, by rw [e4]; ring, by rw [e2, e4]; ring, ?_⟩
    intro n XN hXN φ hφ
    have e5 := h5 n XN hXN φ hφ
    exact ⟨by rw [e5]; ring, by rw [e2, e5]; ring⟩
end Formalism.DivisionValues
