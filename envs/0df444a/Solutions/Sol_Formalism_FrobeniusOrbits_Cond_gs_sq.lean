-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.gs_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:39:29.113666+00:00
-- url     : https://prove2.me/submissions/d32221ed-9ebf-42da-ba98-f17d2dedcfea

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_chi_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
variable {K : Type*} [Field K] [CharZero K]
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {x : K} (hx : IsPrimitiveRoot x p) :
    gs p hx.pow_eq_one ^ 2 = -(p : K) := by
  have h1 : chi p K ≠ 1 := by
    intro h
    have h0 := chi_neg_one (K := K) hp4
    have h2 : (1 : MulChar (ZMod p) K) (-1) = 1 := by
      exact MulChar.one_apply isUnit_one.neg
    rw [h, h2] at h0
    norm_num at h0
  have h2 : (chi p K).IsQuadratic := by
    exact (quadraticChar_isQuadratic (ZMod p)).comp _
  have h3 : (AddChar.zmodChar p hx.pow_eq_one).IsPrimitive := by
    exact AddChar.zmodChar_primitive_of_primitive_root p hx
  unfold gs
  rw [gaussSum_sq h1 h2 h3, chi_neg_one (K := K) hp4, ZMod.card]
  ring
end Formalism.FrobeniusOrbits.Cond
