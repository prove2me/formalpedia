-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.sum_ldeg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:35.957989+00:00
-- url     : https://prove2.me/submissions/3bb7035f-4cc7-41eb-be11-86bcf066991f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) (hp : 0 < p) (ζ : D.EM) (h : D.GoodE p ζ) :
    ∑ i : D.ML, ldeg ζ i ≤ D.totDeg := by
  obtain ⟨_, _, hb, ht, _⟩ := h
  unfold totDeg
  simp only [Fintype.sum_sum_type, dO, Sum.elim_inl, Sum.elim_inr]
  have e1 : ∑ b : D.Lb, ldeg ζ (Sum.inl b) = ∑ b : D.Lb, D.dB b :=
    Finset.sum_congr rfl (fun b _ => hb b)
  have e2 : ∀ t : D.Tau, ldeg ζ (Sum.inr (Sum.inl t)) + (ldeg ζ (Sum.inr (Sum.inr (Sum.inl t)))
      + ldeg ζ (Sum.inr (Sum.inr (Sum.inr t)))) ≤ D.dT t := by
    intro t
    have h1 := ht t
    have hP : 0 < D.P p t := by
      show 0 < p ^ D.g t
      exact Nat.pow_pos hp
    have h2 : ldeg ζ (D.mw t) ≤ D.P p t * ldeg ζ (D.mw t) := Nat.le_mul_of_pos_left _ hP
    show ldeg ζ (D.mlab t) + (ldeg ζ (D.mw t) + ldeg ζ (D.mtp t)) ≤ D.dT t
    omega
  rw [e1]
  apply Nat.add_le_add_left
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun t _ => e2 t)
end Formalism.MainNotions.PlaneGram.TwistData
