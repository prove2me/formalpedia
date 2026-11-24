-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.top_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:49.062897+00:00
-- url     : https://prove2.me/submissions/8a5bc359-44cb-4ebb-abe3-25c4a7e84227

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {m N : ℕ} (a : Fin m → Fin N) (ha : Function.Injective a) :
    (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if a (σ k) = a k then (1 : ℂ) else 0)) = 1 := by
  rw [Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra H
      exact hσ (Equiv.ext fun l => by simpa using not_not.mp (fun h => H ⟨l, h⟩))
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (ha.ne hk)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.SignAntidiagonal
