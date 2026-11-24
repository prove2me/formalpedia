-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.prod_ne_zero_imp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:27.350629+00:00
-- url     : https://prove2.me/submissions/23652c37-ab17-41e9-a5d7-6e7a30739c4f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {m N : ℕ} (a b : Fin m → Fin N) (σ : Equiv.Perm (Fin m))
    (h : ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0) ≠ 0) : ∀ k, a (σ k) = b k := by
  intro k
  by_contra hk
  exact h (Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk))
end Formalism.FourierDecayAlt.P.SignAntidiagonal
