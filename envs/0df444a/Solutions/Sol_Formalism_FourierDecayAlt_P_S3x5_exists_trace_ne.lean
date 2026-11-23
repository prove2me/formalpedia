-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.exists_trace_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:54.929859+00:00
-- url     : https://prove2.me/submissions/923b87d6-768e-46ad-b9fa-74e9a456f4ce

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_two_le_q
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_pm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]
variable [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2) :
    ∃ μ : K, μ + star μ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hq := two_le_q hc
  have h1 := card_pm_le (K := K) hq 1
  have h2 : Nat.card {x : K // x ^ q + 1 * x = 0} = Nat.card K := by
    apply Nat.card_congr
    exact Equiv.subtypeUnivEquiv (fun x => by have := hcon x; rw [hs] at this; rw [one_mul, add_comm]; exact this)
  rw [h2, Nat.card_eq_fintype_card, hc] at h1
  nlinarith
end Formalism.FourierDecayAlt.P.S3x5
