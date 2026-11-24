-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EntryMinorBounds.minor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:04.315565+00:00
-- url     : https://prove2.me/submissions/7c80af32-6723-4396-8e0d-eaaf41478d3b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_det_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_entry_le_mx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.EntryMinorBounds
namespace Formalism.FourierDecayAlt.P.EntryMinorBounds
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (I J : Finset (Fin m)) :
    ‖C2.minorS M I J‖ ≤ (Nat.factorial m : ℝ) * (1 + C2.mx M) ^ m := by
  have hmx : 0 ≤ C2.mx M := norm_nonneg _
  unfold C2.minorS
  split_ifs with h
  · have hcard : I.card ≤ m := by simpa using Finset.card_le_univ I
    refine (det_norm_le _ (fun _ => C2.mx M) (fun a b => entry_le_mx M _ _)).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hcard
    · calc C2.mx M ^ I.card ≤ (1 + C2.mx M) ^ I.card := pow_le_pow_left₀ hmx (by linarith) _
        _ ≤ (1 + C2.mx M) ^ m := pow_le_pow_right₀ (by linarith) hcard
    · positivity
    · positivity
  · rw [norm_zero]; positivity
end Formalism.FourierDecayAlt.P.EntryMinorBounds
