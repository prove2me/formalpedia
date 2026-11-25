-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhFinalArith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:30.783984+00:00
-- url     : https://prove2.me/submissions/977616b3-48f5-422b-b815-d6ebc7b9a6e1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (S1 S2 S3 S4 P1 P3 P4 A1 A2 A3 A4 E0 Eγ g2 I3 I4 X F G Hc H e8 : ℝ)
    (t1 : S1 + S2 + S3 + S4 ≤ P1 - A1 + E0 + (0 - A2 + E0) + (P3 - A3 + Eγ) + (P4 - A4 + Eγ))
    (hA : 0 ≤ A1 + A2 + A3 + A4) (hp : P1 - g2 ≤ X) (hs : P3 + P4 - I3 - I4 ≤ X + e8)
    (h0 : E0 ≤ F) (hγ : Eγ ≤ F) (t3 : F ≤ 2 * G) (t2 : e8 ≤ H) (nn : 0 ≤ Hc) :
    S1 + S2 + S3 + S4 - g2 - I3 - I4 ≤ 2 * X + (8 * G + 8 * Hc + H) := by
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
