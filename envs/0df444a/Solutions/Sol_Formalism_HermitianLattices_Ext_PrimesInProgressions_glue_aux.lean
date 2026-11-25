-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.glue_aux
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:06.598823+00:00
-- url     : https://prove2.me/submissions/13ff472a-d77b-4be7-b4c8-2b30abb5548a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTGlue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {S A B y η E E' F : ℝ} (h : S ≤ A * y * η * E) (hy : 0 ≤ y) (hη : 0 ≤ η)
    (hE : 0 ≤ E) (hEE : E ≤ E') (hF : 0 ≤ F) (hAB : A ≤ B) (hB : 0 ≤ B) :
    S ≤ B * y * η * (E' + F) := by
  have h1 : A * y * η * E ≤ B * y * η * E := by
    have : 0 ≤ y * η * E := by positivity
    nlinarith
  have h2 : B * y * η * E ≤ B * y * η * (E' + F) := by
    have : 0 ≤ B * y * η := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
