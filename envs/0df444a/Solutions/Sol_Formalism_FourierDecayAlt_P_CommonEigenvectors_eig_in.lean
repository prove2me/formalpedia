-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CommonEigenvectors.eig_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:56:38.113905+00:00
-- url     : https://prove2.me/submissions/d09ea6ce-074a-4650-a75e-28efb003168d

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CommonEigenvectors
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.CommonEigenvectors
theorem _root_.solution [FiniteDimensional ℂ V] (T : Module.End ℂ V) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hT : ∀ x ∈ G, T x ∈ G) : ∃ (μ : ℂ) (x : V), x ∈ G ∧ x ≠ 0 ∧ T x = μ • x := by
  haveI : Nontrivial G := Submodule.nontrivial_iff_ne_bot.2 hG
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T.restrict hT)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, x, x.2, fun h => hx.2 (Subtype.ext h), ?_⟩
  have h1 := Module.End.mem_eigenspace_iff.1 hx.1
  have h2 := congrArg Subtype.val h1
  simpa using h2
end Formalism.FourierDecayAlt.P.CommonEigenvectors
