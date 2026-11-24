-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.blk_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:22:45.746561+00:00
-- url     : https://prove2.me/submissions/7e168347-7a9d-4f9b-a239-75cb95a8f4e6

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {R : M.Ty P → M.Ty P → Prop} {ι : Type} (s : Finset ι) {X : ι → A} (hX : ∀ i ∈ s, GlobalTheory κ R (X i)) :
    GlobalTheory κ R (∑ i ∈ s, X i) := by
  intro σ τ h; rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun i hi => hX i hi σ τ h
end Formalism.FourierDecayAlt.P.NFx2
