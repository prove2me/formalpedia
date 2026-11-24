-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.uniK_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:30:53.360901+00:00
-- url     : https://prove2.me/submissions/df51ce2b-c4ba-4ea2-9df4-76936123d179

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution {κ : Fin p → ℤ} {N : Matrix (Fin p) (Fin p) ℂ} (hd : ∀ a, N a a = 0)
    (hz : ∀ a b, κ a < κ b → N a b = 0) : uniK κ (1 + N) ∧ uniK κ (1 - N) := by
  have hne : ∀ a b, κ a < κ b → a ≠ b := fun a b h e => by subst e; exact lt_irrefl _ h
  refine ⟨⟨fun i => by simp [hd i], fun a b hab => ?_⟩, ⟨fun i => by simp [hd i], fun a b hab => ?_⟩⟩
  · simp [Matrix.one_apply_ne (hne a b hab), hz a b hab]
  · simp [Matrix.one_apply_ne (hne a b hab), hz a b hab]
end Formalism.FourierDecayAlt.P.Ux2
