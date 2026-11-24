-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:04.982804+00:00
-- url     : https://prove2.me/submissions/a624ddab-9ddc-461e-a523-145bbd974bd3

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_elim_step

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
theorem _root_.solution {κ : Fin p → ℤ} (hκ : Function.Injective κ) (m : Matrix (Fin p) (Fin p) ℂ) (hm : uniK κ m) :
    ∃ L N : Matrix (Fin p) (Fin p) ℂ, uniK κ L ∧ uniK (kL p) L ∧ uniK (kU p) N ∧ m = L * N := by
  obtain ⟨L, M, h1, h2, h3, h4, h5⟩ := elim_step hκ m hm p
  exact ⟨L, M, h1, h2, ⟨h3.1, fun a b hab => h4 a b b.isLt (kU_lt.mp hab)⟩, h5⟩
end Formalism.FourierDecayAlt.P.Ux2
