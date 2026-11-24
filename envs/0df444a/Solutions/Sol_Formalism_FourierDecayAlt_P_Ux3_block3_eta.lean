-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.block3_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:30:56.801577+00:00
-- url     : https://prove2.me/submissions/75763da7-80c5-469d-994f-c981dcd757cc

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (M : B.Mat k (j + ρ)) : M = blk3
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inl (Sum.inl b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inl (Sum.inr b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inr b)))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inl (Sum.inl b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inl (Sum.inr b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inr b)))
    (M.submatrix (fun a => eB k j ρ (Sum.inr a)) (fun b => eB k j ρ (Sum.inl (Sum.inl b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inr a)) (fun b => eB k j ρ (Sum.inl (Sum.inr b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inr a)) (fun b => eB k j ρ (Sum.inr b))) := by
  ext x y
  obtain ⟨x', rfl⟩ := (eB k j ρ).surjective x
  obtain ⟨y', rfl⟩ := (eB k j ρ).surjective y
  rw [block3_apply]
  rcases x' with ((a | a) | a) <;> rcases y' with ((b | b) | b) <;> simp
end Formalism.FourierDecayAlt.P.Ux3
