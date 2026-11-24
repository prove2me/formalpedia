-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.gfSlice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:29:18.473347+00:00
-- url     : https://prove2.me/submissions/17c4c700-12a2-4b08-88d2-702546ba72db

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_nset_sset
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_z_hat_of_block3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_minor_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_tz_low
import Theorems.Thm_Formalism_QuantumDeterminants_Zhat_eq
import Theorems.Thm_Formalism_QuantumDeterminants_gInv
import Theorems.Thm_Formalism_QuantumDeterminants_nSubgroup


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
theorem _root_.solution : GfSlice := by
  intro k j ρ z z' hz hz' x x' Z γ
  have hs : (Rn k j ρ x)⁻¹ ∈ Sset k (j + ρ) z := nset_sset z ((Formalism.QuantumDeterminants.nSubgroup k (j + ρ)).2.2 _ (rn_nset x))
  have hs' : Rn k j ρ x' ∈ Sset k (j + ρ) z' := nset_sset z' (rn_nset x')
  rw [Formalism.QuantumDeterminants.gInv k (j + ρ) z z' hz hz' _ hs _ hs' (mMap k j ρ Z γ)]
  have hZ : Zhat k (j + ρ) z z' (mMap k j ρ Z γ) =
      Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Z 0 0 (Zhat k ρ (lowV k j ρ z) (lowV k j ρ z') γ)) := by
    unfold mMap
    rw [z_hat_of_block3 z z' hz hz', Formalism.QuantumDeterminants.Zhat_eq]
    congr 1
    simp [← Matrix.mul_assoc, wMat_mul_self]
  have h1 : Dmin k (j + ρ) z z' (mMap k j ρ Z γ) (Fin.last _) =
      Z.det * Dmin k ρ (lowV k j ρ z) (lowV k j ρ z') γ (Fin.last _) := by
    unfold Dmin
    rw [hZ]
    exact minor_blocks _ _ (ρ + 1) le_rfl _
  have h0 : Dmin k (j + ρ) z z' (mMap k j ρ Z γ) ⟨j + ρ, by omega⟩ =
      Z.det * Dmin k ρ (lowV k j ρ z) (lowV k j ρ z') γ ⟨ρ, by omega⟩ := by
    unfold Dmin
    rw [hZ]
    exact minor_blocks _ _ ρ (by omega) _
  unfold Gf
  rw [h1, h0, tz_low z hz, tz_low z' hz', Complex.normSq_mul, Complex.normSq_mul]
  ring
end Formalism.FourierDecayAlt.P.Ux3
