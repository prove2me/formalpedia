-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.w1_commute_of_mem_Glev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:34.843693+00:00
-- url     : https://prove2.me/submissions/46738336-7d42-4fac-aa69-05b6217e9dbe

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_succ_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_weyl_cell_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_mat_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution (c : ℂ) {g : Mx k r} (hg : g ∈ Glev k r l.succ) : w1 k r l c * g = g * w1 k r l c := by
  obtain ⟨hg0, h1, h2⟩ := (glev_succ_iff l g).1 hg
  apply mat_ext
  intro y
  have e1 : ⟪g *ᵥ y, 𝐞⟫ = ⟪y, 𝐞⟫ := by
    conv_lhs => rw [← h1]
    exact uh_herm hg0.1 _ _
  have e2 : ⟪g *ᵥ y, 𝐬⟫ = ⟪y, 𝐬⟫ := by
    conv_lhs => rw [← h2]
    exact uh_herm hg0.1 _ _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, weyl_cell_mulVec, weyl_cell_mulVec, e1, e2, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2]
end Formalism.FourierDecayAlt.P.Qx4
