-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.pos_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:54:24.81447+00:00
-- url     : https://prove2.me/submissions/1b34c75d-6e7d-470c-8515-48bab1641581

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.SkewHermitianParts
open AnisotropicColumnSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SkewHermitianParts
theorem _root_.solution (p : Fin (2 * r + k + 1)) :
    (∃ c, p = eI k r c) ∨ (∃ c, p = esI k r c) ∨ inWb k r (bvec p) := by
  by_cases h1 : p.val < r
  · exact Or.inl ⟨⟨p.val, h1⟩, rfl⟩
  · by_cases h2 : r + k < p.val
    · have := p.isLt
      exact Or.inr (Or.inl ⟨⟨2 * r + k - p.val, by omega⟩, Fin.ext (by simp only [esI]; omega)⟩)
    · refine Or.inr (Or.inr fun i hi => ?_)
      have : i ≠ p := by
        rintro rfl
        omega
      simp [bvec, this]
end Formalism.FourierDecayAlt.P.SkewHermitianParts
