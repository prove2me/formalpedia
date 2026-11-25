-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameEntries.herm_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:40:27.929746+00:00
-- url     : https://prove2.me/submissions/efd53b35-c68b-4233-b8f9-20331855831d

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace FrameEntries
section Hom
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Hom
section Grp
variable {k r : ℕ}
private theorem hpk_conjTranspose_eq_self (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  have := i.2
  have := j.2
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | norm_num
end Grp
section Main
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Main
end FrameEntries
namespace FrameEntries
section Reg
variable {k r : ℕ}
end Reg
end FrameEntries
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FrameEntries
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have hH := hpk_conjTranspose_eq_self k r
  have hs : star (herm (Hpk k r) z z) = herm (Hpk k r) z z := by
    unfold herm
    conv_rhs => rw [Matrix.star_dotProduct]
    rw [Matrix.star_mulVec, hH, ← Matrix.dotProduct_mulVec]
  have him : (herm (Hpk k r) z z).im = 0 := by
    have h2 := congrArg Complex.im hs
    simp at h2
    linarith
  unfold Tz
  apply Complex.ext <;> simp [him]
end Formalism.FourierDecayAlt.P.FrameEntries
