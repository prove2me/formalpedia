-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:46.443061+00:00
-- url     : https://prove2.me/submissions/233207c2-f17b-4295-9bcc-f863b229b389

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.OperatorRepresentations
theorem _root_.solution {ι : Type*} (s : Finset ι) (X : ι → Module.End ℂ (SV k r i D E))
    (T : ι → (Mx k r → E) → Mx k r → E) (h : ∀ j ∈ s, Rep (X j) (T j)) :
    Rep (∑ j ∈ s, X j) (fun f x => ∑ j ∈ s, T j f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rep_zero
  | insert j s hj ih =>
    have := (h j (by simp)).add (ih fun l hl => h l (by simp [hl]))
    simpa only [Finset.sum_insert hj] using this
end Formalism.FourierDecayAlt.P.OperatorRepresentations
