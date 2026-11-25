-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.good_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:27:20.924844+00:00
-- url     : https://prove2.me/submissions/3c10a9d4-4be5-4beb-9227-2f681b977145

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_eh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (hD : IsOpen D) (u : ℂ) (a b : Fin (mdim k r i)) :
    Good k r i D (fun f : Mx k r → E => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) := by
  have hE := good_eh (E := E) hD a b
  have hI : Good k r i D (fun (f : Mx k r → E) (g : Mx k r) =>
      if posL k r i a = posL k r i b then u • f g else 0) := by
    by_cases hc : posL k r i a = posL k r i b
    · simp only [if_pos hc]
      exact Good.smul good_id u
    · simp only [if_neg hc]
      exact good_zero
  exact Good.add hI hE
end Formalism.FourierDecayAlt.P.Qx2
