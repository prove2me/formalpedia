-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x5.herm_f_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:34:47.494644+00:00
-- url     : https://prove2.me/submissions/98472a24-d18e-49b8-a6dc-fbd012efe2ee

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_lt
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_bvec_right
import Theorems.Thm_Formalism_QuantumDeterminants_gn_Hpk_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x5
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    herm (Hpk k r) (fvec k r z c) (bvec (esI k r a)) = if c.val = a.val then 1 else 0 := by
  rw [bvec, ggHerm_bvec_right]
  have hlt : r + k < (esI k r a).val := by simp [esI]; omega
  rw [gn_Hpk_mulVec, dif_pos (Or.inr hlt)]
  have e : (⟨2 * r + k - (esI k r a).val, by omega⟩ : Fin (2 * r + k + 1)) = ⟨a.val, by omega⟩ := by
    apply Fin.ext; simp [esI]; omega
  rw [e, fvec_apply_lt z hz c _ (by simp)]
end Formalism.FourierDecayAlt.P.C2x5
