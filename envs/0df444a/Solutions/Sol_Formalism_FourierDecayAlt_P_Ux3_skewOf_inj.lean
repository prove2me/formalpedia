-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.skewOf_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:31:06.989743+00:00
-- url     : https://prove2.me/submissions/b1e7e201-b29c-4567-af7f-b003b8aa4855

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_apply_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_apply_diag

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
theorem _root_.solution {n : ℕ} (q q' : (G.UT n → ℂ) × (Fin n → ℝ)) (h : skewOf q = skewOf q') : q = q' := by
  obtain ⟨u, d⟩ := q
  obtain ⟨u', d'⟩ := q'
  have h1 : u = u' := by
    funext p
    obtain ⟨⟨a, b⟩, hab⟩ := p
    have := congrFun (congrFun h a) b
    simpa only [skewOf_apply_lt _ _ _ hab] using this
  have h2 : d = d' := by
    funext i
    have := congrFun (congrFun h i) i
    simp only [skewOf_apply_diag] at this
    have h3 := mul_left_cancel₀ Complex.I_ne_zero this
    simpa using h3
  rw [h1, h2]
end Formalism.FourierDecayAlt.P.Ux3
