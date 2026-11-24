-- Prove2me | solution 1 for Formalism.UG.P.GL_smul_standard_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:12.849819+00:00
-- url     : https://prove2.me/submissions/f428a05b-638c-49ab-b4bb-bda673ca47d2

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Theorems.Thm_Formalism_UG_P_tjcosets_smul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {𝔽 : Type} [Field 𝔽]
namespace Formalism.UG.P
theorem _root_.solution (n j : ℕ) (g : GL (Fin n) 𝔽) :
    (g • (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)) =
      fun i => (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j i) := by
  funext i
  rw [tjcosets_smul_apply, standardBasisTuple, Matrix.mulVec_single_one]
end Formalism.UG.P
