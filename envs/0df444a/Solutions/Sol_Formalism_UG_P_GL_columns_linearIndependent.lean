-- Prove2me | solution 1 for Formalism.UG.P.GL_columns_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:05.203873+00:00
-- url     : https://prove2.me/submissions/1201a70c-9825-43da-89cd-3a2db395b773

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Theorems.Thm_Formalism_UG_P_tjcosets_idx_injective

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
theorem _root_.solution [Finite 𝔽] (n j : ℕ) (g : GL (Fin n) 𝔽) :
    LinearIndependent 𝔽 (fun i => (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j i)) := by
  exact (Matrix.linearIndependent_cols_of_isUnit (Units.isUnit g)).comp _ (tjcosets_idx_injective n j)
end Formalism.UG.P
