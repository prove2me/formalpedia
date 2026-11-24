-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_orbit_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:11.989623+00:00
-- url     : https://prove2.me/submissions/ce0c0157-34a2-4a86-b5bd-1c2c42967639

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Theorems.Thm_Formalism_UG_P_GL_smul_standard_tuple
import Theorems.Thm_Formalism_UG_P_GL_columns_linearIndependent
import Theorems.Thm_Formalism_UG_P_tjcosets_exists_smul

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
theorem _root_.solution [Finite 𝔽] (n j : ℕ) :
    MulAction.orbit (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) =
      {w : TjcosetsFr (n - j) n 𝔽 | LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽)} := by
  ext w
  simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, rfl⟩
    rw [GL_smul_standard_tuple]
    exact GL_columns_linearIndependent n j g
  · intro hw
    exact tjcosets_exists_smul n j w hw
end Formalism.UG.P
