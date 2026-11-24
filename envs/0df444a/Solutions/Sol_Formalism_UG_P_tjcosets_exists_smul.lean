-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_exists_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:29.369775+00:00
-- url     : https://prove2.me/submissions/c2dc17e2-bc31-4f14-8055-eaf59ef2417d

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Theorems.Thm_Formalism_UG_P_GL_smul_standard_tuple
import Theorems.Thm_Formalism_UG_P_tjcosets_extend

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
theorem _root_.solution [Finite 𝔽] (n j : ℕ) (w : TjcosetsFr (n - j) n 𝔽)
    (hw : LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽)) :
    ∃ g : GL (Fin n) 𝔽, g • (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) = w := by
  obtain ⟨s, hs, hsw⟩ := tjcosets_extend n j w hw
  let A : Matrix (Fin n) (Fin n) 𝔽 := Matrix.of fun a b => s b a
  have hAc : A.col = s := by funext b a; rfl
  have hA : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.1 (by rw [hAc]; exact hs)
  refine ⟨hA.unit, ?_⟩
  rw [GL_smul_standard_tuple]
  funext i
  rw [IsUnit.unit_spec, hAc, hsw]
end Formalism.UG.P
