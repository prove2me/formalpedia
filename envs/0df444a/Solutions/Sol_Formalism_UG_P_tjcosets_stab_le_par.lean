-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_stab_le_par
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:25.936786+00:00
-- url     : https://prove2.me/submissions/99f4ae1f-ac5b-41df-8333-2bb6bb4b9c62

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Theorems.Thm_Formalism_UG_P_GL_smul_standard_tuple
import Theorems.Thm_Formalism_UG_P_tjcosets_mem_par

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
    MulAction.stabilizer (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) ≤
      tjcosets_par n j := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff, GL_smul_standard_tuple] at hg
  rw [tjcosets_mem_par]
  intro a b ha hb
  have h1 : (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j ⟨b - j, by omega⟩) a
      = standardBasisTuple n j ⟨b - j, by omega⟩ a := congrFun (congrFun hg _) a
  simp only [standardBasisTuple] at h1
  rw [tjcosets_idx_sub n j b hb] at h1
  have hab : a ≠ b := by intro h; subst h; omega
  rw [Pi.single_eq_of_ne hab] at h1
  simpa [Matrix.col] using h1
end Formalism.UG.P
