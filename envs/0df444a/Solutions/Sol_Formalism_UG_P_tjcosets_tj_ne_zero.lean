-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_tj_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:53.227898+00:00
-- url     : https://prove2.me/submissions/ac2be3fb-8502-4fd4-a265-c4e6ff2d0c78

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Theorems.Thm_Formalism_UG_P_tjcosets_dG_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution {L : Type} [Field L] (O : Subring L) (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0)
    (g : GL (Fin n) L) :
    Tj ℤ n O ϖ j g ≠ 0 ↔
      ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O, g = a * tjcosets_dG n j ϖ hϖ * b := by
  unfold Tj
  rw [Set.indicator_apply_ne_zero]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Pi.one_apply, ne_eq,
    one_ne_zero, not_false_eq_true, and_true]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, ha, b, hb, Units.ext (by rw [h, Units.val_mul, Units.val_mul, tjcosets_dG_val])⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul, tjcosets_dG_val]⟩
end Formalism.UG.P
