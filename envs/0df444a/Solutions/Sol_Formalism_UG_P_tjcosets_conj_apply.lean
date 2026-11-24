-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:45.933289+00:00
-- url     : https://prove2.me/submissions/d094fedc-f6fe-477a-88df-ffc43fad11b5

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
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
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L]
variable (O : Subring L) [IsLocalRing O]
variable {O}
namespace Formalism.UG.P
theorem _root_.solution (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0) (g : GL (Fin n) L) (a b : Fin n) :
    (((tjcosets_dG n j ϖ hϖ)⁻¹ * g * tjcosets_dG n j ϖ hϖ : GL (Fin n) L) :
        Matrix (Fin n) (Fin n) L) a b =
      (if (a : ℕ) < j then ϖ⁻¹ else 1) * (g : Matrix (Fin n) (Fin n) L) a b *
        (if (b : ℕ) < j then ϖ else 1) := by
  rw [Units.val_mul, Units.val_mul]
  have hinv : (((tjcosets_dG n j ϖ hϖ)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagJ n ϖ⁻¹ j := rfl
  rw [hinv, tjcosets_dG_val]
  unfold diagJ
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
end Formalism.UG.P
