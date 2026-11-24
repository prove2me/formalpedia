-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:30.340879+00:00
-- url     : https://prove2.me/submissions/968fdd87-0c60-44a5-b505-36ea21e624b5

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Theorems.Thm_Formalism_UG_P_tjcosets_card_orbit
import Theorems.Thm_Formalism_UG_P_tjcosets_red_surjective
import Theorems.Thm_Formalism_UG_P_tjcosets_stab

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
theorem _root_.solution (n j : ℕ) (ϖ : L) (hϖO : ϖ ∈ O) (hϖ : ϖ ≠ 0)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0)
    [Finite (IsLocalRing.ResidueField O)] :
    Nat.card {x : GL (Fin n) L ⧸ GLint (Fin n) O // ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
        x.out = a * tjcosets_dG n j ϖ hϖ * b} =
      (tjcosets_par (𝔽 := IsLocalRing.ResidueField O) n j).index := by
  rw [tjcosets_card_orbit, tjcosets_stab n j ϖ hϖO hϖ hmax]
  exact Subgroup.index_comap_of_surjective _ (tjcosets_red_surjective O n)
end Formalism.UG.P
