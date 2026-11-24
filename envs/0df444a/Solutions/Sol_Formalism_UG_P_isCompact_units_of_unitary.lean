-- Prove2me | solution 1 for Formalism.UG.P.isCompact_units_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:27.15438+00:00
-- url     : https://prove2.me/submissions/b63d357b-2dbc-472f-89d7-b1314c4c636f

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Theorems.Thm_Formalism_UG_P_isCompact_of_unitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
private theorem mul_star_eq_one_of_star_mul_eq_one {M : Matrix n n ℂ} (h : star M * M = 1) : M * star M = 1 := by
  first
  | exact mul_eq_one_comm.mp h
  | (rw [← Matrix.inv_eq_left_inv h]; exact Matrix.mul_nonsing_inv M (Matrix.isUnit_det_of_left_inverse h))
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {T : Set (Matrix n n ℂ)} (hT : IsClosed T)
    (hU : ∀ M ∈ T, star M * M = 1) :
    IsCompact {g : GL n ℂ | (g : Matrix n n ℂ) ∈ T} := by
  have hK : IsCompact T := isCompact_of_unitary hT hU
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hK
  let f : T → GL n ℂ := fun M =>
    ⟨M.1, star M.1, mul_star_eq_one_of_star_mul_eq_one (hU M.1 M.2), hU M.1 M.2⟩
  have hf : Continuous f := by
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hS : {g : GL n ℂ | (g : Matrix n n ℂ) ∈ T} = Set.range f := by
    ext g
    constructor
    · intro hg
      exact ⟨⟨g, hg⟩, Units.ext rfl⟩
    · rintro ⟨M, rfl⟩
      exact M.2
  rw [hS]
  exact isCompact_range hf
end Formalism.UG.P
