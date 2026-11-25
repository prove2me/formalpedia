-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.coeff_mem_of_ZP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:16.372313+00:00
-- url     : https://prove2.me/submissions/c5f13819-e5bf-4a4d-be03-23d271cc5913

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {σ : Type} {P : MvPolynomial σ C} (h : P ∈ ZP C σ) (O : Subring C) (m : σ →₀ ℕ) :
    P.coeff m ∈ O := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  rw [MvPolynomial.coeff_map, eq_intCast]
  exact intCast_mem O _
end Formalism.L2.FormalSeriesBounds.RF
