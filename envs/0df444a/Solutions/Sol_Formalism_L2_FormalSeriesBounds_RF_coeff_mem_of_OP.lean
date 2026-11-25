-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.coeff_mem_of_OP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:12.220797+00:00
-- url     : https://prove2.me/submissions/d3be1e1c-a71d-45b9-ba28-3d6f4d98dab5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksCChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC

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
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {C : Type} [Field C] {O : Subring C} {σ : Type} {P : MvPolynomial σ C} (h : P ∈ OP O σ)
    (m : σ →₀ ℕ) : P.coeff m ∈ O := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  rw [MvPolynomial.coeff_map]
  exact (Q.coeff m).2
end Formalism.L2.FormalSeriesBounds.RF
