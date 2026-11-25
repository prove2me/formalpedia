-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.aeval_mem_OP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:58:33.127922+00:00
-- url     : https://prove2.me/submissions/c5701135-48d1-407c-b0d5-a5e309b68f27

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
theorem _root_.solution {C : Type} [Field C] {O : Subring C} {σ τ : Type} (f : σ → MvPolynomial τ C)
    (hf : ∀ x, f x ∈ OP O τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) : MvPolynomial.aeval f P ∈ OP O τ := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  clear h
  induction Q using MvPolynomial.induction_on
  · rename_i z
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C, eq_intCast (Int.castRingHom C) z, map_intCast]
    exact intCast_mem _ z
  · rename_i p q hp hq
    rw [map_add, map_add]
    exact add_mem hp hq
  · rename_i p x hp
    rw [map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact mul_mem hp (hf x)
end Formalism.L2.FormalSeriesBounds.RF
