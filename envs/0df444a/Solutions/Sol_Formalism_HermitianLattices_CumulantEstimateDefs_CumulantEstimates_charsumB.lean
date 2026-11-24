-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.charsumB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:44.09817+00:00
-- url     : https://prove2.me/submissions/b989225b-54de-48d1-9c9b-a9ac922597d7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_charsumA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
open scoped Nat
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    ∑ c : (ZMod p)ˣ, (ZMod.stdAddChar ((c : ZMod p) * t) : ℂ) = if t = 0 then (p : ℂ) - 1 else -1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : ∑ c : (ZMod p)ˣ, (ZMod.stdAddChar ((c : ZMod p) * t) : ℂ) =
      ∑ x : {a : ZMod p // a ≠ 0}, (ZMod.stdAddChar ((x : ZMod p) * t) : ℂ) :=
    Fintype.sum_equiv unitsEquivNeZero _ _ (fun c => rfl)
  have h2 : ∑ x ∈ (univ : Finset (ZMod p)).erase 0, (ZMod.stdAddChar (x * t) : ℂ) =
      ∑ x : {a : ZMod p // a ≠ 0}, (ZMod.stdAddChar ((x : ZMod p) * t) : ℂ) :=
    Finset.sum_subtype _ (fun x => by simp) _
  rw [h1, ← h2, Finset.sum_erase_eq_sub (mem_univ _), charsumA p t]
  simp only [zero_mul, AddChar.map_zero_eq_one]
  split_ifs <;> ring
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
