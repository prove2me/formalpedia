-- Prove2me | solution 1 for Formalism.CountingSumsFrames.digit_inner_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:21.612313+00:00
-- url     : https://prove2.me/submissions/7df608d7-6982-4ac7-80d7-d47880c26fce

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds

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
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (n G t : ℕ) :
    ((univ : Finset (Fin (n+1))).filter (fun x : Fin (n+1) => ((x : ℕ) + G) % (n+1) = t % (n+1))).card = 1 := by
  set N := n + 1 with hN
  have hNpos : 0 < N := by omega
  let φ : Fin N → Fin N := fun x => ⟨((x : ℕ) + G) % N, Nat.mod_lt _ hNpos⟩
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : ((x : ℕ) + G) % N = ((y : ℕ) + G) % N := congrArg Fin.val hxy
    have h2 : (x : ℕ) ≡ (y : ℕ) [MOD N] := Nat.ModEq.add_right_cancel' G h1
    apply Fin.ext
    rw [← Nat.mod_eq_of_lt x.isLt, ← Nat.mod_eq_of_lt y.isLt]
    exact h2
  obtain ⟨x₀, hx₀⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨t % N, Nat.mod_lt _ hNpos⟩
  rw [Finset.card_eq_one]
  refine ⟨x₀, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hx
    apply hinj
    rw [hx₀]
    exact Fin.ext hx
  · rintro rfl
    exact congrArg Fin.val hx₀
end Formalism.CountingSumsFrames
