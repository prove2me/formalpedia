-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.filteredPoleLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:42:00.371808+00:00
-- url     : https://prove2.me/submissions/594555e6-3a62-4a8b-80ab-21504ed2f60a

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_FilteredPoleLength
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthResidueFieldBase
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_filteredLength


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : FilteredPoleLength := by
  intro O' Rr A _ _ _ _ _ _ _ _ _ _ x mm n F r h0 hn hF hinj hlen

  have hpow : ∀ k, k < n → ∀ m : ℕ, ∀ a ∈ F k, x ^ m • a ∈ F (k + 1) → a ∈ F (k + 1) := by
    intro k hk m
    induction m with
    | zero => intro a _ h; simpa using h
    | succ m ih =>
      intro a ha h
      refine ih a ha (hinj k hk _ ((F k).smul_mem _ ha) ?_)
      rwa [smul_smul, ← pow_succ']

  have hstrict : ∀ k, k ≤ n → ∀ a : A, x ^ mm • a ∈ F k → a ∈ F k := by
    intro k
    induction k with
    | zero => intro _ a _; rw [h0]; trivial
    | succ k ih =>
      intro hk a h
      exact hpow k hk mm a (ih (by omega) a (hF k hk h)) h
  set N : Submodule Rr A := (⊤ : Submodule Rr A).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A))
    with hN
  have hcap : ∀ k, k ≤ n → N ⊓ F k = (F k).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A)) := by
    intro k hk
    ext b
    constructor
    · rintro ⟨⟨a, -, rfl⟩, hb⟩
      exact ⟨a, hstrict k hk a hb, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, trivial, rfl⟩, (F k).smul_mem _ ha⟩

  have hfl := filteredLength Rr A n (fun k => F (min k n)) (by simpa using h0) (by simpa using hn)
    (by
      intro k
      rcases lt_or_ge k n with hk | hk
      · simpa [min_eq_left hk.le, min_eq_left (Nat.succ_le_of_lt hk)] using hF k hk
      · simp [min_eq_right hk, min_eq_right (hk.trans (Nat.le_succ k))]) N
  have hsum : Module.length Rr (A ⧸ N) = (((∑ k ∈ Finset.range n, r k) * mm : ℕ) : ℕ∞) := by
    rw [hfl, Finset.sum_mul, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.mp hk
    rw [min_eq_left hk'.le, min_eq_left (Nat.succ_le_of_lt hk'), hcap k hk'.le]
    exact hlen k hk'
  rw [IsLocalRing.length_restrictScalars O' Rr (A ⧸ N), hsum]
end Formalism.LatticeBaseChangeAlt
