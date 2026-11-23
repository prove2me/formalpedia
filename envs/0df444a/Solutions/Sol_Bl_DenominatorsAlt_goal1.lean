-- Prove2me | solution 1 for Bl.DenominatorsAlt.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:06.301168+00:00
-- url     : https://prove2.me/submissions/23ce85db-ef72-4b42-bb6a-c8cd44fb9a22

import Mathlib
import Definitions.Def_Lemmata_Denominators_Denom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
namespace Bl.DenominatorsAlt
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
omit [StarRing E] in
private lemma denom (c : E) : ∃ k : ℕ, 0 < k ∧ ∃ w : 𝓞 E, (w : E) = (k : E) * c := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
  have hi : IsIntegral ℤ ((y : E) * c) := by
    have := h c (Finset.mem_singleton_self c)
    rwa [zsmul_eq_mul] at this
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨k, by omega, (⟨((k : ℤ) : E) * c, (mem_integralClosure_iff ℤ E).mpr hi⟩ : 𝓞 E), ?_⟩
    show ((k : ℤ) : E) * c = (k : E) * c
    push_cast
    ring
  · refine ⟨k, by omega, -(⟨((-(k : ℤ) : ℤ) : E) * c, (mem_integralClosure_iff ℤ E).mpr hi⟩ : 𝓞 E), ?_⟩
    show -((((-(k : ℤ)) : ℤ) : E) * c) = (k : E) * c
    push_cast
    ring
end Bl.DenominatorsAlt
end

set_option autoImplicit false
open NumberField
open Bl Bl.DenominatorsAlt
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
namespace Bl.DenominatorsAlt
theorem _root_.solution (M : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (M : Set (Fin n → E)) = ⊤)
    (v : Fin n → E) : ∃ m : ℕ, 0 < m ∧ (m : 𝓞 E) • v ∈ M := by
  have key : ∀ x ∈ Submodule.span E (M : Set (Fin n → E)),
      ∃ m : ℕ, 0 < m ∧ (m : 𝓞 E) • x ∈ M := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => exact ⟨1, one_pos, by simpa using h⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, ha, hax⟩ := ihx
      obtain ⟨b, hb, hby⟩ := ihy
      refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
      have e : ((a * b : ℕ) : 𝓞 E) • (x + y)
          = (b : 𝓞 E) • ((a : 𝓞 E) • x) + (a : 𝓞 E) • ((b : 𝓞 E) • y) := by
        rw [smul_smul, smul_smul, Nat.cast_mul, mul_comm (b : 𝓞 E), smul_add]
      rw [e]
      exact M.add_mem (M.smul_mem _ hax) (M.smul_mem _ hby)
    | smul c x _ ih =>
      obtain ⟨a, ha, hax⟩ := ih
      obtain ⟨k, hk, w, hw⟩ := denom c
      refine ⟨k * a, Nat.mul_pos hk ha, ?_⟩
      have e : ((k * a : ℕ) : 𝓞 E) • (c • x) = w • ((a : 𝓞 E) • x) := by
        rw [← algebraMap_smul E ((k * a : ℕ) : 𝓞 E), ← algebraMap_smul E w,
          ← algebraMap_smul E (a : 𝓞 E), smul_smul, smul_smul, map_natCast, map_natCast,
          ← RingOfIntegers.coe_eq_algebraMap, hw]
        push_cast
        ring_nf
      rw [e]
      exact M.smul_mem _ hax
  exact key v (by rw [hsp]; exact Submodule.mem_top)
end Bl.DenominatorsAlt
