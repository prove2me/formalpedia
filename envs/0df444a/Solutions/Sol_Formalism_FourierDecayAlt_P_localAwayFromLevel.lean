-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.localAwayFromLevel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:04.011377+00:00
-- url     : https://prove2.me/submissions/fd67c310-53bd-4b1f-bda2-9b47f558400a

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.LocOrdinary := by
  intro E _ _ _ g k ν P hP hg
  have hg0 : (g : E) ≠ 0 := by
    intro h
    apply hg
    have : g = 0 := by exact_mod_cast h
    simp [this]
  have key : ∀ (k k' : ℤ) (t : E), t ∈ locAt E P (zsub E (idl E g k ν)) →
      t ∈ locAt E P (zsub E (idl E g k' ν)) := by
    intro k k' t
    rintro ⟨a, ha, h⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k' ≤ k + n := ⟨(k' - k).toNat, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k + n = k' + m := ⟨(k + n - k').toNat, by omega⟩
    refine ⟨(g : 𝓞 (maximalRealSubfield E)) ^ n * a,
      fun hh => (hP.mem_or_mem hh).elim (fun h' => hg (hP.mem_of_pow_mem _ h')) ha, ?_⟩
    change _ ∈ idl E g k ν at h
    show _ ∈ idl E g k' ν
    unfold idl at h ⊢
    rw [mul_comm, FractionalIdeal.mem_singleton_mul] at h ⊢
    obtain ⟨z, hz, hh⟩ := h
    refine ⟨(g : E) ^ m * z, ?_, ?_⟩
    · have := (dd E ^ ν : FI E).coeToSubmodule.smul_mem ((g : 𝓞 E) ^ m) hz
      rw [Algebra.smul_def] at this
      simpa using this
    · rw [map_mul, mul_assoc, hh, map_pow, map_natCast, ← mul_assoc, ← mul_assoc, ← zpow_natCast,
        ← zpow_natCast, ← zpow_add₀ hg0, ← zpow_add₀ hg0, add_comm (n : ℤ) k, hm]
  ext t
  exact ⟨key _ _ t, key _ _ t⟩
end Formalism.FourierDecayAlt.P
