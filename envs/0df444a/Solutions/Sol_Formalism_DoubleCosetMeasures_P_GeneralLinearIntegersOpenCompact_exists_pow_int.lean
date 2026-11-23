-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.exists_pow_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:34.570328+00:00
-- url     : https://prove2.me/submissions/fe24a438-ab8f-4334-80ae-bb9dec49f490

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
theorem _root_.solution (R : Subring K) (ϖ : Kˣ) (hϖ : (ϖ : K) ∈ R)
    (hx : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) {n : ℕ} (e : Fin n → ℕ)
    (x : Matrix (Fin n) (Fin n) K)
    (hstr : ∀ a b, x a b = 0 ∨ (a = b ∧ x a b = 1) ∨ e a < e b) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m → ∀ a b,
      (((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * x a b * ((ϖ ^ (m * e b) : Kˣ) : K) ∈ R := by
  choose k hk using fun p : Fin n × Fin n => hx (x p.1 p.2)
  refine ⟨Finset.univ.sup k, fun m hm a b => ?_⟩
  rcases hstr a b with h | ⟨rfl, h⟩ | h
  · simp [h, R.zero_mem]
  · rw [h, mul_one, Units.inv_mul]; exact R.one_mem
  · obtain ⟨d, hd⟩ : ∃ d, e b = e a + (d + 1) := ⟨e b - e a - 1, by omega⟩
    have hk' : k (a, b) ≤ m * (d + 1) :=
      le_trans (Finset.le_sup (f := k) (Finset.mem_univ (a, b)))
        (le_trans hm (Nat.le_mul_of_pos_right m (Nat.succ_pos d)))
    have hu : (((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * ((ϖ ^ (m * e a) : Kˣ) : K) = 1 := Units.inv_mul _
    have eq : (((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * x a b * ((ϖ ^ (m * e b) : Kˣ) : K) =
        (ϖ : K) ^ (m * (d + 1) - k (a, b)) * ((ϖ : K) ^ k (a, b) * x a b) := by
      calc _ = x a b * ((ϖ ^ (m * (d + 1)) : Kˣ) : K) *
            ((((ϖ ^ (m * e a))⁻¹ : Kˣ) : K) * ((ϖ ^ (m * e a) : Kˣ) : K)) := by
            rw [hd, mul_add, pow_add, Units.val_mul]; ring
        _ = _ := by
            rw [hu, mul_one, Units.val_pow_eq_pow_val, ← mul_assoc, ← pow_add,
              Nat.sub_add_cancel hk', mul_comm]
    rw [eq]
    exact R.mul_mem (R.pow_mem hϖ _) (hk (a, b))
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
