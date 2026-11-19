-- Prove2me | solution 1 for DiazModulus.fischler_theorem_6_4_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:18:59.194906+00:00
-- url     : https://prove2.me/submissions/37c82937-35a7-4bf3-b40d-03dec3b795c5

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_power_span_finrank
import Theorems.Thm_DiazModulus_fischler_rational_hull

open Complex ComplexConjugate

/-! # Fischler 2001, Theorem 6.4 (1)

Let `k ≥ 3` and suppose every product `v_{I(0)}⋯v_{I(k−1)}` lies in `ℒ̃`. Then the `Q̄`-span of `v₁, …, v_m` has
dimension at most `1`. Write `v = Σₐ cₐwₐ` with complex `cₐ` and `Q̄`-free algebraic vectors `wₐ`, the number of
terms being that dimension. If it is `0`, then `v = 0` and `a = 0`, `v′ = 0` work, since `k ≥ 1`. If it is `1`,
then `v = c₀w₀` with `w₀` algebraic and non-zero: choosing `j` with `w₀ⱼ ≠ 0`, `vⱼᵏ = c₀ᵏw₀ⱼᵏ ∈ ℒ̃`, and dividing
by the non-zero algebraic number `w₀ⱼᵏ` gives `a = c₀ᵏ ∈ ℒ̃`. With `v′ = w₀`, every product `v_I` equals
`c₀ᵏ·v′_I = a·v′_I`. -/

namespace RC9_F6a
open DiazModulus

/-- If `v = c • w` with `w` algebraic and non-zero and every `k`-fold product of the `v i` is in `ℒ̃`,
then `cᵏ ∈ ℒ̃`. -/
theorem pow_mem {m k : ℕ} (v : Fin m → ℂ) (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde)
    (c : ℂ) (w : Fin m → ℂ) (hwQ : ∀ i, w i ∈ Qbar) (hw0 : w ≠ 0) (hvw : ∀ i, v i = c * w i) :
    c ^ k ∈ LogAlgTilde := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (funext h)
  have hq0 : (⟨w j ^ k, Qbar.pow_mem (hwQ j) k⟩ : ↥Qbar) ≠ 0 := by
    intro h; exact hj (pow_eq_zero_iff'.1 (congrArg Subtype.val h)).1
  rw [← Submodule.smul_mem_iff LogAlgTilde hq0, Subfield.smul_def, smul_eq_mul]
  have := hv (fun _ => j)
  rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hvw, mul_pow, mul_comm] at this

end RC9_F6a

open DiazModulus in
theorem solution {m k : ℕ} (hk : 3 ≤ k) (v : Fin m → ℂ)
    (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) :
    ∃ a ∈ LogAlgTilde, ∃ v' : Fin m → ℂ, (∀ i, v' i ∈ Qbar) ∧
      ∀ I : Fin k → Fin m, ∏ t, v (I t) = a * ∏ t, v' (I t) := by
  have hn := (DiazModulus.fischler_power_span_finrank (by omega) v hv).2 hk
  obtain ⟨n, c, w, hn', -, hw, hwQ, hvw, -⟩ := DiazModulus.fischler_rational_hull v
  rw [← hn'] at hn
  interval_cases n
  · refine ⟨0, zero_mem _, 0, fun _ => zero_mem _, fun I => ?_⟩
    have hv0 : v = 0 := by simpa using hvw
    obtain ⟨p, rfl⟩ : ∃ p, k = p + 1 := ⟨k - 1, by omega⟩
    simp [hv0]
  · have hv1 : ∀ i, v i = c 0 * w 0 i := fun i => by simpa using congr_fun hvw i
    refine ⟨c 0 ^ k, RC9_F6a.pow_mem v hv (c 0) (w 0) (hwQ 0) (hw.ne_zero 0) hv1, w 0, hwQ 0,
      fun I => ?_⟩
    simp only [hv1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
