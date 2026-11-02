-- Prove2me | solution 1 for DiazModulus.quadric_trdeg_two_alg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T12:53:14.055221+00:00
-- url     : https://prove2.me/submissions/c7845cce-b224-4ee0-b6b9-15224db10e24

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_log_pair_rigid_of_trdeg_one

open Complex ComplexConjugate

/-! # `quadric_trdeg_two` for algebraic exponentials

If the transcendence degree were at most 1, `log_pair_rigid_of_trdeg_one` (the four exponentials theorem in
transcendence degree one, on the matrix of the quadric `|u|² = m⁻¹ |v|²`) would put `v` in `ℚu ∪ ℚū`,
against the `ℚ`-independence of `u, ū, v, v̄`. -/

open DiazModulus in
theorem solution {K : Subfield ℂ} (hK : ∀ z ∈ K, IsAlgebraic ℚ z)
    {u v : ℂ} {m : ℚ}
    (hu : Complex.exp u ∈ K) (hv : Complex.exp v ∈ K)
    (hm : m ≠ 0) (hquad : v * conj v = (m : ℂ) * (u * conj u))
    (hindep : ∀ a b c d : ℚ,
      (a : ℂ) * u + (b : ℂ) * conj u + (c : ℂ) * v + (d : ℂ) * conj v = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) :
    2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({u, conj u, v, conj v} : Set ℂ)) := by
  have hu0 : u ≠ 0 := by
    intro h
    have := (hindep 1 0 0 0 (by simp [h])).1
    exact one_ne_zero this
  have hv0 : v ≠ 0 := by
    intro h
    have := (hindep 0 0 1 0 (by simp [h])).2.2.1
    exact one_ne_zero this
  have hc : u * conj u = ((m⁻¹ : ℚ) : ℂ) * (v * conj v) := by
    rw [hquad]; push_cast
    have : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    field_simp
  have hset : ({u, conj u, v, conj v} : Set ℂ) = ({u, v, conj u, conj v} : Set ℂ) := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  by_contra hlt
  have hle : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({u, v, conj u, conj v} : Set ℂ)) ≤ 1 := by
    by_contra h1
    apply hlt
    have h2 := Order.succ_le_of_lt (lt_of_not_ge h1)
    have h3 : Order.succ (1 : Cardinal) = 2 := by
      have := Cardinal.succ_natCast 1
      simpa [one_add_one_eq_two] using this
    rwa [h3] at h2
  obtain ⟨q, hq | hq⟩ := log_pair_rigid_of_trdeg_one u v hu0 hv0 (hK _ hu) (hK _ hv) _ hc hle
  · have := (hindep q 0 (-1) 0 (by rw [hq]; push_cast; ring)).2.2.1
    norm_num at this
  · have := (hindep 0 q (-1) 0 (by rw [hq]; push_cast; ring)).2.2.1
    norm_num at this
