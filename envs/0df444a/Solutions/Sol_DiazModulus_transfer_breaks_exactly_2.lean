-- Prove2me | solution 2 for DiazModulus.transfer_breaks_exactly
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:14:33.22639+00:00
-- url     : https://prove2.me/submissions/de1a8428-bf75-4bc1-8f5f-c61ecf478af7

import Mathlib
import Definitions.Def_DiazModulus

/-!
# What a transfer that loses candidacy must break

Let `u` be a candidate and `Φ` a ring endomorphism of `ℂ` that fixes the algebraic numbers and
commutes with conjugation at `u`, such that `Φ u` is not a candidate.

* The modulus is carried over verbatim: `Φ u · conj (Φ u) = Φ (u ū) = Φ ‖u‖² = ‖u‖²`, since
  `‖u‖²` is algebraic.
* If `Φ` commuted with `exp` at `u`, then `exp (Φ u) = Φ (exp u) = exp u` would be algebraic, and
  `Φ u` would be a candidate.
* The other five clauses are one failure, `Φ ∉ {id, conj}`, since `id u` and `conj u` are
  candidates. A ring endomorphism of `ℂ` that maps `ℝ` into `ℝ` is the identity on `ℝ`, as `ℝ`
  has no other ring endomorphism, so it is `id` or `conj`. One that commutes with conjugation
  everywhere maps `ℝ` into `ℝ`, and a continuous one is `id` or `conj` by Mathlib.
-/

open Complex ComplexConjugate

namespace W5_transfer

/-- A ring endomorphism of `ℂ` that maps `ℝ` into `ℝ` is the identity or conjugation. -/
theorem ringHom_eq_id_or_conj_of_mapsTo_real (Φ : ℂ →+* ℂ)
    (h : ∀ x : ℝ, (Φ (x : ℂ)).im = 0) : Φ = RingHom.id ℂ ∨ Φ = starRingEnd ℂ := by
  let ψ : ℝ →+* ℝ :=
    { toFun := fun x => (Φ x).re
      map_one' := by simp
      map_mul' := fun a b => by simp [h]
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hψ (x : ℝ) : Φ x = x := Complex.ext (Real.ringHom_apply ψ x) (by simp [h])
  simpa only [DFunLike.ext_iff] using! Complex.real_algHom_eq_id_or_conj
    (AlgHom.mk' Φ fun c z => by simp [Complex.real_smul, hψ])

end W5_transfer

open DiazModulus W5_transfer in
theorem solution (Φ : ℂ →+* ℂ) (u : ℂ) (hu : IsCandidate u)
    (hfix : ∀ a : ℂ, IsAlgebraic ℚ a → Φ a = a)
    (hconj : Φ (conj u) = conj (Φ u))
    (hnot : ¬ IsCandidate (Φ u)) :
    ‖Φ u‖ = ‖u‖ ∧
      Φ (Complex.exp u) ≠ Complex.exp (Φ u) ∧
      (∃ x : ℝ, (Φ (x : ℂ)).im ≠ 0) ∧
      (∃ z : ℂ, Φ (conj z) ≠ conj (Φ z)) ∧
      ¬ Continuous (Φ : ℂ → ℂ) ∧
      Φ ≠ RingHom.id ℂ ∧ Φ ≠ starRingEnd ℂ := by
  obtain ⟨hu0, hmod, hexp⟩ := hu
  -- the modulus is carried over verbatim
  have hnorm : ‖Φ u‖ = ‖u‖ := by
    have h : Φ u * conj (Φ u) = u * conj u := by
      rw [← hconj, ← map_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact hfix _ (by push_cast; exact hmod.pow 2)
    rw [Complex.mul_conj, Complex.mul_conj, Complex.ofReal_inj] at h
    rw [Complex.norm_def, Complex.norm_def, h]
  -- `id` and `conj` carry the candidate `u` to a candidate
  have hnid : ¬ (Φ = RingHom.id ℂ ∨ Φ = starRingEnd ℂ) := by
    rintro (rfl | rfl)
    · exact hnot ⟨hu0, hmod, hexp⟩
    · exact hnot ⟨by simpa using hu0, by rwa [Complex.norm_conj],
        by rw [Complex.exp_conj]; exact hexp.algHom (starRingEnd ℂ).toRatAlgHom⟩
  refine ⟨hnorm, fun h => hnot ⟨(map_ne_zero Φ).2 hu0, hnorm ▸ hmod, ?_⟩,
    not_forall.1 fun h => hnid (ringHom_eq_id_or_conj_of_mapsTo_real Φ h),
    not_forall.1 fun h => hnid (ringHom_eq_id_or_conj_of_mapsTo_real Φ fun x => ?_),
    fun h => hnid (Complex.ringHom_eq_id_or_conj_of_continuous h),
    fun h => hnid (.inl h), fun h => hnid (.inr h)⟩
  · rw [← h, hfix _ hexp]
    exact hexp
  · have hx := congrArg Complex.im (h x)
    rw [Complex.conj_ofReal, Complex.conj_im] at hx
    linarith
