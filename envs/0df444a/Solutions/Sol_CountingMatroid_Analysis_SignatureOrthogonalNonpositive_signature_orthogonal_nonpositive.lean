-- Prove2me | solution 1 for CountingMatroid.Analysis.SignatureOrthogonalNonpositive.signature_orthogonal_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T09:43:53.973106+00:00
-- url     : https://prove2.me/submissions/a8c47f34-d077-4780-8b43-93edfe6fec39

import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

set_option autoImplicit false

/-!
The elementary real quadratic-form step in the transport Hessian argument:
a form with at most one positive direction is nonpositive on the orthogonal
complement of any vector where the form is positive.
-/

namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SignatureOrthogonalNonpositive

/-- PAPER: main.tex:605-608
A quadratic form with at most one positive direction is nonpositive on the
orthogonal complement of a positive vector. -/
theorem solution {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (hsig : sigPos Q ≤ 1) (e v : V) (he : 0 < Q e)
    (horth : Q.associated e v = 0) : Q v ≤ 0 := by
  by_contra hn
  have hv : 0 < Q v := lt_of_not_ge hn
  let L : (Fin 2 → ℝ) →ₗ[ℝ] V :=
    { toFun := fun z => z 0 • e + z 1 • v
      map_add' := by intro z w; simp [add_smul]; abel
      map_smul' := by intro c z; simp [smul_add, mul_smul] }
  have hcalc (z : Fin 2 → ℝ) :
      Q (L z) = (z 0) ^ 2 * Q e + (z 1) ^ 2 * Q v := by
    rw [← Q.associated_eq_self_apply ℝ (L z)]
    simp [L, horth, QuadraticMap.associated_isSymm ℝ Q v e,
      QuadraticMap.associated_eq_self_apply, pow_two]
    ring
  have hpos : (Q.comp L).PosDef := by
    intro z hz
    rw [QuadraticMap.comp_apply, hcalc]
    have hne : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hz
      ext j
      fin_cases j <;> simp [hn]
    rcases hne with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0,
        mul_nonneg (sq_nonneg (z 1)) hv.le]
    · nlinarith [sq_pos_of_ne_zero h1,
        mul_nonneg (sq_nonneg (z 0)) he.le]
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro z hz
    by_contra hzn
    have hp := hpos z hzn
    have hz0 := LinearMap.mem_ker.mp hz
    simpa [QuadraticMap.comp_apply, hz0] using hp
  have hrange : (Q.restrict (LinearMap.range L)).PosDef := by
    intro z hz
    obtain ⟨w, hw⟩ := z.property
    have hwne : w ≠ 0 := by
      intro hw0
      apply hz
      apply Subtype.ext
      simpa [hw0] using hw.symm
    simpa only [QuadraticMap.restrict_apply, QuadraticMap.comp_apply, hw]
      using hpos w hwne
  have hdim := le_sigPos_of_posDef Q hrange
  rw [LinearMap.finrank_range_of_inj hinj] at hdim
  have htwo : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  rw [htwo] at hdim
  omega
