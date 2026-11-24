-- Prove2me | solution 1 for Formalism.G0.DetQuotValP.not_dvd_substS_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:42.765596+00:00
-- url     : https://prove2.me/submissions/24de1c4a-1c29-477d-82b6-3702f54cf6be

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal
import Theorems.Thm_Formalism_G0_DetQuotValP_msMat_eval_zero_mul_eq_mul_diagonal
import Theorems.Thm_Formalism_G0_DetValP_substS_X
import Theorems.Thm_Formalism_G0_DetValP_substS_det


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
open Formalism Formalism.G0 Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetQuotValP
theorem _root_.solution {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r)
    (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A)
    (hv : ∀ l, vec (A l) = true) (hS : ¬ ∀ l, A l ∈ S) (g : GL (Fin r) L) :
    ¬ MvPolynomial.C Polynomial.X ∣ substS (K := K) vec S g (detLetters A) := by
  intro h
  obtain ⟨l₀, hl₀⟩ := not_forall.mp hS
  let last : Fin r := ⟨r - 1, by omega⟩
  let τ : Equiv.Perm (Fin r) := Equiv.swap l₀ last
  let v : ι × Fin r → L := fun p => ∑ l, if p.1 = A l then g.1 p.2 (τ l) else 0
  have hvA : ∀ l b, v (A l, b) = g.1 b (τ l) := by
    intro l b
    simp only [v]
    rw [Finset.sum_eq_single l]
    · simp
    · intro k _ hk
      have : A l ≠ A k := fun x => hk (hA x).symm
      simp [this]
    · simp
  let φ := MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : L)) v
  have h2 := map_dvd φ h
  rw [show φ (MvPolynomial.C Polynomial.X) = 0 by simp [φ], substS_det, zero_dvd_iff] at h2
  have hM : (Matrix.of fun l a => φ (substS (K := K) vec S g (MvPolynomial.X (A l, a)))) =
      (g.1.transpose).submatrix τ id := by
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.transpose_apply, substS_X]
    by_cases hl : A l ∈ S
    · simp only [hl, hv l, if_true, map_sum, map_mul, φ, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', hvA]
      have := congrFun (congrFun (msMat_eval_zero_mul_eq_mul_diagonal g) a) (τ l)
      rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
      simp only [Matrix.map_apply, Polynomial.coe_evalRingHom] at this
      simp only [Polynomial.coe_evalRingHom]
      rw [this]
      have hne : (τ l).val + 1 ≠ r := by
        intro e
        have h' : τ l = last := by ext; simp [last]; omega
        have hll : l = l₀ := by
          have := congrArg τ h'
          rw [Equiv.swap_apply_self] at this
          simpa [τ] using this
        exact hl₀ (hll ▸ hl)
      simp [hne]
    · simp only [hl, if_false, φ, MvPolynomial.eval₂Hom_X', hvA]
  rw [hM, Matrix.det_permute, Matrix.det_transpose] at h2
  have hu := Matrix.isUnits_det_units g
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with e | e <;> simp [e, hu.ne_zero] at h2
end Formalism.G0.DetQuotValP
