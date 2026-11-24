-- Prove2me | solution 1 for Formalism.G0.DetValP.part2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:36.217156+00:00
-- url     : https://prove2.me/submissions/a920519c-42ba-401a-b7da-1e4eaf8b239f

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Theorems.Thm_Formalism_G0_DetValP_substS_det
import Theorems.Thm_Formalism_G0_DetValP_entry_one_mem
import Theorems.Thm_Formalism_G0_DetValP_entry_one_nmem

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
open Formalism Formalism.G0 Formalism.G0.DetValP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetValP
theorem _root_.solution {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, vec (A l) = true)
    (hS : ¬ ∀ l, A l ∈ S) :
    ¬ MvPolynomial.C (Polynomial.X ^ 1) ∣
      substS (K := K) vec S (1 : GL (Fin r) K) (detLetters A) := by
  intro h
  obtain ⟨l₀, hl₀⟩ := not_forall.mp hS
  let last : Fin r := ⟨r - 1, by omega⟩
  let τ : Equiv.Perm (Fin r) := Equiv.swap l₀ last
  let v : ι × Fin r → K := fun p => if p.1 = A (τ p.2) then 1 else 0
  have h2 := map_dvd (MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : K)) v) h
  rw [MvPolynomial.eval₂Hom_C, substS_det] at h2
  simp only [Polynomial.coe_evalRingHom, pow_one, Polynomial.eval_X, zero_dvd_iff] at h2
  have hM : (Matrix.of fun l a => MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : K)) v
      (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (A l, a)))) =
      (1 : Matrix (Fin r) (Fin r) K).submatrix id τ := by
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    have hvv : v (A l, a) = if l = τ a then 1 else 0 := by
      simp only [v]
      by_cases e : l = τ a
      · simp [e]
      · have : A l ≠ A (τ a) := fun x => e (hA x)
        simp [e, this]
    by_cases hl : A l ∈ S
    · rw [entry_one_mem vec S _ v (A l) hl (hv l) a, hvv]
      by_cases e : l = τ a
      · have ha : a.val + 1 ≠ r := by
          intro ha
          have : a = last := by ext; simp [last]; omega
          apply hl₀
          have hll : l = l₀ := by rw [e, this]; exact Equiv.swap_apply_right l₀ last
          rw [← hll]; exact hl
        simp [e, ha]
      · simp [e]
    · rw [entry_one_nmem vec S _ v (A l) hl a, hvv]
  rw [hM, Matrix.det_permute', Matrix.det_one, mul_one] at h2
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with e | e <;> simp [e] at h2
end Formalism.G0.DetValP
