-- Prove2me | solution 1 for Formalism.G0.DetValP.part1b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:36.132046+00:00
-- url     : https://prove2.me/submissions/b07637e8-684e-4bb7-b1bc-e9142bef44f1

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Theorems.Thm_Formalism_G0_DetValP_substS_det
import Theorems.Thm_Formalism_G0_DetValP_prod_last
import Theorems.Thm_Formalism_G0_DetValP_entry_one_mem

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
    (hS : ∀ l, A l ∈ S) :
    ¬ MvPolynomial.C (Polynomial.X ^ 2) ∣
      substS (K := K) vec S (1 : GL (Fin r) K) (detLetters A) := by
  intro h
  let v : ι × Fin r → Polynomial K := fun p => if p.1 = A p.2 then 1 else 0
  have h2 := map_dvd (MvPolynomial.eval₂Hom (RingHom.id (Polynomial K)) v) h
  rw [MvPolynomial.eval₂Hom_C, RingHom.id_apply, substS_det] at h2
  have hM : (Matrix.of fun l a => MvPolynomial.eval₂Hom (RingHom.id (Polynomial K)) v
      (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (A l, a)))) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1) := by
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, entry_one_mem vec S _ v (A l) (hS l) (hv l) a, Matrix.diagonal_apply]
    by_cases hla : l = a
    · subst hla; simp [v]
    · have : A l ≠ A a := fun e => hla (hA e)
      simp [v, this, hla]
  rw [hM, Matrix.det_diagonal, prod_last hr] at h2
  have := Polynomial.natDegree_le_of_dvd h2 Polynomial.X_ne_zero
  simp at this
end Formalism.G0.DetValP
