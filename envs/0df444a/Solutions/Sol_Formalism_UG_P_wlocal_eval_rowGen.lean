-- Prove2me | solution 1 for Formalism.UG.P.wlocal_eval_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:25.402933+00:00
-- url     : https://prove2.me/submissions/6dc9fbe8-dd8a-49de-ac6c-fb4dd42e863e

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial
noncomputable section
namespace Formalism.UG.P
open Formalism.GradedWeylDivisibility
section
variable {R : Type} [CommRing R]
private lemma C_ite_add_ite_mul {σ : Type} (p q : Prop) [Decidable p] [Decidable q] (c : R)
    (Y : MvPolynomial σ R) :
    C ((if p then 1 else 0) + (if q then c else 0)) * Y = (if p then Y else 0) + (if q then C c * Y else 0) := by
  split_ifs <;> simp [add_mul]
end
section
variable {R : Type} [CommRing R]
end
section
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
end
section
variable {R S : Type} [CommRing R] [CommRing S]
end
section
variable {R : Type} [CommRing R]
end
end Formalism.UG.P
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution {r n : ℕ} (a b : Fin r) (c : R) (f : MvPolynomial (Fin r × Fin n) R) :
    Polynomial.eval (C c) (rowGen R b a f) = rowAct R (wlocal_E a b c) f := by
  refine MvPolynomial.induction_on
    (motive := fun f => Polynomial.eval (C c) (rowGen R b a f) = rowAct R (wlocal_E a b c) f) f ?_ ?_ ?_
  · intro x
    simp [rowGen, rowAct, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · intro p q hp hq
    rw [map_add, map_add, Polynomial.eval_add, hp, hq]
  · intro p v hp
    rw [map_mul, map_mul, Polynomial.eval_mul, hp]
    congr 1
    obtain ⟨i, j⟩ := v
    simp only [rowGen, rowAct, aeval_X, wlocal_E, C_ite_add_ite_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Polynomial.eval_add, Polynomial.eval_C]
    by_cases h : i = a
    · simp [h] <;> ring
    · simp [h]
end Formalism.UG.P
