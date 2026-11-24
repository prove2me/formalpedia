-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.colAddGen_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:52.090628+00:00
-- url     : https://prove2.me/submissions/2cc4089c-5471-4059-8a6d-98e92159f008

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l j (rowAct R g f) = rowActO R g (colAddGen R l j f) := by
  have key : (colAddGen R l j).comp (rowAct R g) =
      (rowActO R g).comp (colAddGen R (r := r) l j) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp only [AlgHom.comp_apply, colAddGen, rowAct, rowActO, aeval_X, map_sum,
      map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    by_cases h : t = j
    · simp only [h, if_true, aeval_X, map_add, map_mul, Option.elim]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    · simp [h]
  exact DFunLike.congr_fun key f
end Formalism.GradedWeylDivisibility
