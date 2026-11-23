-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.eq_sum_gramSchmidt_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:35.98393+00:00
-- url     : https://prove2.me/submissions/7e30f245-0194-4b53-86d6-63da80beebab

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {r : ℕ} (a : Fin r → U) (n : Fin r) :
    a n = ∑ i, s5bL a n i • gramSchmidt ℂ a i := by
  have h0 := gramSchmidt_def'' ℂ a n
  have : ∀ i, s5bL a n i • gramSchmidt ℂ a i = (if i = n then gramSchmidt ℂ a i else 0) +
      (if i < n then (inner ℂ (gramSchmidt ℂ a i) (a n) / ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2)) •
        gramSchmidt ℂ a i else 0) := by
    intro i; simp only [s5bL, Matrix.of_apply]
    rcases lt_trichotomy i n with h | h | h
    · simp [h, h.ne]
    · simp [h]
    · simp [not_lt.2 h.le, h.ne']
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun i => i < n) = Finset.Iio n := by ext i; simp
  rw [hf]; exact h0
end Formalism.HermitianLatticeCounting.P
