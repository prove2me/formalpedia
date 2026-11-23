-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.LemmaU.II_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:35.556259+00:00
-- url     : https://prove2.me/submissions/12554895-3f8a-454f-b392-52ce252fa68c

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ComplexConjugate
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.LemmaU
open Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}
namespace Formalism.DoubleCosetMeasures.P.LemmaU
theorem _root_.solution (O : Subring F) (ϖ : F) (y : Matrix (Fin t) (Fin a) F) (hy : y ∈ IIset O ϖ)
    (g : Matrix (Fin a) (Fin a) F) (hg : ∀ i j, g i j ∈ O) : y * g ∈ IIset O ϖ := by
  simp only [Formalism.DoubleCosetMeasures.IIset, Set.mem_setOf_eq] at hy ⊢
  choose o ho hyo using hy
  intro i j
  refine ⟨∑ k, o i k * g k j, O.sum_mem fun k _ => O.mul_mem (ho i k) (hg k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hyo i k, mul_assoc]
end Formalism.DoubleCosetMeasures.P.LemmaU
