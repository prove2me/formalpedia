-- Prove2me | solution 1 for Formalism.GM.DetBound.nnnorm_sum_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:54.81355+00:00
-- url     : https://prove2.me/submissions/222f23c4-c80e-4328-9fc0-a502fb2c1e5b

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DetBound
open Finset Polynomial
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.GM.DetBound
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → K) (r b : NNReal)
    (h : ∀ i ∈ s, ‖f i‖₊ * r ≤ b) : ‖∑ i ∈ s, f i‖₊ * r ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc ‖f a + ∑ i ∈ s, f i‖₊ * r ≤ max ‖f a‖₊ ‖∑ i ∈ s, f i‖₊ * r := by
          gcongr; exact IsUltrametricDist.nnnorm_add_le_max _ _
      _ = max (‖f a‖₊ * r) (‖∑ i ∈ s, f i‖₊ * r) := max_mul_of_nonneg _ _ r.2
      _ ≤ b := max_le (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))
end Formalism.GM.DetBound
