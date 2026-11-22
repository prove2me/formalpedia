-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggHerm_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:10:03.240144+00:00
-- url     : https://prove2.me/submissions/872b90dc-f4d8-4163-a30e-541872bb3395

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (v w : ι → ℂ) :
    herm H v w = star (herm H w v) := by
  have hH' : ∀ i j, star (H i j) = H j i := by
    intro i j
    have e := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using e
  simp only [herm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Pi.star_apply, hH',
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring
end Formalism.QuantumDeterminants
