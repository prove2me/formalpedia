-- Prove2me | solution 1 for Formalism.ELL.DeuringModel.exists_root_deuring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:21.176105+00:00
-- url     : https://prove2.me/submissions/b22d56dc-54df-46c3-973a-96f4b96601c0

import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Deuring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ELL
open Formalism.ELL.DeuringModel
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.DeuringModel
theorem _root_.solution [IsAlgClosed K] (j : K) :
    ∃ a : K, a ^ 3 * (a ^ 3 - 24) ^ 3 = j * (a ^ 3 - 27) := by
  let P : K[X] := X ^ 3 * (X ^ 3 - C 24) ^ 3 - C j * (X ^ 3 - C 27)
  have hdeg : P.degree = 12 := by
    simp only [P]
    compute_degree!
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P (by rw [hdeg]; norm_num)
  refine ⟨a, ?_⟩
  simp only [P, IsRoot, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at ha
  exact sub_eq_zero.mp ha
end Formalism.ELL.DeuringModel
