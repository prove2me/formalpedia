-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.psd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:31.521426+00:00
-- url     : https://prove2.me/submissions/5d2c24ec-981b-4593-92eb-5bf6c65d8ca0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
theorem _root_.solution {ι : Type} {F : Finset α} (s : Finset ι) (k : ι → α → α → ℂ)
    (h : ∀ i ∈ s, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ s, k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero F
  | insert i s hi ih =>
    have := psd_add (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj))
    exact psd_congr this fun x _ y _ => by rw [sum_insert hi]
end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
