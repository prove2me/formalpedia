-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.psd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:05.835221+00:00
-- url     : https://prove2.me/submissions/79ffbc87-9a04-4c48-8a8a-a73b59dfbf57

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
variable {X : Type}
namespace Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
theorem _root_.solution {ι : Type} (S : Finset ι) {F : Finset X} {k : ι → X → X → ℂ}
    (hk : ∀ i ∈ S, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ S, k i x y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using psd_zero F
  | insert i S hi ih =>
    have := psd_add (hk i (Finset.mem_insert_self _ _))
      (ih fun j hj => hk j (Finset.mem_insert_of_mem hj))
    refine psd_congr ?_ this
    intro x _ y _; rw [Finset.sum_insert hi]
end Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
