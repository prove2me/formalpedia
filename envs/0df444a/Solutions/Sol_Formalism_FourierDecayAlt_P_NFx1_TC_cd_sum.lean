-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx1.TC.cd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:19.86452+00:00
-- url     : https://prove2.me/submissions/1718b49b-ef1d-4fc4-92bd-09ccdcbb1880

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_TC_cd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_TC_CD_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_TC_CD_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx1 Formalism.FourierDecayAlt.P.NFx1.TC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.NFx1.TC
theorem _root_.solution {ι : Type*} (s : Finset ι) (c : ι → ℂ) (T : ι → (Mx k r → E) → Mx k r → E)
    (hT : ∀ j ∈ s, CD k r i (T j)) : CD k r i (fun f x => ∑ j ∈ s, c j • T j f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cd_zero
  | insert j s hj ih =>
    have := ((hT j (by simp)).smul (c j)).add (ih fun l hl => hT l (by simp [hl]))
    simpa only [Finset.sum_insert hj] using this
end Formalism.FourierDecayAlt.P.NFx1.TC
