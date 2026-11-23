-- Prove2me | solution 1 for Formalism.L2.Col.diagEmb_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:17.330489+00:00
-- url     : https://prove2.me/submissions/2b4055f3-b634-452d-874d-2271654466b7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Theorems.Thm_Formalism_L2_Col_diagEmb_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ]
variable {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution {r : ℕ} (h : r ≤ n) : Function.Injective (diagEmb κ h) := by
  intro g g' e
  apply Units.ext
  apply Matrix.ext
  intro i j
  have e' := congrArg (fun X : GL (Fin n) κ => (X : Matrix (Fin n) (Fin n) κ) (Fin.castLE h i) (Fin.castLE h j)) e
  beta_reduce at e'
  rw [diagEmb_val, diagEmb_val, diagMat_of_lt _ (show (Fin.castLE h i).val < r from i.2)
    (show (Fin.castLE h j).val < r from j.2), diagMat_of_lt _ (show (Fin.castLE h i).val < r from i.2)
    (show (Fin.castLE h j).val < r from j.2)] at e'
  exact e'
end Formalism.L2.Col
