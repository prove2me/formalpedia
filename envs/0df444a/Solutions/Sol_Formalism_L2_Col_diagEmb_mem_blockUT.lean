-- Prove2me | solution 1 for Formalism.L2.Col.diagEmb_mem_blockUT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:34.311014+00:00
-- url     : https://prove2.me/submissions/dac86514-f560-4c9f-9291-e3b8fd5a467e

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
theorem _root_.solution {r : ℕ} (h : r ≤ n) (bl : List ℕ) (g : GL (Fin r) κ) : diagEmb κ h g ∈ blockUT n κ r bl := by
  intro i j hij
  have hij' : coarse r bl j.val < coarse r bl i.val := hij
  have hi : ¬ i.val < r := fun hi => by rw [coarse_of_lt hi] at hij'; omega
  rw [diagEmb_val, diagMat_of_not_left _ _ hi]
  exact Matrix.one_apply_ne fun e => by rw [e] at hij'; omega
end Formalism.L2.Col
