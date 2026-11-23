-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.LevelData.inv_S_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:58.167853+00:00
-- url     : https://prove2.me/submissions/96b1d33f-286b-4bd5-905c-9dd6104a0cfe

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_S_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.R.PInv
namespace _root_.Formalism.FourierDecayAlt.R.LevelData
theorem _root_.solution {f : Fin r → A} (hf : ∀ i, f i ∈ L.fns) :
    (List.ofFn f).prod ∈ Algebra.adjoin ℂ L.fns :=
  Subalgebra.list_prod_mem _ (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact L.inv_S_mem (hf i))
end _root_.Formalism.FourierDecayAlt.R.LevelData
end Formalism.FourierDecayAlt.R.PInv
