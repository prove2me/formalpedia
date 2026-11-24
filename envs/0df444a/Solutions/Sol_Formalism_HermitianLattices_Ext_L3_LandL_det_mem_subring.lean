-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LandL.det_mem_subring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:29.106916+00:00
-- url     : https://prove2.me/submissions/d0eb629b-8b07-43c4-8f0e-469a7bd3b9a6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandLA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LandL
namespace Formalism.HermitianLattices.Ext.L3.LandL
theorem _root_.solution {K : Type*} [Field K] (A : Subring K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, M i j ∈ A) : M.det ∈ A := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => h _ _) _
end Formalism.HermitianLattices.Ext.L3.LandL
