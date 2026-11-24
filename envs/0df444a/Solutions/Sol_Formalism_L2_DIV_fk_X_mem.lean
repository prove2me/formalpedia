-- Prove2me | solution 1 for Formalism.L2.DIV.fk_X_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.58655+00:00
-- url     : https://prove2.me/submissions/8fd8ba92-5f16-449c-adb1-bfb0b4e07763

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] (K0 : Subfield K)
namespace Formalism.L2.DIV
theorem _root_.solution {σ : Type} (v : σ) : (X v : MvPolynomial σ K) ∈ (map (σ := σ) K0.subtype).range :=
  ⟨X v, map_X _ _⟩
end Formalism.L2.DIV
