-- Prove2me | solution 1 for Formalism.L2.DIV.fk_int_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:46.55961+00:00
-- url     : https://prove2.me/submissions/3c41d7ed-0fdb-488b-a0d2-749c9d2b49d1

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
theorem _root_.solution {σ : Type} (P : MvPolynomial σ ℤ) :
    map (Int.castRingHom K) P ∈ (map (σ := σ) K0.subtype).range := by
  refine ⟨map (Int.castRingHom K0) P, ?_⟩
  rw [MvPolynomial.map_map, RingHom.ext_int (K0.subtype.comp (Int.castRingHom K0)) (Int.castRingHom K)]
end Formalism.L2.DIV
