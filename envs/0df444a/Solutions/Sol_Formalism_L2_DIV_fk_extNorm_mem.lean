-- Prove2me | solution 1 for Formalism.L2.DIV.fk_extNorm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:28.006144+00:00
-- url     : https://prove2.me/submissions/fd00f6b6-c0cb-435d-8df0-2a70a0f805b2

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_int_mem
import Theorems.Thm_Formalism_L2_DIV_fk_fock_mem
import Theorems.Thm_Formalism_L2_DIV_map_extremal


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
theorem _root_.solution [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) : extNorm K lam ∈ K0 := by
  unfold extNorm
  refine prod_mem fun τ _ => ?_
  rw [← map_extremal (Int.castRingHom K)]
  exact fk_fock_mem K0 _ (fk_int_mem K0 _)
end Formalism.L2.DIV
