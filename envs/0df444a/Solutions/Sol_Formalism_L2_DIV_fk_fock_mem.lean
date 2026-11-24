-- Prove2me | solution 1 for Formalism.L2.DIV.fk_fock_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:15.123573+00:00
-- url     : https://prove2.me/submissions/2c75c4e9-8c89-42df-aa6c-4999e268ff31

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_coeff_mem

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
theorem _root_.solution [StarRing K] {σ : Type} (P : MvPolynomial σ ℤ) {Q : MvPolynomial σ K}
    (hQ : Q ∈ (map (σ := σ) K0.subtype).range) : fockS (map (Int.castRingHom K) P) Q ∈ K0 := by
  unfold fockS
  refine sum_mem fun m _ => mul_mem (mul_mem ?_ (fk_coeff_mem K0 hQ m)) (natCast_mem K0 _)
  rw [coeff_map, eq_intCast, star_intCast]
  exact intCast_mem K0 _
end Formalism.L2.DIV
