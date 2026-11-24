-- Prove2me | solution 1 for Formalism.L2.DIV.good_part_hermitian_of_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.516101+00:00
-- url     : https://prove2.me/submissions/b2fe85be-0dd2-4ed1-ad1e-f2f656036295

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_image_idempotent_spec
import Theorems.Thm_Formalism_L2_DIV_image_idempotent_rational
import Theorems.Thm_Formalism_L2_DIV_star_mem_cmMax
import Theorems.Thm_Formalism_L2_DIV_cut_posDef
import Theorems.Thm_Formalism_L2_DIV_gaMat_rat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution (h : GoodAtSpec) : GoodPartHermitianSpec := by
  intro K _ _ _ v0 hv S hH hpos G _ _ r hr X hX P ψ
  have hrat : ∀ i j, S.V0E r X P ψ i j ∈ cmMax K := by
    intro i j
    unfold CSD.V0E CSD.cutE
    exact image_idempotent_rational K S.dim _ (fun i j => gaMat_rat S r hr _ (h K v0 hv G X hX P ψ).rat i j) i j
  refine ⟨hrat, ?_, ?_⟩
  · intro i j
    unfold CSD.goodPartHermitianForm CSD.cutH
    rw [Matrix.smul_apply, smul_eq_mul]
    refine mul_mem (inv_mem (natCast_mem _ _)) ?_
    rw [Matrix.mul_apply]
    refine sum_mem fun k _ => mul_mem ?_ (hrat k j)
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (by rw [Matrix.conjTranspose_apply]; exact star_mem_cmMax (hrat l i)) (hH l k)
  · intro v
    unfold CSD.goodPartHermitianForm CSD.cutH
    exact cut_posDef S.H (S.cutE r _) (image_idempotent_spec K S.dim _).1 hrat (Nat.card P) Nat.card_pos v (hpos v)
end Formalism.L2.DIV
