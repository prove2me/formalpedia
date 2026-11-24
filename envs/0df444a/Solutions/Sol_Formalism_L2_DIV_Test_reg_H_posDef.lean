-- Prove2me | solution 1 for Formalism.L2.DIV.Test.reg_H_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:10:27.790049+00:00
-- url     : https://prove2.me/submissions/5d54c265-d420-4821-bc6c-d42bf958bb70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_Test_reg_csum
import Theorems.Thm_Formalism_L2_DIV_CSD_I_eq_sum
import Theorems.Thm_Formalism_L2_DIV_CSD_I_injective


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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
namespace Formalism.L2.DIV.Test
theorem _root_.solution (v0 : InfinitePlace K) (h0 : IsConjAt v0) :
    ((regCSD K G).H.map v0.embedding).PosDef := by
  classical
  let B : Matrix G (Fin (regCSD K G).dim) K :=
    Matrix.of fun c i => (((regCSD K G).basis i).1 : G → K) c
  have hH : (regCSD K G).H = Bᴴ * B := by
    ext i j
    simp only [CSD.H, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact reg_csum K G _ _
  have hmap : (regCSD K G).H.map v0.embedding = (B.map v0.embedding)ᴴ * (B.map v0.embedding) := by
    rw [hH, Matrix.map_mul, Matrix.conjTranspose_map (f := v0.embedding) (fun a => h0 a)]
  have hBI : ∀ x, B.mulVec x = (regCSD K G).I x := by
    intro x
    rw [CSD.I_eq_sum]
    funext c
    simp only [Matrix.mulVec, dotProduct, B, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hinj : Function.Injective (Matrix.toLin' B) := by
    intro x y hxy
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hBI, hBI] at hxy
    exact (regCSD K G).I_injective hxy
  obtain ⟨g, hg⟩ := (Matrix.toLin' B).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hC : LinearMap.toMatrix' g * B = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h
  have hC' : (LinearMap.toMatrix' g).map v0.embedding * B.map v0.embedding = 1 := by
    rw [← Matrix.map_mul, hC, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinj' : Function.Injective (B.map v0.embedding).mulVec := by
    intro x y hxy
    have h := congrArg ((LinearMap.toMatrix' g).map v0.embedding).mulVec hxy
    simpa only [Matrix.mulVec_mulVec, hC', Matrix.one_mulVec] using h
  rw [hmap]
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj'
end Formalism.L2.DIV.Test
