-- Prove2me | solution 1 for Formalism.L2.DIV.cut_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:20.321951+00:00
-- url     : https://prove2.me/submissions/63cd3cba-138d-4d61-87dc-86ea84f67881

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_map_injective_of_injective

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (hE : Function.Injective E.mulVec) (hrat : ∀ i j, E i j ∈ cmMax K) (N : ℕ) (hN : 0 < N)
    (v : InfinitePlace K) (hpos : (H.map v.embedding).PosDef) :
    (((N : K)⁻¹ • (Eᴴ * H * E)).map v.embedding).PosDef := by
  have hE' := map_injective_of_injective E hE v.embedding
  have key : (Eᴴ * H * E).map v.embedding =
      (E.map v.embedding)ᴴ * H.map v.embedding * E.map v.embedding := by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext i j
    simp only [Matrix.map_apply, Matrix.conjTranspose_apply]
    exact hrat j i v.embedding
  have hsm : ((N : K)⁻¹ • (Eᴴ * H * E)).map v.embedding = ((N : ℂ)⁻¹) • ((Eᴴ * H * E).map v.embedding) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
  have hc : (0 : ℂ) < (N : ℂ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hN)
  rw [hsm, key]
  have hP := hpos.conjTranspose_mul_mul_same hE'
  first
  | exact hP.smul hc
  | exact Matrix.PosDef.smul hP hc
end Formalism.L2.DIV
