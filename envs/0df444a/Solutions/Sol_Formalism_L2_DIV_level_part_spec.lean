-- Prove2me | solution 1 for Formalism.L2.DIV.level_part_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:51.169054+00:00
-- url     : https://prove2.me/submissions/d7803cdd-83c5-4082-a101-e0bb4dca230e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_actMat_mul_lvlIdem
import Theorems.Thm_Formalism_L2_DIV_CSD_lvlIdem_mulVec_of_mem

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
theorem _root_.solution : LvlPartSpec := by
  intro K _ _ _ S G _ _ r P ψ
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    show ∀ h : P, (S.actMat r (h : G)).mulVec ((S.gaMat r (lvlIdem P ψ)).mulVecLin y) =
      ((ψ h : Kˣ) : K) • (S.gaMat r (lvlIdem P ψ)).mulVecLin y
    intro h
    have hsm : ∀ (c : K) (M : Matrix (Fin S.dim) (Fin S.dim) K) (v : Fin S.dim → K),
        (c • M).mulVec v = c • M.mulVec v := by
      intro c M v
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, S.actMat_mul_lvlIdem r P ψ h, hsm]
  · intro hx
    exact LinearMap.mem_range.mpr ⟨x, by
      rw [Matrix.mulVecLin_apply]
      exact S.lvlIdem_mulVec_of_mem r P ψ x hx⟩
end Formalism.L2.DIV
