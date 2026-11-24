-- Prove2me | solution 1 for Formalism.L2.Indef.ColData.period_images_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:18:38.576526+00:00
-- url     : https://prove2.me/submissions/cf7781d6-77b9-4f20-ab74-d192132f99a4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_ColData_fnorm_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.ColData
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)
namespace Formalism.L2.Indef.ColData
theorem _root_.solution (h : C.L1e) (hX : IsUnit (S.XE Bs.v0).det) (hD : 0 < S.D) (z : Sp.HH) (hz : z ∈ Sp.Rw) : ∃ y, C.sE y = z := by
  obtain ⟨hs, hm, hr, -⟩ := h
  have hinj : Function.Injective C.sE := by
    intro y1 y2 h12
    have h0 : C.sE (y1 - y2) = 0 := by rw [map_sub, h12, sub_self]
    have := hs (y1 - y2)
    rw [h0, norm_zero] at this
    exact sub_eq_zero.mp (fnorm_eq_zero _ hX _ this.symm)
  have hfin : FiniteDimensional ℂ Sp.Rw := Module.finite_of_finrank_pos (by rw [hr]; exact hD)
  let g : (Fin S.D → ℂ) →ₗ[ℂ] Sp.HH :=
    { toFun := fun y => C.sE (star y)
      map_add' := fun a b => by simp only [star_add, map_add]
      map_smul' := fun c a => by
        first
        | simp only [star_smul, map_smulₛₗ, starRingEnd_apply, star_star, RingHom.id_apply]
        | (simp only [RingHom.id_apply]
           rw [star_smul, map_smulₛₗ, starRingEnd_apply, star_star]) }
  have hinjg : Function.Injective g := fun a b hab => star_injective (hinj hab)
  have hle : LinearMap.range g ≤ Sp.Rw := by
    rintro _ ⟨y, rfl⟩
    exact hm _
  have hrank : finrank ℂ (LinearMap.range g) = finrank ℂ Sp.Rw := by
    rw [LinearMap.finrank_range_of_inj hinjg, hr]
    simp
  have heq : LinearMap.range g = Sp.Rw := by
    by_contra hne
    exact (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)).ne hrank
  rw [← heq] at hz
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hz
  exact ⟨star y, hy⟩
end Formalism.L2.Indef.ColData
