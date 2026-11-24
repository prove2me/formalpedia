-- Prove2me | solution 1 for Formalism.HN.DualPolygon.dualZ_inf_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:04.534453+00:00
-- url     : https://prove2.me/submissions/0d32e9d5-d413-4946-8cb3-4425f84aab54

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_duality_dualZ_quot_le
import Theorems.Thm_Formalism_HN_duality_mem_dualZ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (L S : Submodule ℤ E) (hS : S ≤ L) :
    dualZ L ⊓ ((Submodule.span ℝ (S : Set E))ᗮ).restrictScalars ℤ = dualZ (Formalism.F.quot L S) := by
  set W := Submodule.span ℝ (S : Set E) with hW
  have hQW : Submodule.span ℝ (Formalism.F.quot L S : Set E) ≤ Wᗮ := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.1 hz
    exact Wᗮ.starProjection_apply_mem x
  apply le_antisymm
  · rintro y ⟨hyD, hyO⟩
    have hyO' : y ∈ Wᗮ := hyO
    have hyD : y ∈ dualZ L := hyD
    rw [duality_mem_dualZ] at hyD ⊢
    obtain ⟨hyL, hint⟩ := hyD
    refine ⟨?_, ?_⟩
    · have hPy : Wᗮ.starProjection y = y := Submodule.starProjection_eq_self_iff.2 hyO'
      have hspan : Submodule.span ℝ (Formalism.F.quot L S : Set E) =
          (Submodule.span ℝ (L : Set E)).map (Wᗮ.starProjection : E →L[ℝ] E).toLinearMap := by
        rw [← Submodule.span_image]
        congr 1
      rw [hspan, ← hPy]
      exact Submodule.mem_map_of_mem hyL
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
      obtain ⟨n, hn⟩ := hint x hx
      refine ⟨n, ?_⟩
      rw [hn]
      have h0 : inner ℝ (W.starProjection x) y = 0 :=
        Submodule.inner_right_of_mem_orthogonal (W.starProjection_apply_mem x) hyO'
      show inner ℝ x y = inner ℝ (Wᗮ.starProjection x) y
      rw [Submodule.starProjection_orthogonal_val, inner_sub_left, h0, sub_zero]
  · intro y hy
    refine ⟨duality_dualZ_quot_le L S hS hy, ?_⟩
    have := ((duality_mem_dualZ _ y).1 hy).1
    exact hQW this
end Formalism.HN.DualPolygon
