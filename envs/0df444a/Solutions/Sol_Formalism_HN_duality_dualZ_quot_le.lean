-- Prove2me | solution 1 for Formalism.HN.duality_dualZ_quot_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:18.53598+00:00
-- url     : https://prove2.me/submissions/fd91796a-5d04-45ab-8ff2-e3ed937ff863

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_mem_dualZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
section Dual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [FiniteDimensional ℝ E]
private theorem starProjection_mem_and_sub_mem_orthogonal (K : Submodule ℝ E)
    [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x ∈ K ∧ x - K.starProjection x ∈ Kᗮ := by
  constructor
  · exact K.starProjection_apply_mem x
  · exact K.sub_starProjection_mem_orthogonal x
end Dual
universe u
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [FiniteDimensional ℝ E]
namespace Formalism.HN
theorem _root_.solution (L T : Submodule ℤ E) (hT : T ≤ L) :
    dualZ (Formalism.F.quot L T) ≤ dualZ L := by
  intro y hy
  rw [duality_mem_dualZ] at hy ⊢
  obtain ⟨hy1, hy2⟩ := hy
  have hWL : span ℝ (T : Set E) ≤ span ℝ (L : Set E) := Submodule.span_mono hT
  have hQ : ∀ x ∈ L, (span ℝ (T : Set E))ᗮ.starProjection x ∈ Formalism.F.quot L T ∧
      (span ℝ (T : Set E))ᗮ.starProjection x ∈ (span ℝ (T : Set E))ᗮ ∧
      x - (span ℝ (T : Set E))ᗮ.starProjection x ∈ span ℝ (T : Set E) := by
    intro x hx
    obtain ⟨h1, h2⟩ := starProjection_mem_and_sub_mem_orthogonal (span ℝ (T : Set E))ᗮ x
    refine ⟨Submodule.mem_map_of_mem
      (f := ((span ℝ (T : Set E))ᗮ.starProjection : E →L[ℝ] E).toLinearMap.restrictScalars ℤ) hx,
      h1, ?_⟩
    rwa [Submodule.orthogonal_orthogonal] at h2
  have hspan : span ℝ (Formalism.F.quot L T : Set E) ≤
      (span ℝ (T : Set E))ᗮ ⊓ span ℝ (L : Set E) := by
    refine Submodule.span_le.mpr fun q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hq
    change (span ℝ (T : Set E))ᗮ.starProjection x ∈ (span ℝ (T : Set E))ᗮ ⊓ span ℝ (L : Set E)
    obtain ⟨-, h1, h2⟩ := hQ x hx
    rw [Submodule.mem_inf]
    refine ⟨h1, ?_⟩
    have h4 := Submodule.sub_mem _ (Submodule.subset_span hx : x ∈ span ℝ (L : Set E)) (hWL h2)
    rwa [sub_sub_cancel] at h4
  obtain ⟨hyW, hyL⟩ := Submodule.mem_inf.mp (hspan hy1)
  refine ⟨hyL, fun x hx => ?_⟩
  obtain ⟨hq, -, h2⟩ := hQ x hx
  obtain ⟨n, hn⟩ := hy2 _ hq
  refine ⟨n, ?_⟩
  have h0 : inner ℝ (x - (span ℝ (T : Set E))ᗮ.starProjection x) y = 0 := by
    exact Submodule.inner_right_of_mem_orthogonal h2 hyW
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [hn, h0]
end Formalism.HN
