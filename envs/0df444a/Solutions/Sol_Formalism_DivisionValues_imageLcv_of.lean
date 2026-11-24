-- Prove2me | solution 1 for Formalism.DivisionValues.imageLcv_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:16.673385+00:00
-- url     : https://prove2.me/submissions/62736ec9-0db9-4254-81bb-66b415de8a66

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Theorems.Thm_Formalism_DivisionValues_imageLcv_lidx_map
import Theorems.Thm_Formalism_DivisionValues_imageLcv_std_li
import Theorems.Thm_Formalism_DivisionValues_imageLcv_gram_ne

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
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution (h : LcvBasis) : ImageLcv := by
  intro K _ _ _ _ d XS XT hXS hXT φ hφ L hL
  classical
  have hu : IsUnit φ := (Matrix.isUnit_iff_isUnit_det φ).mpr hφ
  have hinj : Function.Injective φ.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hu
  have hsurj : Function.Surjective φ.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  let f : (Fin d → K) ≃ₗ[𝓞 K] (Fin d → K) :=
    LinearEquiv.ofBijective ((Matrix.mulVecLin φ).restrictScalars (𝓞 K)) ⟨hinj, hsurj⟩
  have hfmap : ∀ A : Submodule (𝓞 K) (Fin d → K),
      matLat φ A = A.map (f : (Fin d → K) →ₗ[𝓞 K] (Fin d → K)) := by
    intro A
    ext x
    rw [matLat, Submodule.mem_map, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hE := imageLcv_std_li (K := K) d
  have hF : LinearIndependent K (fun i => φ.mulVec (Pi.single i 1 : Fin d → K)) :=
    hE.map' (Matrix.mulVecLin φ) (LinearMap.ker_eq_bot.mpr hinj)
  have hspan : Submodule.span (𝓞 K) (Set.range (fun i => φ.mulVec (Pi.single i 1 : Fin d → K))) =
      matLat φ (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) := by
    rw [matLat, Submodule.map_span, ← Set.range_comp]
    rfl
  have hLat : Submodule.IsLattice K (matLat φ L) := by
    refine ⟨(Submodule.IsLattice.fg (self := hL)).map _, ?_⟩
    have : ((matLat φ L : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K)) =
        (Matrix.mulVecLin φ) '' (L : Set (Fin d → K)) := by
      rw [matLat, Submodule.map_coe]
      rfl
    rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top (self := hL), Submodule.map_top,
      LinearMap.range_eq_top]
    exact hsurj
  obtain ⟨-, h1⟩ := h K d XT hXT (matLat φ L) hLat _ hF
  obtain ⟨-, h2⟩ := h K d XS hXS L hL _ hE
  have hidx : ∀ w : HeightOneSpectrum (𝓞 K),
      idx w (Submodule.span (𝓞 K) (Set.range (fun i => φ.mulVec (Pi.single i 1 : Fin d → K))))
        (matLat φ L) =
      idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) L := by
    intro w
    rw [hspan, hfmap, hfmap]
    exact imageLcv_lidx_map _ f _ _
  simp only [hidx] at h1
  rw [h1, h2]
  have hdet : ∀ v, Real.log (detRatio XS XT φ v) =
      Real.log (gram XT v (fun i => φ.mulVec (Pi.single i 1 : Fin d → K))).det.re -
        Real.log (gram XS v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    intro v
    unfold detRatio
    exact Real.log_div (imageLcv_gram_ne XT hXT _ hF v) (imageLcv_gram_ne XS hXS _ hE v)
  simp only [hdet, Finset.sum_sub_distrib]
  ring
end Formalism.DivisionValues
