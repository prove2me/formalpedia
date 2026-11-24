-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localValuationFiltration.exists_local_data
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:33.210806+00:00
-- url     : https://prove2.me/submissions/c373672a-d7e4-4799-a8a3-40ab015e1af1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_repr_coe
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_discrIdeal_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_aniso_of_totPosDef
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_gram
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_gram_det_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_exists_basis_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_def
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_vd_locF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localValuationFiltration
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.localValuationFiltration
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (H : Matrix (Fin (finrank K V)) (Fin (finrank K V)) (𝓞 K))
      (D : 𝓞 F), locF 𝔭 (spanO b) = locF 𝔭 L ∧ (∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) ∧
        Hᴴ = H ∧ H.det = ι D ∧ D ≠ 0 ∧ vd h L 𝔭 = vF 𝔭 D := by
  obtain ⟨b, hbL, hb⟩ := exists_basis_locF hL h𝔭
  obtain ⟨H, hH, hdet⟩ := LocF.exists_gram hLi b hbL
  have hHH : Hᴴ = H := by
    ext i j
    show algebraMap (𝓞 K) K (star (H j i)) = algebraMap (𝓞 K) K (H i j)
    rw [hH, star_def]
    show star (algebraMap (𝓞 K) K (H j i)) = _
    rw [hH]
    exact hs.eq _ _
  obtain ⟨D, hD⟩ := (conjO_eq_iff_mem_range hF H.det).1 (by
    rw [← star_def, ← det_conjTranspose, hHH])
  have hD0 : D ≠ 0 := by
    rintro rfl
    apply LocF.gram_det_ne_zero h (LocF.aniso_of_totPosDef hd) b b.linearIndependent
    rw [← hdet, ← hD, map_zero, map_zero]
  refine ⟨b, H, D, hb, hH, hHH, hD.symm, hD0, ?_⟩
  rw [← vd_locF hF h L h𝔭, ← hb, vd_locF hF h _ h𝔭]
  unfold vd vF
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  rw [← mem_pow_iff (K := K), hD]
  constructor
  · intro hle
    exact hle (Ideal.subset_span ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, hdet⟩)
  · intro hmem
    refine BallB.discrIdeal_le b fun x hx z hz => ?_
    have hx' : b.det x = algebraMap (𝓞 K) K (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det := by
      rw [Basis.det_apply, RingHom.map_det]
      congr 1
      ext i j
      exact repr_coe b ⟨x j, hx j⟩ i
    have : z = star (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det * H.det *
        (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det := by
      apply RingOfIntegers.coe_injective
      rw [hz, hx', BallB.gdet, ← hdet]
      rfl
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)
end Formalism.HermitianLattices.Ext.L3.localValuationFiltration
