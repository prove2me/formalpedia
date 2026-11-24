-- Prove2me | solution 1 for Formalism.HN.quotient_lattice_realization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:25.055746+00:00
-- url     : https://prove2.me/submissions/12d5b0eb-5869-4210-8dc7-4ee2b8468743

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_QuotientRealization_covol_eq_of_norm_eq
import Theorems.Thm_Formalism_HN_QuotientRealization_zl_mono
import Theorems.Thm_Formalism_HN_QuotientRealization_exists_mat
import Theorems.Thm_Formalism_HN_QuotientRealization_proj_norm_sq
import Theorems.Thm_Formalism_HN_QuotientRealization_proj_eq_tv
import Theorems.Thm_Formalism_HN_QuotientRealization_tv_injective
import Theorems.Thm_Formalism_F_degQuot
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_norm_sq_realize
import Theorems.Thm_Formalism_HN_place_lattice_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution : QuotRealize := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A S hA hSat
  classical
  have hfinV : FiniteDimensional K V := Module.Finite.of_basis b
  set U := Submodule.span K (S : Set V) with hU
  let κ := Fin (finrank K (V ⧸ U))
  let b'' : Basis κ K (V ⧸ U) := Module.finBasis K (V ⧸ U)
  have hsurj : ∀ k, ∃ y, U.mkQ y = b'' k := fun k => U.mkQ_surjective _
  choose c hc using hsurj
  have hM := fun v => QuotientRealization.exists_mat (QuotientRealization.tv b X U c v)
    (QuotientRealization.tv_injective b X U b'' c hX hc v)
  choose M hMu hMn using hM
  let X'' : InfinitePlace K → Matrix κ κ ℂ := fun v => (M v)⁻¹
  have hX'' : ∀ v, IsUnit (X'' v).det := fun v => Matrix.isUnit_nonsing_inv_det _ (hMu v)
  have hnorm : ∀ v (x : V), Formalism.HermitianLatticesTheory.normAt b'' X'' v (U.mkQ x) =
      ‖(QuotientRealization.pv b X U v)ᗮ.starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))‖ := by
    intro v x
    rw [QuotientRealization.proj_eq_tv b X U b'' c hc v x, ← hMn v]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X'', Matrix.nonsing_inv_nonsing_inv _ (hMu v)]
    rfl
  refine ⟨κ, inferInstance, inferInstance, b'', X'', hX'', hnorm, ?_⟩
  intro N hSN hNA
  have hNfg : N.FG := Submodule.FG.of_le hA hNA
  set N'' := N.map (U.mkQ.restrictScalars (𝓞 K)) with hN''

  have hUle : U ≤ Submodule.span K (N : Set V) := Submodule.span_mono hSN
  have hrk : rkK N'' + rkK S = rkK N := by
    have hspan : Submodule.span K (N'' : Set (V ⧸ U)) = (Submodule.span K (N : Set V)).map U.mkQ := by
      rw [hN'', Submodule.map_coe]
      exact Submodule.span_image U.mkQ
    let W := Submodule.span K (N : Set V)
    let fW : W →ₗ[K] V ⧸ U := U.mkQ ∘ₗ W.subtype
    have h1 := LinearMap.finrank_range_add_finrank_ker fW
    have hr : LinearMap.range fW = W.map U.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hk : LinearMap.ker fW = U.comap W.subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hUle).finrank_eq] at h1
    unfold rkK
    rw [hspan]
    exact h1
  have hrkR : ((rkK N : ℝ) - rkK S) = rkK N'' := by
    rw [← hrk]; push_cast; ring

  let ρ := Formalism.HermitianLatticesTheory.realize b X
  let ρ'' := Formalism.HermitianLatticesTheory.realize b'' X''
  have hNlat := place_lattice_structure K V ι b X hX N hNfg
  have hN''lat := place_lattice_structure K (V ⧸ U) κ b'' X'' hX'' N'' (hNfg.map _)
  have : DiscreteTopology (zl ρ N) := hNlat.1.2
  have hsatN : Formalism.F.IsSaturated (zl ρ N) (zl ρ S) :=
    ⟨QuotientRealization.zl_mono ρ hSN, fun x hx hxs =>
      hSat.2.2 x (QuotientRealization.zl_mono ρ hNA hx) hxs⟩
  have : DiscreteTopology (Formalism.F.quot (zl ρ N) (zl ρ S)) :=
    (Formalism.F.degQuot _ _ _ inferInstance hsatN).1
  have : DiscreteTopology (zl ρ'' N'') := hN''lat.1.2
  let W := Submodule.span ℝ (zl ρ S : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))
  let f : N →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
    (Wᗮ.starProjection.toLinearMap.toAddMonoidHom).comp (ρ.comp N.subtype.toAddMonoidHom)
  let g : N →+ EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2) :=
    ρ''.comp ((U.mkQ.toAddMonoidHom).comp N.subtype.toAddMonoidHom)
  have h1 : ∀ y, y ∈ Formalism.F.quot (zl ρ N) (zl ρ S) ↔ ∃ m : N, f m = y := by
    intro y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨ρ x, ⟨x, hx, rfl⟩, rfl⟩
  have h2 : ∀ y, y ∈ zl ρ'' N'' ↔ ∃ m : N, g m = y := by
    intro y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨U.mkQ x, ⟨x, hx, rfl⟩, rfl⟩
  have hn : ∀ m, ‖f m‖ = ‖g m‖ := by
    rintro ⟨x, hx⟩
    have hsq : ‖f ⟨x, hx⟩‖ ^ 2 = ‖g ⟨x, hx⟩‖ ^ 2 := by
      show ‖Wᗮ.starProjection (ρ x)‖ ^ 2 = ‖ρ'' (U.mkQ x)‖ ^ 2
      rw [QuotientRealization.proj_norm_sq b X S x, PlaceOperatorNorms.norm_sq_realize]
      simp only [hnorm]
      rfl
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  have hcov := QuotientRealization.covol_eq_of_norm_eq f g _ _ h1 h2 hn
  have hht : htQ b X N S = ht b'' X'' N'' := by
    unfold htQ ht
    rw [hcov, hrkR, ← Nat.cast_mul, Real.rpow_natCast]
  refine ⟨hht, ?_⟩
  unfold sizeQ size
  rw [hht, hrkR]
end Formalism.HN
