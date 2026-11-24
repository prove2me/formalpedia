-- Prove2me | solution 1 for Formalism.HN.rescaleCovol_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:56.867033+00:00
-- url     : https://prove2.me/submissions/cb303491-3c68-4441-82a3-8617a16f1ddf

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
import Theorems.Thm_Formalism_HN_rscMap_apply
import Theorems.Thm_Formalism_HN_mem_placePart_iff
import Theorems.Thm_Formalism_HN_inner_eq_sum_pl
import Theorems.Thm_Formalism_HN_realize_smul_eq
import Theorems.Thm_Formalism_F_covolEqGram
import Theorems.Thm_P2M_Formalism_F_linearIndependent_coe_basis____9cab7951c4f4


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
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (h1 : PlaceSplit) (h2 : GramBlock) (h3 : PlLat) : RescaleCovol := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X c hX hc N hN
  have hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det := by
    intro v
    have hc0 : (c v : ℂ) ≠ 0 := by exact_mod_cast (hc v).ne'
    rw [Matrix.det_smul]
    exact (hc0.isUnit.pow _).mul (hX v)
  have hρ' := realize_smul_eq b X c hX hc
  have hinj : Function.Injective ((rscMap (ι := ι) c).restrictScalars ℤ) := by
    intro x y hxy
    ext p
    have := congrArg (fun z => z p) hxy
    simp only [LinearMap.restrictScalars_apply, rscMap_apply] at this
    exact mul_left_cancel₀ (inv_ne_zero (hc p.1).ne') this
  have hL' : zl (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N =
      (zl (Formalism.HermitianLatticesTheory.realize b X) N).map ((rscMap (ι := ι) c).restrictScalars ℤ) := by
    ext y
    simp only [zl, Submodule.mem_map, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, (hρ' x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, hρ' x⟩
  obtain ⟨⟨_, hLd⟩, -, -⟩ := h3 K V ι b X hX N hN
  obtain ⟨⟨_, hL'd⟩, -, -⟩ := h3 K V ι b _ hX' N hN
  rw [hL'] at hL'd ⊢
  have := hLd
  have := hL'd
  let E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)
  let L := zl (Formalism.HermitianLatticesTheory.realize b X) N
  let bL := Module.finBasis ℤ L
  let e := Submodule.equivMapOfInjective _ hinj L
  let bM := bL.map e
  have hbM : (fun i => (bM i : E)) = fun i => rscMap (ι := ι) c (bL i) := by
    funext i; simp [bM, e]
  rw [Formalism.F.covolEqGram _ _ _ bM, Formalism.F.covolEqGram _ L _ bL, hbM]
  have horth : ∀ v w : InfinitePlace K, v ≠ w → ∀ x ∈ placePart (ι := ι) v,
      ∀ y ∈ placePart (ι := ι) w, inner ℝ x y = 0 := by
    intro v w hvw x hx y hy
    rw [inner_eq_sum_pl]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : p.1 = v
    · rw [(mem_placePart_iff w y).1 hy p (by rw [hp]; exact hvw), mul_zero]
    · rw [(mem_placePart_iff v x).1 hx p hp, zero_mul]
  have hTinner : ∀ v, ∀ x ∈ placePart (ι := ι) v, ∀ y ∈ placePart (ι := ι) v,
      inner ℝ (rscMap c x) (rscMap c y) = (c v)⁻¹ ^ 2 * inner ℝ x y := by
    intro v x hx y hy
    rw [inner_eq_sum_pl, inner_eq_sum_pl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rscMap_apply, rscMap_apply]
    by_cases hp : p.1 = v
    · rw [hp]; ring
    · rw [(mem_placePart_iff v x).1 hx p hp]; ring
  have hTmap : ∀ v, ∀ x ∈ placePart (ι := ι) v,
      rscMap c x ∈ placePart (ι := ι) v ∧ ‖rscMap c x‖ ≤ (c v)⁻¹ * ‖x‖ := by
    intro v x hx
    refine ⟨(mem_placePart_iff v _).2 fun p hp => ?_, le_of_eq ?_⟩
    · rw [rscMap_apply, (mem_placePart_iff v x).1 hx p hp, mul_zero]
    · have h := hTinner v x hx x hx
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← mul_pow] at h
      exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.2 (hc v).le) (norm_nonneg _))
        two_ne_zero).1 h
  have hspZ : Submodule.span ℤ (Set.range fun i => (bL i : E)) = L := by
    have := congrArg (Submodule.map L.subtype) bL.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range fun i => (bL i : E)) = Submodule.span ℝ (L : Set E) := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (bL i).2)
    · refine Submodule.span_le.2 fun x hx => ?_
      rw [← hspZ] at hx
      exact Submodule.span_le_restrictScalars ℤ ℝ _ hx
  classical
  obtain ⟨hsplit, hdim⟩ := h1 K V ι b X hX N hN
  have hG := (h2 (InfinitePlace K) E E (Fin (finrank ℤ L)) (placePart (ι := ι)) (placePart (ι := ι))
    (rscMap c) (fun v => (c v)⁻¹) (Submodule.span ℝ (L : Set E)) (fun i => (bL i : E))
    horth horth (fun v => inv_nonneg.2 (hc v).le) hTmap hsplit
    (Formalism.F.linearIndependent_coe_basis''' L bL) hspan).2 hTinner
  have hdim' : ∀ v, finrank ℝ (Submodule.span ℝ (L : Set E) ⊓ placePart (ι := ι) v :
      Submodule ℝ E) = 2 * rkK N := hdim
  simp only [hdim'] at hG
  rw [hG, Real.sqrt_mul (Finset.prod_nonneg fun v _ => pow_nonneg (inv_nonneg.2 (hc v).le) _)]
  congr 1
  have hsq : (∏ v, (c v)⁻¹ ^ (2 * (2 * rkK N))) = (∏ v, (c v)⁻¹ ^ (2 * rkK N)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    ring
  rw [hsq, Real.sqrt_sq (Finset.prod_nonneg fun v _ => pow_nonneg (inv_nonneg.2 (hc v).le) _),
    Real.rpow_neg (Finset.prod_nonneg fun v _ => (hc v).le),
    show (2 * (rkK N : ℝ)) = ((2 * rkK N : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    ← Finset.prod_pow, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun v _ => inv_pow _ _
end Formalism.HN
