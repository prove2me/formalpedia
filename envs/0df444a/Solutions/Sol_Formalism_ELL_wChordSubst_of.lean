-- Prove2me | solution 1 for Formalism.ELL.wChordSubst_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:54.291737+00:00
-- url     : https://prove2.me/submissions/1b9be7e8-2664-40e7-81d4-23b32f05270b

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_mvsubst_psubst
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_eq_zero_of_weq
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_ne_zero_of_weq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism.ELL.WeierstrassSubstitution
namespace Formalism.ELL
theorem _root_.solution (hU : Formalism.ELL.WSubstUnique.{u}) : Formalism.ELL.WChordSubst.{u} := by
  intro K _ W w hw F₂ hF0 hch σ _ s t hs ht hs0 ht0 hxst
  classical

  have chord_forms : ∀ (L : Type u) [Field L] (V : WeierstrassCurve.Affine L)
      (x0 x1 w0 w1 D PX : L), w0 ≠ 0 → w1 ≠ 0 → D = x0 * w1 - x1 * w0 → D ≠ 0 →
      PX = (w0 - w1) ^ 2 * w0 * w1 + V.a₁ * (w0 - w1) * D * w0 * w1
        - V.a₂ * D ^ 2 * w0 * w1 - x0 * D ^ 2 * w1 - x1 * D ^ 2 * w0 →
      V.addX (x0 / w0) (x1 / w1) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
          PX / (D ^ 2 * w0 * w1) ∧
      V.addY (x0 / w0) (x1 / w1) (-1 / w0) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
          (-((w0 - w1) * (PX - x0 * D ^ 2 * w1)) + D ^ 3 * w1 - V.a₁ * D * PX
            - V.a₃ * D ^ 3 * w0 * w1) / (D ^ 3 * w0 * w1) := by
    intro L _ V x0 x1 w0 w1 D PX h0 h1 hD hd hPX
    have hl : (-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1) = (w0 - w1) / D := by
      rw [hD]
      rw [hD] at hd
      field_simp
      ring
    have hX : V.addX (x0 / w0) (x1 / w1) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
        PX / (D ^ 2 * w0 * w1) := by
      rw [hl, hPX]
      simp only [WeierstrassCurve.Affine.addX]
      field_simp
    refine ⟨hX, ?_⟩
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY]
    rw [hX, hl]
    field_simp
    ring
  have hv : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hs, ht]
  set φ := MvPowerSeries.substAlgHom (R := K) hv with hφ
  have φe : ∀ g, φ g = MvPowerSeries.subst ![s, t] g := fun g => by
    rw [hφ, MvPowerSeries.coe_substAlgHom]
  have φX0 : φ (MvPowerSeries.X 0) = s := by rw [φe, MvPowerSeries.subst_X hv]; rfl
  have φX1 : φ (MvPowerSeries.X 1) = t := by rw [φe, MvPowerSeries.subst_X hv]; rfl
  have φw : ∀ g : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff g = 0 →
      φ (w.subst g) = w.subst (φ g) := fun g hg => by
    rw [φe, φe, mvsubst_psubst w g hg _ hv]
  have φw0 : φ (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) = w.subst s := by
    rw [φw _ (MvPowerSeries.constantCoeff_X 0), φX0]
  have φw1 : φ (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = w.subst t := by
    rw [φw _ (MvPowerSeries.constantCoeff_X 1), φX1]
  have φwF : φ (w.subst F₂) = w.subst (φ F₂) := φw F₂ hF0
  have injA := IsFractionRing.injective (MvPowerSeries (Fin 2) K)
    (FractionRing (MvPowerSeries (Fin 2) K))
  have injB := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))

  have ws0 : w.subst s ≠ 0 := ne_zero_of_weq (hU K W w hw σ s hs).1 hs0
  have wt0 : w.subst t ≠ 0 := ne_zero_of_weq (hU K W w hw σ t ht).1 ht0
  have dB : s * w.subst t - t * w.subst s ≠ 0 := by
    intro h
    apply hxst
    unfold Formalism.ELL.xOf
    rw [div_eq_div_iff ((map_ne_zero_iff _ injB).2 ws0) ((map_ne_zero_iff _ injB).2 wt0),
      ← map_mul, ← map_mul]
    congr 1
    linear_combination h
  have w00 : w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    ws0 (by rw [← φw0, h, map_zero])
  have w10 : w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    wt0 (by rw [← φw1, h, map_zero])
  have φD : φ (MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
      MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) =
      s * w.subst t - t * w.subst s := by
    simp only [map_sub, map_mul, φX0, φX1, φw0, φw1]
  have dA : MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
      MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    dB (by rw [← φD, h, map_zero])
  unfold Formalism.ELL.ChordAt at hch ⊢
  simp only at hch ⊢
  unfold Formalism.ELL.xOf Formalism.ELL.yOf at hch ⊢
  rw [(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00)
      ((map_ne_zero_iff _ injA).2 w10) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injA).2 dA) rfl).1,
    (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00)
      ((map_ne_zero_iff _ injA).2 w10) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injA).2 dA) rfl).2] at hch
  rw [(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0)
      ((map_ne_zero_iff _ injB).2 wt0) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injB).2 dB) rfl).1,
    (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0)
      ((map_ne_zero_iff _ injB).2 wt0) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injB).2 dB) rfl).2]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃] at hch ⊢
  simp only [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K)
    (FractionRing (MvPowerSeries (Fin 2) K))] at hch
  simp only [IsScalarTower.algebraMap_apply K (MvPowerSeries σ K)
    (FractionRing (MvPowerSeries σ K))]
  have iw0 := (map_ne_zero_iff _ injA).2 w00
  have iw1 := (map_ne_zero_iff _ injA).2 w10
  have idA : algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) (MvPowerSeries.X 0) *
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))
        (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) -
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) (MvPowerSeries.X 1) *
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))
        (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact (map_ne_zero_iff _ injA).2 dA
  have jw0 := (map_ne_zero_iff _ injB).2 ws0
  have jw1 := (map_ne_zero_iff _ injB).2 wt0
  have jdB : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s *
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst t) -
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) t *
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact (map_ne_zero_iff _ injB).2 dB
  obtain ⟨hx, hy⟩ := hch
  rw [← φe F₂]
  by_cases hwF : w.subst F₂ = 0
  ·
    have hF : F₂ = 0 := eq_zero_of_weq (hwF ▸ (hU K W w hw (Fin 2) F₂ hF0).1)
    have hr : w.subst (φ F₂) = 0 := by
      rw [hF, map_zero]
      exact ((hU K W w hw σ 0 (map_zero _)).2 0 (map_zero _)
        (by unfold Formalism.ELL.WEqAt; simp)).symm
    rw [hwF, map_zero, div_zero, eq_comm, div_eq_zero_iff] at hx hy
    have hx' := hx.resolve_right (by simp [iw0, iw1, idA])
    have hy' := hy.resolve_right (by simp [iw0, iw1, idA])
    simp only [← map_mul, ← map_sub, ← map_add, ← map_pow, ← map_neg] at hx' hy'
    rw [map_eq_zero_iff _ injA] at hx' hy'
    have hxB := congrArg φ hx'
    have hyB := congrArg φ hy'
    simp only [map_mul, map_sub, map_add, map_pow, map_neg, map_zero, AlgHom.commutes,
      φX0, φX1, φw0, φw1] at hxB hyB
    have hxF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hxB
    have hyF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hyB
    simp only [map_mul, map_sub, map_add, map_pow, map_neg, map_zero] at hxF hyF
    rw [hr, map_zero, div_zero, div_zero]
    constructor
    · rw [hxF, zero_div]
    · rw [hyF, zero_div]
  · have iwF := (map_ne_zero_iff _ injA).2 hwF
    rw [div_eq_div_iff iwF (by simp [iw0, iw1, idA])] at hx
    rw [div_eq_div_iff iwF (by simp [iw0, iw1, idA]), neg_one_mul] at hy
    simp only [← map_mul, ← map_sub, ← map_add, ← map_pow, ← map_neg] at hx hy
    rw [injA.eq_iff] at hx hy
    have hxB := congrArg φ hx
    have hyB := congrArg φ hy
    simp only [map_mul, map_sub, map_add, map_pow, map_neg, AlgHom.commutes,
      φX0, φX1, φw0, φw1, φwF] at hxB hyB
    have hxF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hxB
    have hyF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hyB
    simp only [map_mul, map_sub, map_add, map_pow, map_neg] at hxF hyF

    have jwr : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst (φ F₂)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, neg_eq_zero] at hyF
      revert hyF
      simp [jw0, jw1, jdB]
    constructor
    · rw [div_eq_div_iff jwr (by simp [jw0, jw1, jdB])]
      linear_combination hxF
    · rw [div_eq_div_iff jwr (by simp [jw0, jw1, jdB]), neg_one_mul]
      linear_combination hyF
end Formalism.ELL
