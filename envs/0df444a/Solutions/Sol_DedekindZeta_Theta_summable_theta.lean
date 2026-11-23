-- Prove2me | solution 1 for DedekindZeta.Theta.summable_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:07:14.061814+00:00
-- url     : https://prove2.me/submissions/c918271a-b26b-4ef0-acf9-646578275414

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {t : ℝ}
    (ht : 0 < t) :
    Summable fun x : (I : Submodule (𝓞 K) K) =>
      Real.exp (-Real.pi * t * ‖eEmb K (x : K)‖ ^ 2) := by
  classical
  -- View `I` as a unit (nonzero fractional ideals form a `CommGroupWithZero`).
  set I' : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 I hI with hI'
  -- The image lattice of `I` in the (non-Euclidean) mixed space.  It is a full,
  -- discrete lattice, so power-law sums over it converge (`ZLattice`).
  set M := mixedEmbedding.idealLattice K I' with hM
  -- The continuous linear equivalence relating the two models of `K_ℝ`.
  set toM := mixedEmbedding.euclidean.toMixed K with htoM
  -- The full embedding map `K_ℝ → K_ℝ^{eucl}` used by `eEmb`: weight the complex
  -- places by `√2`, then pass to the Euclidean model.  It is a fixed `ℝ`-linear
  -- iso, so it does not affect summability.
  set g : mixedSpace K ≃L[ℝ] minkowskiSpace K := (scaleMixed K).trans toM.symm with hg
  -- A norm-comparison constant for the inverse of `g`.
  set Cl : ℝ := ‖g.symm.toContinuousLinearMap‖ with hCl
  set Ko : ℝ := Cl + 1 with hKo
  have hCl_nonneg : 0 ≤ Cl := norm_nonneg _
  have hKo_pos : 0 < Ko := by rw [hKo]; linarith
  set c : ℝ := Ko⁻¹ with hc
  have hc_pos : 0 < c := by rw [hc]; exact inv_pos.mpr hKo_pos
  set a : ℝ := Real.pi * t * c ^ 2 with hadef
  have ha : 0 < a := by
    rw [hadef]; have := Real.pi_pos; positivity
  -- Finiteness of lattice points in any ball (discreteness of `M`).
  have hfin : ∀ R : ℝ, {z : M | ‖(z : mixedSpace K)‖ < R}.Finite := by
    intro R
    have hb : (Metric.ball (0 : mixedSpace K) R ∩ (M : Set (mixedSpace K))).Finite := by
      rw [hM, ← mixedEmbedding.span_idealLatticeBasis]
      exact ZSpan.setFinite_inter _ Metric.isBounded_ball
    apply (hb.preimage (Subtype.val_injective.injOn)).subset
    intro z hz
    refine ⟨?_, z.2⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  -- Power-law summability over the lattice `M`.
  set r : ℝ := -(Module.finrank ℤ M : ℝ) - 1 with hr
  have hsum_rpow : Summable (fun z : M => ‖(z : mixedSpace K)‖ ^ r) :=
    ZLattice.summable_norm_rpow M r (by rw [hr]; linarith)
  -- Gaussian decay beats any negative power.
  have hev : ∀ᶠ s : ℝ in Filter.atTop, Real.exp (-a * s ^ 2) ≤ s ^ r := by
    have key : Filter.Tendsto (fun s : ℝ => s ^ (-r) * Real.exp (-a * s ^ 2))
        Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun s : ℝ => s ^ 2) Filter.atTop Filter.atTop :=
        Filter.tendsto_pow_atTop two_ne_zero
      have hcomp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-r / 2) a ha).comp h2
      refine hcomp.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with s hs
      simp only [Function.comp_apply]
      congr 1
      rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs]
      congr 1
      push_cast; ring
    filter_upwards [key.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
      Filter.eventually_gt_atTop (0 : ℝ)] with s hs1 hs2
    have hsr : (0 : ℝ) < s ^ r := Real.rpow_pos_of_pos hs2 r
    have hrw : s ^ r * (s ^ (-r) * Real.exp (-a * s ^ 2)) = Real.exp (-a * s ^ 2) := by
      rw [← mul_assoc, ← Real.rpow_add hs2, add_neg_cancel, Real.rpow_zero, one_mul]
    calc Real.exp (-a * s ^ 2)
        = s ^ r * (s ^ (-r) * Real.exp (-a * s ^ 2)) := hrw.symm
      _ ≤ s ^ r * 1 := by exact mul_le_mul_of_nonneg_left hs1.le hsr.le
      _ = s ^ r := mul_one _
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hev
  -- Summability of the Gaussian over the lattice `M` (in the Euclidean model).
  have hsum_g : Summable (fun z : M =>
      Real.exp (-Real.pi * t * ‖g (z : mixedSpace K)‖ ^ 2)) := by
    apply Summable.of_norm_bounded_eventually hsum_rpow
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (hfin R)
    intro z hz
    simp only [Set.mem_setOf_eq]
    by_contra hlt
    push_neg at hlt
    apply hz
    set s : ℝ := ‖(z : mixedSpace K)‖ with hsdef
    set w := g (z : mixedSpace K) with hw
    have hsKo : s ≤ Ko * ‖w‖ := by
      calc s = ‖g.symm w‖ := by
              rw [hsdef, hw, ContinuousLinearEquiv.symm_apply_apply]
        _ ≤ Cl * ‖w‖ := g.symm.toContinuousLinearMap.le_opNorm w
        _ ≤ Ko * ‖w‖ := by gcongr; linarith
    have hcs : c * s ≤ ‖w‖ := by
      rw [hc]
      rw [inv_mul_le_iff₀ hKo_pos]
      linarith
    have hcs_nonneg : 0 ≤ c * s := by positivity
    have hws : c ^ 2 * s ^ 2 ≤ ‖w‖ ^ 2 := by
      have := pow_le_pow_left₀ hcs_nonneg hcs 2
      rwa [mul_pow] at this
    have hexp_le : Real.exp (-Real.pi * t * ‖w‖ ^ 2) ≤ Real.exp (-a * s ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hle : a * s ^ 2 ≤ Real.pi * t * ‖w‖ ^ 2 := by
        have heq : a * s ^ 2 = Real.pi * t * (c ^ 2 * s ^ 2) := by rw [hadef]; ring
        rw [heq]
        have hpt : (0 : ℝ) ≤ Real.pi * t := by have := Real.pi_pos; positivity
        exact mul_le_mul_of_nonneg_left hws hpt
      linarith
    have hg_nonneg : (0 : ℝ) ≤ Real.exp (-Real.pi * t * ‖w‖ ^ 2) := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hg_nonneg]
    exact hexp_le.trans (hR s hlt)
  -- Transfer summability back along the injection `I ↪ M`.
  have hφ : ∀ x : ↥(I : Submodule (𝓞 K) K), mixedEmbedding K (x : K) ∈ M := by
    intro x
    rw [hM, mixedEmbedding.mem_idealLattice]
    refine ⟨(x : K), ?_, rfl⟩
    have hx : (x : K) ∈ (I : Submodule (𝓞 K) K) := x.2
    simpa [hI', FractionalIdeal.mem_coe] using hx
  set φ : ↥(I : Submodule (𝓞 K) K) → M := fun x => ⟨mixedEmbedding K (x : K), hφ x⟩ with hφdef
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have h1 : mixedEmbedding K (x : K) = mixedEmbedding K (y : K) := by
      simpa [hφdef] using congrArg (Subtype.val) hxy
    have h2 : (x : K) = (y : K) := mixedEmbedding_injective K h1
    exact Subtype.ext h2
  refine (hsum_g.comp_injective hφ_inj).congr (fun x => ?_)
  simp only [Function.comp_apply, hφdef, eEmb, hg, htoM,
    ContinuousLinearEquiv.trans_apply]
end DedekindZeta.Theta
