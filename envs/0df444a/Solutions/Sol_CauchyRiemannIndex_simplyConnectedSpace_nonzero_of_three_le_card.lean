-- Prove2me | solution 1 for CauchyRiemannIndex.simplyConnectedSpace_nonzero_of_three_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T18:13:20.736985+00:00
-- url     : https://prove2.me/submissions/bac01f2c-f6bb-4a0f-8bc8-7bffc2f812f6

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Theorems.Thm_SP4Mission_sphere_simplyConnected

namespace CauchyRiemannIndex

open scoped ContinuousMap

/-- `ℝ^ι ∖ {0}` is homotopy equivalent to the unit sphere of `EuclideanSpace ℝ (Fin (card ι))`. -/
noncomputable def nonzeroHomotopyEquivSphere (ι : Type*) [Fintype ι] :
    {y : ι → ℝ // y ≠ 0} ≃ₕ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (Fintype.card ι))) 1 := by
  let L : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hL : ∀ y : {y : ι → ℝ // y ≠ 0}, L y.1 ≠ 0 := fun y h =>
    y.2 (L.map_eq_zero_iff.mp h)
  have hn : ∀ y : {y : ι → ℝ // y ≠ 0}, 0 < ‖L y.1‖ := fun y => norm_pos_iff.mpr (hL y)
  have hcL : Continuous fun y : {y : ι → ℝ // y ≠ 0} => L y.1 :=
    L.continuous.comp continuous_subtype_val
  have hcinv : Continuous fun y : {y : ι → ℝ // y ≠ 0} => ‖L y.1‖⁻¹ :=
    (continuous_norm.comp hcL).inv₀ fun y => (hn y).ne'
  let f : C({y : ι → ℝ // y ≠ 0},
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (Fintype.card ι))) 1) :=
    have hm : ∀ y : {y : ι → ℝ // y ≠ 0},
        ‖L y.1‖⁻¹ • L y.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (Fintype.card ι))) 1 :=
      fun y => by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (hn y).ne']
    ⟨fun y => ⟨‖L y.1‖⁻¹ • L y.1, hm y⟩, (hcinv.smul hcL).subtype_mk hm⟩
  let g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (Fintype.card ι))) 1,
      {y : ι → ℝ // y ≠ 0}) :=
    have hm : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (Fintype.card ι))) 1,
        L.symm z.1 ≠ 0 := fun z h => by
      have h1 := congrArg L h
      simp only [ContinuousLinearEquiv.apply_symm_apply, map_zero] at h1
      have h2 := mem_sphere_zero_iff_norm.mp z.2
      rw [h1, norm_zero] at h2
      exact zero_ne_one h2
    ⟨fun z => ⟨L.symm z.1, hm z⟩, (L.symm.continuous.comp continuous_subtype_val).subtype_mk hm⟩
  refine
    { toFun := f
      invFun := g
      left_inv := ⟨
        { toFun := fun p => ⟨((1 - (p.1 : ℝ)) * ‖L p.2.1‖⁻¹ + p.1) • p.2.1, by
              have hc : 0 < (1 - (p.1 : ℝ)) * ‖L p.2.1‖⁻¹ + p.1 := by
                have h0 := p.1.2.1
                have h1 := p.1.2.2
                rcases eq_or_lt_of_le h0 with h | h
                · rw [← h]; simpa using hn p.2
                · nlinarith [inv_pos.mpr (hn p.2)]
              exact smul_ne_zero hc.ne' p.2.2⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
              (hcinv.comp continuous_snd)).add
                (continuous_subtype_val.comp continuous_fst)).smul
              (continuous_subtype_val.comp continuous_snd)
          map_zero_left := fun y => by
            apply Subtype.ext
            simp [f, g, L.symm_apply_eq, map_smul]
          map_one_left := fun y => by
            apply Subtype.ext
            simp }⟩
      right_inv := by
        have : f.comp g = ContinuousMap.id _ := by
          ext z : 2
          have h2 := mem_sphere_zero_iff_norm.mp z.2
          simp [f, g, h2]
        rw [this] }

/-- If `ι` has at least three elements, the punctured space `ℝ^ι ∖ {0}` is simply connected. -/
theorem simplyConnectedSpace_nonzero_of_three_le_card_aux {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) : SimplyConnectedSpace {y : ι → ℝ // y ≠ 0} := by
  haveI := SP4Mission.sphere_simplyConnected (Fintype.card ι) hι
  exact (nonzeroHomotopyEquivSphere ι).simplyConnectedSpace

end CauchyRiemannIndex

open CauchyRiemannIndex

theorem solution {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) : SimplyConnectedSpace {y : ι → ℝ // y ≠ 0} :=
  simplyConnectedSpace_nonzero_of_three_le_card_aux hι
