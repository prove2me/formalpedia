-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lattice_sum_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:38.447799+00:00
-- url     : https://prove2.me/submissions/08343747-5687-41f3-85ee-fe5e926ba4e8

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_lt_one_of_lt_one
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_inverse_cube_plateau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
open MeasureTheory Metric
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : LatticeSum := by
  intro ι _ Λ H hH hΛ
  have hH0 : 0 < H := by linarith
  have hpi := Real.pi_pos
  set f := Fintype.card ι with hf
  let w₁ : ℂ → ℝ := fun z => ((max 1 (‖z‖ / H)) ^ 3)⁻¹
  let W : (ι → ℂ) → ℝ := fun x => ∏ v, w₁ (x v)
  obtain ⟨hw1i, hw1v⟩ := integral_inverse_cube_plateau H hH0
  have hWi : Integrable W :=
    Integrable.fintype_prod (f := fun _ => w₁) (μ := fun _ => volume) (fun _ => hw1i)
  have hWv : ∫ x, W x = (3 * Real.pi * H ^ 2) ^ f := by
    have := integral_fintype_prod_volume_eq_pow (ι := ι) w₁
    rw [hw1v] at this; exact this
  have hw10 : ∀ z, 0 < w₁ z := fun z => by simp only [w₁]; positivity
  have hW0 : ∀ x, 0 ≤ W x := fun x => Finset.prod_nonneg fun v _ => (hw10 _).le
  let P : (ι → ℂ) → Set (ι → ℂ) := fun c => Set.pi Set.univ fun v => ball (c v) (1 / 2)
  have hPm : ∀ c, MeasurableSet (P c) := fun c => MeasurableSet.univ_pi fun v => measurableSet_ball
  have hPvol' : ∀ c, (volume : Measure (ι → ℂ)) (P c) = ENNReal.ofReal ((Real.pi / 4) ^ f) := by
    intro c
    simp only [P]
    rw [volume_pi_pi]
    simp only [Complex.volume_ball]
    rw [Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [← ENNReal.ofReal_pow (by norm_num), ← NNReal.coe_real_pi, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; simp; ring
  have hPvol : ∀ c, (volume : Measure (ι → ℂ)).real (P c) = (Real.pi / 4) ^ f := by
    intro c; rw [measureReal_def, hPvol', ENNReal.toReal_ofReal (by positivity)]
  have hcomp : ∀ c y, y ∈ P c → W c ≤ (27 / 8) ^ f * W y := by
    intro c y hy
    simp only [W]
    rw [hf, Fintype.card, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v _ => (hw10 _).le) fun v _ => ?_
    have h1 := hy v (Set.mem_univ v)
    rw [mem_ball, dist_eq_norm] at h1
    have h2 : ‖y v‖ ≤ ‖c v‖ + 1 / 2 := by
      have : ‖y v‖ ≤ ‖y v - c v‖ + ‖c v‖ := by simpa using norm_add_le (y v - c v) (c v)
      linarith
    set a := max 1 (‖c v‖ / H) with ha
    set b := max 1 (‖y v‖ / H) with hb
    have ha1 : 1 ≤ a := le_max_left _ _
    have hb1 : 1 ≤ b := le_max_left _ _
    have hba : b ≤ 3 / 2 * a := by
      apply max_le (by linarith)
      have h3 : ‖c v‖ / H ≤ a := le_max_right _ _
      have h4 : ‖y v‖ / H ≤ ‖c v‖ / H + 1 / 2 := by
        rw [div_le_iff₀ hH0]
        have : (‖c v‖ / H + 1 / 2) * H = ‖c v‖ + H / 2 := by field_simp
        rw [this]; linarith
      linarith
    show (a ^ 3)⁻¹ ≤ 27 / 8 * (b ^ 3)⁻¹
    have h5 : b ^ 3 ≤ 27 / 8 * a ^ 3 := by
      calc b ^ 3 ≤ (3 / 2 * a) ^ 3 := pow_le_pow_left₀ (by linarith) hba 3
        _ = _ := by ring
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
    exact h5
  have key : ∀ S : Finset Λ, ∑ D ∈ S, W D ≤ (41 * H ^ 2) ^ f := by
    intro S
    have D : Set.Pairwise (S : Set Λ) (Function.onFun Disjoint fun D : Λ => P D) := by
      rintro c hc d hd hcd
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      have hne : (c : ι → ℂ) - d ≠ 0 := sub_ne_zero.mpr fun h => hcd (Subtype.ext h)
      obtain ⟨v₀, -⟩ : ∃ v, (c : ι → ℂ) v ≠ (d : ι → ℂ) v :=
        Function.ne_iff.mp fun h => hcd (Subtype.ext h)
      have h1 := hΛ _ (Λ.sub_mem c.2 d.2) hne
      have h2 := prod_lt_one_of_lt_one (fun v => ‖((c : ι → ℂ) - d) v‖) (fun v => norm_nonneg _)
        (fun v => by
          have a1 := hx v (Set.mem_univ v)
          have a2 := hx' v (Set.mem_univ v)
          rw [mem_ball, dist_eq_norm] at a1 a2
          have : ‖(c : ι → ℂ) v - (d : ι → ℂ) v‖ ≤ ‖x v - (d : ι → ℂ) v‖ + ‖x v - (c : ι → ℂ) v‖ := by
            have e : (c : ι → ℂ) v - (d : ι → ℂ) v = (x v - (d : ι → ℂ) v) - (x v - (c : ι → ℂ) v) := by
              abel
            rw [e]; exact norm_sub_le _ _
          simp only [Pi.sub_apply]; linarith) v₀
      linarith
    have hgi : Integrable fun y => (27 / 8 : ℝ) ^ f * W y := hWi.const_mul _
    have h1 : ∀ D ∈ S, W D * (Real.pi / 4) ^ f ≤ ∫ y in P D, (27 / 8 : ℝ) ^ f * W y := by
      intro D _
      rw [← hPvol D, mul_comm, ← smul_eq_mul]
      exact setIntegral_ge_of_const_le (hPm D) (by rw [hPvol']; exact ENNReal.ofReal_ne_top)
        (fun y hy => hcomp D y hy) hgi.integrableOn
    have h2 : ∑ D ∈ S, ∫ y in P D, (27 / 8 : ℝ) ^ f * W y =
        ∫ y in ⋃ D ∈ S, P D, (27 / 8 : ℝ) ^ f * W y :=
      (integral_biUnion_finset S (fun D _ => hPm D) D (fun D _ => hgi.integrableOn)).symm
    have h3 : ∫ y in ⋃ D ∈ S, P D, (27 / 8 : ℝ) ^ f * W y ≤ ∫ y, (27 / 8 : ℝ) ^ f * W y :=
      setIntegral_le_integral hgi (Filter.Eventually.of_forall fun y => by
        have := hW0 y; positivity)
    have h4 : ∫ y, (27 / 8 : ℝ) ^ f * W y = (27 / 8 : ℝ) ^ f * (3 * Real.pi * H ^ 2) ^ f := by
      rw [integral_const_mul, hWv]
    have h5 : (∑ D ∈ S, W D) * (Real.pi / 4) ^ f ≤ (27 / 8 : ℝ) ^ f * (3 * Real.pi * H ^ 2) ^ f := by
      rw [Finset.sum_mul]
      calc _ ≤ ∑ D ∈ S, ∫ y in P D, (27 / 8 : ℝ) ^ f * W y := Finset.sum_le_sum h1
        _ = _ := h2
        _ ≤ _ := h3
        _ = _ := h4
    have h6 : (27 / 8 : ℝ) ^ f * (3 * Real.pi * H ^ 2) ^ f ≤ (41 * H ^ 2) ^ f * (Real.pi / 4) ^ f := by
      rw [← mul_pow, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [mul_pos hpi (pow_pos hH0 2)]
    exact le_of_mul_le_mul_right (h5.trans h6) (by positivity)
  have hsum : Summable (fun D : Λ => W D) := summable_of_sum_le (fun D => hW0 D) key
  exact ⟨hsum, hsum.tsum_le_of_sum_le key⟩
end Formalism.HermitianLatticeCounting.P
