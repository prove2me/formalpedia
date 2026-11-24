-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.log_l_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:19.476805+00:00
-- url     : https://prove2.me/submissions/9a2f2a30-fe34-4642-9a58-8134da915800

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FiniteEulerProductLeZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
private lemma summable_inv_pow_of_two_le (M : ℕ) (hM : 2 ≤ M) : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ M) := by
  refine (Real.summable_nat_pow_inv.2 (by omega : 1 < M)).congr fun n => ?_
  rw [inv_pow]
private lemma tsum_inv_pow_eq_zeta (M : ℕ) (hM : 2 ≤ M) : ∑' n : ℕ, ((n : ℝ)⁻¹) ^ M = zetaR M := by
  rw [(summable_inv_pow_of_two_le M hM).tsum_eq_zero_add, zetaR]
  have h0 : ((((0 : ℕ) : ℝ))⁻¹) ^ M = 0 := by
    simp [zero_pow (by omega : M ≠ 0)]
  rw [h0, zero_add]
  congr 1
  ext n
  push_cast
  rw [one_div, inv_pow]
private lemma finite_euler_product_le_zeta (M : ℕ) (hM : 2 ≤ M) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹ ≤ zetaR M := by
  classical
  have hM0 : M ≠ 0 := by omega
  let F : ℕ →*₀ ℝ :=
    { toFun := fun n => ((n : ℝ)⁻¹) ^ M
      map_zero' := by simp [hM0]
      map_one' := by simp
      map_mul' := fun a b => by push_cast; rw [mul_inv, mul_pow] }
  have hF : ∀ n, F n = ((n : ℝ)⁻¹) ^ M := fun n => rfl
  have hsum : Summable (fun n => ‖F n‖) :=
    (summable_inv_pow_of_two_le M hM).congr fun n => by rw [hF, Real.norm_of_nonneg (by positivity)]
  have ht := EulerProduct.eulerProduct_completely_multiplicative hsum
  have htsum : ∑' n, F n = zetaR M := by
    simp only [hF]
    exact tsum_inv_pow_eq_zeta M hM
  rw [htsum] at ht
  have hfac : ∀ p : ℕ, p.Prime → 1 ≤ (1 - F p)⁻¹ := by
    intro p hp
    rw [hF]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have h1 : 0 ≤ ((p : ℝ)⁻¹) ^ M := by positivity
    have h2 : ((p : ℝ)⁻¹) ^ M < 1 := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hp1) hM0
    rw [one_le_inv₀ (by linarith)]
    linarith
  change ∏ p ∈ S, (1 - F p)⁻¹ ≤ zetaR M
  refine ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨S.sup id + 1, fun n hn => ?_⟩)
  have hsub : S ⊆ n.primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow]
    refine ⟨?_, hS p hp⟩
    have := Finset.le_sup (f := id) hp
    simp only [id] at this
    omega
  rw [← Finset.prod_sdiff hsub]
  apply le_mul_of_one_le_left
  · exact Finset.prod_nonneg fun p hp => le_trans zero_le_one (hfac p (hS p hp))
  · exact Finset.prod_induction _ (fun x => 1 ≤ x)
      (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      fun p hp => hfac p (Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.1 hp).1)
private lemma abs_log_inv_one_sub_le (s y x : ℝ) (hs : s = 1 ∨ s = -1) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) :
    |Real.log ((1 - s * y)⁻¹)| ≤ -Real.log (1 - x) := by
  rcases hs with rfl | rfl
  · have h1 : 0 < 1 - y := by linarith
    have h2 : 0 < 1 - x := by linarith
    rw [one_mul, Real.log_inv, abs_neg, abs_of_nonpos (Real.log_nonpos h1.le (by linarith))]
    have := Real.log_le_log h2 (by linarith : 1 - x ≤ 1 - y)
    linarith
  · rw [Real.log_inv, abs_neg, neg_one_mul, sub_neg_eq_add,
      abs_of_nonneg (Real.log_nonneg (by linarith))]
    have a := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + y)
    have b := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - x)
    linarith
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : LogLValueFinitePlaces := by
  intro f M ι _ pr Nv s hM hpr hN hs hcard
  classical
  have hM0 : M ≠ 0 := by omega
  have hxp : ∀ p : ℕ, p.Prime → 0 ≤ ((p : ℝ)⁻¹) ^ M ∧ ((p : ℝ)⁻¹) ^ M < 1 := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact ⟨by positivity, pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hp1) hM0⟩
  have hpos : ∀ v, 0 < (pr v : ℝ) := fun v => by exact_mod_cast (hpr v).pos
  have hy0 : ∀ v, 0 ≤ ((Nv v)⁻¹) ^ M := fun v => by
    have := lt_of_lt_of_le (hpos v) (hN v)
    positivity
  have hyx : ∀ v, ((Nv v)⁻¹) ^ M ≤ (((pr v : ℕ) : ℝ)⁻¹) ^ M := fun v =>
    pow_le_pow_left₀ (inv_nonneg.2 (lt_of_lt_of_le (hpos v) (hN v)).le)
      (inv_anti₀ (hpos v) (hN v)) M
  have hfpos : ∀ v, 0 < 1 - s v * ((Nv v)⁻¹) ^ M := by
    intro v
    have h1 := (hxp _ (hpr v)).2
    have h2 := hyx v
    rcases hs v with h | h <;> rw [h] <;> nlinarith [hy0 v]
  set T := Finset.univ.image pr with hT
  have hTp : ∀ p ∈ T, p.Prime := by
    intro p hp
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
    exact hpr v
  have hlogp : ∀ p ∈ T, 0 ≤ -Real.log (1 - ((p : ℝ)⁻¹) ^ M) := by
    intro p hp
    have := hxp p (hTp p hp)
    have : Real.log (1 - ((p : ℝ)⁻¹) ^ M) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  rw [Real.log_prod (fun v _ => (inv_pos.2 (hfpos v)).ne')]
  calc |∑ v, Real.log ((1 - s v * ((Nv v)⁻¹) ^ M)⁻¹)|
      ≤ ∑ v, |Real.log ((1 - s v * ((Nv v)⁻¹) ^ M)⁻¹)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, -Real.log (1 - (((pr v : ℕ) : ℝ)⁻¹) ^ M) := Finset.sum_le_sum fun v _ =>
        abs_log_inv_one_sub_le (s v) _ _ (hs v) (hy0 v) (hyx v) (hxp _ (hpr v)).2
    _ = ∑ p ∈ T, ∑ v ∈ Finset.univ.filter (fun v => pr v = p),
          -Real.log (1 - (((pr v : ℕ) : ℝ)⁻¹) ^ M) :=
        (Finset.sum_fiberwise_of_maps_to (fun v _ => Finset.mem_image_of_mem pr (Finset.mem_univ v)) _).symm
    _ ≤ ∑ p ∈ T, (f : ℝ) * -Real.log (1 - ((p : ℝ)⁻¹) ^ M) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.sum_congr rfl (g := fun _ => -Real.log (1 - ((p : ℝ)⁻¹) ^ M))
          (fun v hv => by rw [(Finset.mem_filter.1 hv).2]), Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard p) (hlogp p hp)
    _ = (f : ℝ) * Real.log (∏ p ∈ T, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹) := by
        rw [← Finset.mul_sum, Real.log_prod (fun p hp => (inv_pos.2 (by
          linarith [(hxp p (hTp p hp)).2])).ne')]
        simp only [Real.log_inv]
    _ ≤ (f : ℝ) * Real.log (zetaR M) := by
        refine mul_le_mul_of_nonneg_left (Real.log_le_log (Finset.prod_pos fun p hp => inv_pos.2 (by
          linarith [(hxp p (hTp p hp)).2])) (finite_euler_product_le_zeta M hM T hTp)) (Nat.cast_nonneg f)
end Formalism.HermitianLattices.GenusMassVolumes
