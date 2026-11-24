-- Prove2me | solution 1 for Formalism.L2.S.Pv.PsiTrCore.exists_int_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:55.41008+00:00
-- url     : https://prove2.me/submissions/81ec7e5d-5274-45bd-a418-0ba2a981d750

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
import Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_valued_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
namespace Formalism.L2.S.Pv.PsiTrCore
variable {F : Type} [Field F] [NumberField F]
private theorem exists_integer_approx_valuation (v : HeightOneSpectrum (𝓞 F)) (k : F) (hk : v.valuation F k ≤ 1)
    (N : ℕ) : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) ≤ WithZero.exp (-(N : ℤ)) := by
  classical
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) k
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hY : algebraMap (𝓞 F) F y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  set m := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors with hm
  have hvy : v.intValuation y = WithZero.exp (-(m : ℤ)) := v.intValuation_if_neg hy0
  have hX : v.intValuation x =
      v.valuation F (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y) * v.intValuation y := by
    rw [← valuation_of_algebraMap (K := F) v x, ← valuation_of_algebraMap (K := F) v y, ← map_mul,
      div_mul_cancel₀ _ hY]
  have hxm : x ∈ v.asIdeal ^ m := by
    rw [← intValuation_le_pow_iff_mem, hX, ← hvy]
    exact mul_le_of_le_one_left' hk
  have hdvd : v.asIdeal ^ m ∣ Ideal.span {y} := (intValuation_le_pow_iff_dvd v y m).mp hvy.le
  obtain ⟨J, hJ⟩ := hdvd
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hJv
    have hy1 : y ∈ v.asIdeal ^ m * J := hJ ▸ Ideal.mem_span_singleton_self y
    have hy2 : y ∈ v.asIdeal ^ (m + 1) := by
      rw [pow_succ]; exact Ideal.mul_mono_right hJv hy1
    have := (intValuation_le_pow_iff_mem v y (m + 1)).mpr hy2
    rw [hvy, WithZero.exp_le_exp] at this
    omega
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJv
  have hxt : x * t ∈ Ideal.span {y} := hJ ▸ Ideal.mul_mem_mul hxm htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hxt
  obtain ⟨s, i, hi, hsi⟩ := v.isMaximal.exists_inv htv
  have htt : t * (s * ∑ j ∈ Finset.range N, i ^ j) = 1 - i ^ N := by
    have h1 : s * t = 1 - i := by linear_combination hsi
    calc t * (s * ∑ j ∈ Finset.range N, i ^ j) = (s * t) * ∑ j ∈ Finset.range N, i ^ j := by ring
      _ = 1 - i ^ N := by rw [h1, mul_neg_geom_sum]
  refine ⟨z * (s * ∑ j ∈ Finset.range N, i ^ j), ?_⟩
  set X := algebraMap (𝓞 F) F x
  set Y := algebraMap (𝓞 F) F y
  have hzF : algebraMap (𝓞 F) F z * Y = X * algebraMap (𝓞 F) F t := by
    simp only [X, Y, ← map_mul, hz]
  have httF : algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F (s * ∑ j ∈ Finset.range N, i ^ j) =
      1 - algebraMap (𝓞 F) F (i ^ N) := by
    rw [← map_mul, htt, map_sub, map_one]
  have hZ : algebraMap (𝓞 F) F z = X * algebraMap (𝓞 F) F t / Y := eq_div_of_mul_eq hY hzF
  have key : X / Y - algebraMap (𝓞 F) F (z * (s * ∑ j ∈ Finset.range N, i ^ j)) =
      X / Y * algebraMap (𝓞 F) F (i ^ N) := by
    rw [map_mul, hZ]
    linear_combination (-(X / Y)) * httF
  rw [key, map_mul, valuation_of_algebraMap]
  have hIN : v.intValuation (i ^ N) ≤ WithZero.exp (-(N : ℤ)) :=
    (intValuation_le_pow_iff_mem v _ N).mpr (Ideal.pow_mem_pow hi N)
  exact (mul_le_of_le_one_left' hk).trans hIN
end Formalism.L2.S.Pv.PsiTrCore
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.PsiTrCore
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.S.Pv.PsiTrCore
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (a w : v.adicCompletion F)
    (ha : Valued.v a ≤ 1) (hw : w ≠ 0) (hw1 : Valued.v w ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (a - algebraMap F (v.adicCompletion F) (r : F)) < Valued.v w := by
  have hw0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).mpr hw
  obtain ⟨N, hN⟩ : ∃ N : ℕ, WithZero.exp (-(N : ℤ)) < Valued.v w := by
    refine ⟨(-(Valued.v w).log).toNat + 1, ?_⟩
    conv_rhs => rw [← WithZero.exp_log hw0]
    rw [WithZero.exp_lt_exp]
    omega
  have hU : IsOpen {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} := by
    have h := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict w)).preimage
      (continuous_id.sub continuous_const : Continuous fun y : v.adicCompletion F ↦ y - a)
    have e : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} =
        (fun y : v.adicCompletion F ↦ y - a) ⁻¹'
          {x | Valued.v.restrict x < Valued.v.restrict w} := by
      ext y
      exact (Valuation.restrict_lt_iff (R := v.adicCompletion F) Valued.v).symm
    rw [e]
    exact h
  have hs : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} ∈ nhds a := by
    refine hU.mem_nhds ?_
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_lt_iff.mpr hw0
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F v).mem_nhds hs
  simp only [Set.mem_setOf_eq] at hk
  have hak : Valued.v (a - algebraMap F (v.adicCompletion F) k) < Valued.v w := by
    rwa [Valuation.map_sub_swap]
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) k = a - (a - algebraMap F (v.adicCompletion F) k) := by
      ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le ha (hak.le.trans hw1))
  obtain ⟨r, hr⟩ := exists_integer_approx_valuation v k hk1 N
  refine ⟨r, ?_⟩
  have e : a - algebraMap F (v.adicCompletion F) (r : F) =
      (a - algebraMap F (v.adicCompletion F) k) +
        algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F r) := by
    have hr' : (r : F) = algebraMap (𝓞 F) F r := rfl
    rw [map_sub, ← hr']
    ring
  rw [e]
  refine Valuation.map_add_lt _ hak ?_
  rw [valued_algebraMap]
  exact lt_of_le_of_lt hr hN
end Formalism.L2.S.Pv.PsiTrCore
