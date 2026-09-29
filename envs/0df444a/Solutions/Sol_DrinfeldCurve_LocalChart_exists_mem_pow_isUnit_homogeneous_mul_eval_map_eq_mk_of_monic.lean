-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_mem_pow_isUnit_homogeneous_mul_eval_map_eq_mk_of_monic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/89c0d7b4-83b2-5c74-a6d9-c06ddcea6e86

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_mul_eval_map_eq_mk_of_monic

set_option autoImplicit false

open IsLocalRing

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "LocalChart.drinfeldForm mk mk_surjective relation"
namespace LocalChart
p2m_export "DrinfeldCurve.LocalChart" "drinfeldForm"
namespace DistPolyPureAux
p2m_open "DrinfeldCurve.LocalChart DrinfeldCurve"

open MvPowerSeries

theorem isUnit_constantCoeff_of_isUnit_mk {W : Type} [CommRing W] [IsLocalRing W] (π : W) (hπ : π ∈ maximalIdeal W)
    (f u v : MvPowerSeries (Fin 2) W) (hf : constantCoeff f = 0) (g : MvPowerSeries (Fin 2) W)
    (hg : IsUnit (Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) g)) : IsUnit (constantCoeff g) := by
  set φ : MvPowerSeries (Fin 2) W →+* ResidueField W := (residue W).comp constantCoeff with hφ
  have hker : ∀ a ∈ Ideal.span {C π * v - f * u}, φ a = 0 := by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [hφ, RingHom.coe_comp, Function.comp_apply, map_mul, map_sub, constantCoeff_C, hf, zero_mul, sub_zero]
    rw [(residue_eq_zero_iff π).mpr hπ]; simp
  have h1 := hg.map (Ideal.Quotient.lift _ φ hker)
  rw [Ideal.Quotient.lift_mk] at h1
  simp only [hφ, RingHom.coe_comp, Function.comp_apply] at h1
  by_contra hnu
  have hm : constantCoeff g ∈ maximalIdeal W := (mem_maximalIdeal _).mpr hnu
  rw [(residue_eq_zero_iff _).mpr hm] at h1
  exact not_isUnit_zero h1

theorem coeff_drinfeldForm_zero {W : Type} [CommRing W] (q : ℕ) [Fact q.Prime] :
    coeff (0 : Fin 2 →₀ ℕ) (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
  classical
  have e1 : (X 0 : MvPowerSeries (Fin 2) W) * X 1 ^ q = monomial (Finsupp.single 0 1 + Finsupp.single 1 q) 1 := by
    rw [X_pow_eq, X_def, monomial_mul_monomial, one_mul]
  have e2 : (X 0 : MvPowerSeries (Fin 2) W) ^ q * X 1 = monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
    rw [X_pow_eq, X_def, monomial_mul_monomial, one_mul]
  unfold DrinfeldCurve.LocalChart.drinfeldForm
  rw [e1, e2, map_sub, coeff_monomial, coeff_monomial, if_neg, if_neg, sub_zero]
  · intro hn; have := congrArg (fun n : Fin 2 →₀ ℕ => n 1) hn; simp at this
  · intro hn; have := congrArg (fun n : Fin 2 →₀ ℕ => n 0) hn; simp at this

theorem drinfeldForm_mem_pow {W : Type} [CommRing W] (q : ℕ) [Fact q.Prime] :
    DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 1) := by
  have h0 : (X 0 : MvPowerSeries (Fin 2) W) ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} := Ideal.subset_span (by simp)
  have h1 : (X 1 : MvPowerSeries (Fin 2) W) ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} := Ideal.subset_span (by simp)
  unfold DrinfeldCurve.LocalChart.drinfeldForm
  refine Ideal.sub_mem _ ?_ ?_
  · rw [pow_succ']; exact Ideal.mul_mem_mul h0 (Ideal.pow_mem_pow h1 q)
  · rw [pow_succ]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow h0 q) h1

theorem sum_coeff_eq_zero_of_mem_pow {W : Type} [CommRing W] (N e : ℕ) (hNe : N < e) (T : MvPowerSeries (Fin 2) W)
    (hT : T ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ e) (a b : W) :
    (∑ i ∈ Finset.range (N + 1),
        coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (N - i)) T * a ^ i * b ^ (N - i)) = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have := (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W e T).mp hT
    (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (N - i)) (by simp; omega)
  rw [this, zero_mul, zero_mul]

end DrinfeldCurve.LocalChart.DistPolyPureAux

open DrinfeldCurve.LocalChart.DistPolyPureAux in
theorem solution
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π})
    (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}) (hs : IsUnit s)
    (d k : ℕ) (h : MvPowerSeries (Fin 2) W)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d)
    (hunit : ∀ a b : W, (a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W) →
        a ^ q * b - a * b ^ q ∈ maximalIdeal W →
        IsUnit (∑ i ∈ Finset.range (d + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) h
              * a ^ i * b ^ (d - i)))
    (P : Polynomial W) (hPm : P.Monic) (hPk : P.natDegree = k)
    (hPc : ∀ i < k, P.coeff i ∈ maximalIdeal W ^ (((k - i) * d) / (q + 1) + 1)) :
    ∃ (h' : MvPowerSeries (Fin 2) W)
      (_ : h' ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (d * k)),
      (∀ a b : W, (a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W) →
          a ^ q * b - a * b ^ q ∈ maximalIdeal W →
          IsUnit (∑ i ∈ Finset.range (d * k + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) h'
              * a ^ i * b ^ (d * k - i))) ∧
      s * (P.map ((Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u})).comp
            (MvPowerSeries.C : W →+* MvPowerSeries (Fin 2) W))).eval
          (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) h) =
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) h' := by
  classical
  let I : Ideal (MvPowerSeries (Fin 2) W) := Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}
  let J : Ideal (MvPowerSeries (Fin 2) W) := Ideal.span {MvPowerSeries.C π * v - f * u}
  have hπm : π ∈ maximalIdeal W := by rw [hπ]; exact Ideal.mem_span_singleton_self π
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    have h1 := (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W (q + 2) _).mp hf 0 (by simp)
    rw [map_sub, coeff_drinfeldForm_zero q, sub_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
    exact h1
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective s
  have hG' : Ideal.Quotient.mk J G = s := hG
  have hGu : IsUnit (MvPowerSeries.constantCoeff G) :=
    isUnit_constantCoeff_of_isUnit_mk π hπm f u v hf0 G (by rw [hG]; exact hs)

  have hfI : f ∈ I ^ (q + 1) := by
    have : f = (f - DrinfeldCurve.LocalChart.drinfeldForm q W) + DrinfeldCurve.LocalChart.drinfeldForm q W := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ _) hf) (drinfeldForm_mem_pow q)

  obtain ⟨vU, hvU⟩ := hv
  set vinv : MvPowerSeries (Fin 2) W := ((vU⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) with hvinv
  have hvvinv : v * vinv = 1 := by rw [← hvU, hvinv, Units.mul_inv]
  have hCπ : Ideal.Quotient.mk J (MvPowerSeries.C π) = Ideal.Quotient.mk J (f * u * vinv) := by
    have h0 : Ideal.Quotient.mk J (MvPowerSeries.C π * v - f * u) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [map_sub, sub_eq_zero, map_mul, map_mul] at h0
    calc Ideal.Quotient.mk J (MvPowerSeries.C π)
        = Ideal.Quotient.mk J (MvPowerSeries.C π) * Ideal.Quotient.mk J (v * vinv) := by rw [hvvinv, map_one, mul_one]
      _ = Ideal.Quotient.mk J f * Ideal.Quotient.mk J u * Ideal.Quotient.mk J vinv := by rw [map_mul, ← mul_assoc, h0]
      _ = Ideal.Quotient.mk J (f * u * vinv) := by rw [map_mul, map_mul]

  have hcoef : ∀ i, i < k → ∃ w : W, P.coeff i = π ^ (((k - i) * d) / (q + 1) + 1) * w := by
    intro i hi
    have := hPc i hi
    rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  choose w hw using hcoef

  let t : ℕ → MvPowerSeries (Fin 2) W := fun i =>
    if hi : i < k then G * ((f * u * vinv) ^ (((k - i) * d) / (q + 1) + 1) * MvPowerSeries.C (w i hi)) * h ^ i else 0
  have ht_mem : ∀ i, i < k → t i ∈ I ^ (d * k + 1) := by
    intro i hi
    simp only [t, dif_pos hi]
    have hm : (k - i) * d < (q + 1) * (((k - i) * d) / (q + 1) + 1) := Nat.lt_mul_div_succ _ (Nat.succ_pos q)
    have hfu : (f * u * vinv) ^ (((k - i) * d) / (q + 1) + 1) * MvPowerSeries.C (w i hi) ∈
        I ^ ((q + 1) * (((k - i) * d) / (q + 1) + 1)) := by
      refine Ideal.mul_mem_right _ _ ?_
      rw [pow_mul]
      exact Ideal.pow_mem_pow (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hfI)) _
    have hhi : h ^ i ∈ I ^ (d * i) := by rw [pow_mul]; exact Ideal.pow_mem_pow hh i
    have hprod : G * ((f * u * vinv) ^ (((k - i) * d) / (q + 1) + 1) * MvPowerSeries.C (w i hi)) * h ^ i ∈
        I ^ ((q + 1) * (((k - i) * d) / (q + 1) + 1) + d * i) := by
      rw [pow_add]; exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hfu) hhi
    refine Ideal.pow_le_pow_right ?_ hprod
    have : d * k = (k - i) * d + d * i := by
      rw [Nat.sub_mul, Nat.mul_comm d i, Nat.mul_comm d k, Nat.sub_add_cancel (Nat.mul_le_mul_right _ hi.le)]
    omega
  let T : MvPowerSeries (Fin 2) W := ∑ i ∈ Finset.range k, t i
  have hT_mem : T ∈ I ^ (d * k + 1) :=
    Ideal.sum_mem _ fun i hi => ht_mem i (Finset.mem_range.mp hi)

  have hGhk := MvPowerSeries.mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow W G h d k hh
  refine ⟨G * h ^ k + T, Ideal.add_mem _ (hGhk 0 0).1 (Ideal.pow_le_pow_right (Nat.le_succ _) hT_mem), ?_, ?_⟩
  · intro a b hab hdir
    have hsplit : (∑ i ∈ Finset.range (d * k + 1),
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) (G * h ^ k + T)
          * a ^ i * b ^ (d * k - i)) =
        (∑ i ∈ Finset.range (d * k + 1),
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) (G * h ^ k)
            * a ^ i * b ^ (d * k - i)) +
        (∑ i ∈ Finset.range (d * k + 1),
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) T
            * a ^ i * b ^ (d * k - i)) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_add]; ring
    rw [hsplit, sum_coeff_eq_zero_of_mem_pow (d * k) (d * k + 1) (Nat.lt_succ_self _) T hT_mem a b, add_zero,
      (hGhk a b).2]
    exact hGu.mul ((hunit a b hab hdir).pow k)
  ·
    have hmonic : P.coeff k = 1 := by rw [← hPk]; exact hPm.coeff_natDegree
    have e1 : s * (Ideal.Quotient.mk J h) ^ k = Ideal.Quotient.mk J (G * h ^ k) := by rw [← hG', ← map_pow, ← map_mul]
    have e2 : ∀ i ∈ Finset.range k,
        s * (((Ideal.Quotient.mk J).comp (MvPowerSeries.C : W →+* MvPowerSeries (Fin 2) W)) (P.coeff i) *
          (Ideal.Quotient.mk J h) ^ i) = Ideal.Quotient.mk J (t i) := by
      intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      simp only [t, dif_pos hi']
      rw [RingHom.comp_apply, hw i hi', map_mul MvPowerSeries.C, map_pow MvPowerSeries.C, map_mul (Ideal.Quotient.mk J),
        map_pow (Ideal.Quotient.mk J), hCπ, ← hG']
      simp only [← map_pow, ← map_mul]
      congr 1; ring
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, hPk, Finset.sum_range_succ, hmonic, map_one, one_mul, mul_add,
      Finset.mul_sum, Finset.sum_congr rfl e2, e1, ← map_sum, ← map_add, add_comm]

end S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_mul_eval_map_eq_mk_of_monic
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_mul_eval_map_eq_mk_of_monic (solution)
