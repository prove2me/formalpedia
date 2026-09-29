-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_sub_C_eq_mk_of_sub_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a5009bb5-e48c-5770-ad5b-77ac15f9ab11

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_sub_C_eq_mk_of_sub_eq_pow_mul

set_option autoImplicit false

open MvPowerSeries

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "LocalChart.drinfeldForm mk relation"
namespace LocalChart
p2m_export "DrinfeldCurve.LocalChart" "drinfeldForm"
p2m_open "DrinfeldCurve.LocalChart DrinfeldCurve"

def lowVanish (W : Type*) [CommRing W] (k : ℕ) : Ideal (MvPowerSeries (Fin 2) W) where
  carrier := {φ | ∀ n : Fin 2 →₀ ℕ, n.degree < k → coeff n φ = 0}
  zero_mem' := fun n _ => by simp
  add_mem' := fun {a b} ha hb n hn => by simp [ha n hn, hb n hn]
  smul_mem' := fun r {a} ha n hn => by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpn : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have : p.2.degree < k := by
      have := congrArg Finsupp.degree hpn; rw [map_add] at this; omega
    rw [ha p.2 this, mul_zero]

theorem mem_lowVanish {W : Type*} [CommRing W] (k : ℕ) (φ : MvPowerSeries (Fin 2) W) :
    φ ∈ lowVanish W k ↔ ∀ n : Fin 2 →₀ ℕ, n.degree < k → coeff n φ = 0 := Iff.rfl

theorem lowVanish_mul_le {W : Type*} [CommRing W] (k l : ℕ) :
    lowVanish W k * lowVanish W l ≤ lowVanish W (k + l) := by
  classical
  refine Ideal.mul_le.mpr fun a ha b hb n hn => ?_
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpn : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hdeg : p.1.degree + p.2.degree = n.degree := by rw [← map_add, hpn]
  by_cases h1 : p.1.degree < k
  · rw [ha p.1 h1, zero_mul]
  · have : p.2.degree < l := by omega
    rw [hb p.2 this, mul_zero]

theorem span_X_le_lowVanish (W : Type*) [CommRing W] :
    Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ≤ lowVanish W 1 := by
  classical
  rw [Ideal.span_le]
  rintro φ (rfl | rfl) <;>
  · intro n hn
    have hn0 : n = 0 := (Finsupp.degree_eq_zero_iff n).mp (by omega)
    subst hn0
    rw [coeff_X]; simp [eq_comm, Finsupp.single_eq_zero]

theorem span_X_pow_le_lowVanish (W : Type*) [CommRing W] (k : ℕ) :
    (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ k ≤ lowVanish W k := by
  induction k with
  | zero => intro φ _ n hn; omega
  | succ k ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (span_X_le_lowVanish W)).trans (lowVanish_mul_le k 1)

end DrinfeldCurve.LocalChart

open _root_.DrinfeldCurve.LocalChart _root_.P2MW.S_DrinfeldCurve_LocalChart_exists_sub_C_eq_mk_of_sub_eq_pow_mul.DrinfeldCurve.LocalChart in
theorem solution
    (q : ℕ) {W : Type} [CommRing W]
    (c : W) (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 2))
    (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {C c * v - f * u})
    (a₀ a w : W) (N : ℕ) (ha : a₀ - a = c ^ N * w)
    (e₀ : ℕ) (hN : e₀ + 1 ≤ N * (q + 1))
    (h : MvPowerSeries (Fin 2) W)
    (hh : h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ e₀)
    (hs : s - Ideal.Quotient.mk _ (C a₀) = Ideal.Quotient.mk _ h) :
    ∃ h' : MvPowerSeries (Fin 2) W,
      h' ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ e₀ ∧
      (∀ i : ℕ, i ≤ e₀ → coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h' =
        coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h) ∧
      s - Ideal.Quotient.mk _ (C a) = Ideal.Quotient.mk _ h' := by
  classical
  obtain ⟨vU, rfl⟩ := hv
  set J : Ideal (MvPowerSeries (Fin 2) W) := Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} with hJ

  set g : MvPowerSeries (Fin 2) W := f * u * ((vU⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) with hg
  have hcg : C c - g ∈ (Ideal.span {C c * (vU : MvPowerSeries (Fin 2) W) - f * u}) := by
    have : C c - g = (C c * (vU : MvPowerSeries (Fin 2) W) - f * u) * ((vU⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) := by
      rw [sub_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hfJ : f ∈ J ^ (q + 1) := by
    have hD : DrinfeldCurve.LocalChart.drinfeldForm q W ∈ J ^ (q + 1) := by
      unfold DrinfeldCurve.LocalChart.drinfeldForm
      have hX0 : (X 0 : MvPowerSeries (Fin 2) W) ∈ J := Ideal.subset_span (by simp)
      have hX1 : (X 1 : MvPowerSeries (Fin 2) W) ∈ J := Ideal.subset_span (by simp)
      refine Ideal.sub_mem _ ?_ ?_
      · rw [pow_succ']; exact Ideal.mul_mem_mul hX0 (Ideal.pow_mem_pow hX1 q)
      · rw [pow_succ]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hX0 q) hX1
    have : f = (f - DrinfeldCurve.LocalChart.drinfeldForm q W) + DrinfeldCurve.LocalChart.drinfeldForm q W := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) hf) hD
  have hgJ : g ∈ J ^ (q + 1) := by
    rw [hg, mul_assoc]; exact Ideal.mul_mem_right _ _ hfJ
  have hgN : g ^ N * C w ∈ J ^ (e₀ + 1) := by
    have : g ^ N ∈ J ^ (N * (q + 1)) := by rw [mul_comm, pow_mul]; exact Ideal.pow_mem_pow hgJ N
    exact Ideal.pow_le_pow_right hN (Ideal.mul_mem_right _ _ this)
  refine ⟨h + g ^ N * C w, ?_, ?_, ?_⟩
  · exact Ideal.add_mem _ hh (Ideal.pow_le_pow_right (Nat.le_succ e₀) hgN)
  · intro i hi
    rw [map_add]
    have : coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) (g ^ N * C w) = 0 := by
      apply span_X_pow_le_lowVanish W (e₀ + 1) hgN
      rw [map_add, Finsupp.degree_single, Finsupp.degree_single]; omega
    rw [this, add_zero]
  ·
    have h1 : s - Ideal.Quotient.mk (Ideal.span {C c * (vU : MvPowerSeries (Fin 2) W) - f * u}) (C a) =
        (s - Ideal.Quotient.mk (Ideal.span {C c * (vU : MvPowerSeries (Fin 2) W) - f * u}) (C a₀)) + Ideal.Quotient.mk (Ideal.span {C c * (vU : MvPowerSeries (Fin 2) W) - f * u}) (C (a₀ - a)) := by
      rw [map_sub (C : W →+* _), map_sub]; ring
    rw [h1, hs, ← map_add]
    apply (Ideal.Quotient.eq).mpr
    rw [ha, map_mul, map_pow]

    have : h + (C c) ^ N * C w - (h + g ^ N * C w) = ((C c) ^ N - g ^ N) * C w := by ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (by
      obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow (C c) g N
      rw [hr]; exact Ideal.mul_mem_right _ _ hcg)

end S_DrinfeldCurve_LocalChart_exists_sub_C_eq_mk_of_sub_eq_pow_mul
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_sub_C_eq_mk_of_sub_eq_pow_mul (solution)
