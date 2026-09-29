-- Prove2me | solution 1 for FormalGroup.evalSeries_map_algebraMap_eq_subst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e49ad3af-5e9a-50fa-af06-6b0d53c12764

import Mathlib
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_evalSeries_map_algebraMap_eq_subst

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DW2N1

open Filter Topology

theorem X_pow_dvd_subst_sub_sum {T : Type*} [CommRing T] (g s : PowerSeries T) (hs : PowerSeries.constantCoeff s = 0) (N : ℕ) :
    (PowerSeries.X : PowerSeries T) ^ N ∣
      PowerSeries.subst s g - ∑ n ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff n g) * s ^ n := by
  classical
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  have hsX : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero' hs
  rw [map_sub, PowerSeries.coeff_subst' hsX, map_sum]
  have hvan : ∀ n, m < n → PowerSeries.coeff m (s ^ n) = 0 := by
    intro n hn
    apply PowerSeries.coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast hn) (PowerSeries.le_order_pow_of_constantCoeff_eq_zero n hs)
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (m + 1)) _ (by
      intro n hn
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hn
      simp only
      rw [hvan n (by omega), smul_zero])]
  rw [← Finset.sum_range_add_sum_Ico _ (show m + 1 ≤ N by omega)]
  have htail : ∑ n ∈ Finset.Ico (m + 1) N, PowerSeries.coeff m (PowerSeries.C (PowerSeries.coeff n g) * s ^ n) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_Ico] at hn
    rw [← PowerSeries.smul_eq_C_mul, map_smul, hvan n (by omega), smul_zero]
  rw [htail, add_zero, sub_eq_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← PowerSeries.smul_eq_C_mul, map_smul]

private theorem _root_.DW2N1.hasSum_eval₂ {R₀ : Type*} [CommRing R₀] [UniformSpace R₀] [DiscreteUniformity R₀]
    {A : Type*} [CommRing A] [Algebra R₀ A] (I : Ideal A) [IsAdicComplete I A]
    (f : PowerSeries R₀) (x : A) (hx : x ∈ I) :
    letI : WithIdeal A := ⟨I⟩
    HasSum (fun n : ℕ => algebraMap R₀ A (PowerSeries.coeff n f) * x ^ n) (PowerSeries.eval₂ (algebraMap R₀ A) x f) := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have ha : PowerSeries.HasEval x := (PowerSeries.hasEval_def x).mpr (WithIdeal.isTopologicallyNilpotent_of_mem hx)
  exact PowerSeries.hasSum_eval₂ hφ ha f

p2m_export "DW2N1" "hasSum_eval₂"
end DW2N1

open Filter Topology in

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (g s : PowerSeries T) (hs : PowerSeries.constantCoeff s = 0) :
    (letI : WithIdeal (PowerSeries T) := ⟨maximalIdeal (PowerSeries T)⟩;
      FormalGroup.evalSeries (PowerSeries.map (algebraMap T (PowerSeries T)) g) s) = PowerSeries.subst s g := by
  classical
  letI Wd : WithIdeal (PowerSeries T) := ⟨maximalIdeal (PowerSeries T)⟩
  haveI hcomp : IsAdicComplete (maximalIdeal (PowerSeries T)) (PowerSeries T) := MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := T)
  have hI : IsAdic (maximalIdeal (PowerSeries T)) := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp hcomp
  set 𝔪 := maximalIdeal (PowerSeries T) with h𝔪
  have hXm : (PowerSeries.X : PowerSeries T) ∈ 𝔪 := by
    rw [h𝔪, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hsm : s ∈ 𝔪 := by
    obtain ⟨s', hs'⟩ := (PowerSeries.X_dvd_iff).mpr hs
    rw [hs']; exact Ideal.mul_mem_right _ _ hXm

  have hsum := @DW2N1.hasSum_eval₂ (PowerSeries T) _ ⊥ inferInstance (PowerSeries T) _ _ 𝔪 hcomp
    (PowerSeries.map (algebraMap T (PowerSeries T)) g) s hsm
  have hlim1 : Tendsto (fun N => ∑ n ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff n g) * s ^ n) atTop
      (𝓝 (FormalGroup.evalSeries (PowerSeries.map (algebraMap T (PowerSeries T)) g) s)) := by
    have := hsum.tendsto_sum_nat
    simp only [PowerSeries.coeff_map, Algebra.algebraMap_self, RingHom.id_apply] at this
    exact this

  have hlim2 : Tendsto (fun N => ∑ n ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff n g) * s ^ n) atTop
      (𝓝 (PowerSeries.subst s g)) := by
    rw [(Ideal.hasBasis_nhds_adic 𝔪 (PowerSeries.subst s g)).tendsto_right_iff]
    intro n _
    refine Filter.eventually_atTop.mpr ⟨n, fun N hN => ?_⟩
    refine ⟨∑ m ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff m g) * s ^ m - PowerSeries.subst s g, ?_, by ring⟩
    obtain ⟨c, hc⟩ := DW2N1.X_pow_dvd_subst_sub_sum g s hs N
    have : ∑ m ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff m g) * s ^ m - PowerSeries.subst s g = -(PowerSeries.X ^ N * c) := by
      rw [← hc]; ring
    rw [SetLike.mem_coe, this]
    exact (𝔪 ^ n).neg_mem (Ideal.pow_le_pow_right hN (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hXm N)))
  exact tendsto_nhds_unique hlim1 hlim2

end S_FormalGroup_evalSeries_map_algebraMap_eq_subst
end P2MW
export P2MW.S_FormalGroup_evalSeries_map_algebraMap_eq_subst (solution)
