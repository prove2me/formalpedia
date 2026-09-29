-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.finite_and_finrank_kerAlgebra_varpi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/62347814-c657-5fab-9bf3-1e35a5e0edc2

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_finite_and_finrank_kerAlgebra_varpi
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

noncomputable section

namespace KerDegSol

open MvPowerSeries

variable {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

theorem constantCoeff_varpi (i : Fin 2) : constantCoeff (X₀.varpi i) = 0 :=
  X₀.isLawHom_varpi.1 i

theorem exists_eq_sum_X_pow_mul {R : Type*} [CommRing R] {σ : Type*} [DecidableEq σ] (p : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s < p) → coeff d f = 0) →
      ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s ^ p * q s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s < p then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s < p then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ^ p ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨q, hq⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update q s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t ^ p * Function.update q s q' t = ∑ t ∈ T, X t ^ p * q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hq, ← hq']
    ring

theorem subst_mem_span (g : MvPowerSeries (Fin 2) k) (hg : constantCoeff g = 0) :
    subst X₀.varpi g ∈ Ideal.span (Set.range X₀.varpi) := by
  classical
  have hs : HasSubst X₀.varpi := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
  obtain ⟨r, hr⟩ := exists_eq_sum_X_pow_mul (R := k) 1 Finset.univ g (fun d hd => by
    have hd0 : d = 0 := by
      ext s
      have := hd s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [hd0, coeff_zero_eq_constantCoeff_apply]
    exact hg)
  rw [hr, ← coe_substAlgHom hs, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, pow_one, coe_substAlgHom hs, subst_X hs s]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

theorem span_comp_le :
    Ideal.span (Set.range (X₀.varpi.comp X₀.varpi)) ≤ Ideal.span (Set.range X₀.varpi) := by
  apply Ideal.span_le.2
  rintro _ ⟨i, rfl⟩
  exact subst_mem_span X₀ (X₀.varpi i) (constantCoeff_varpi X₀ i)

theorem map_id (φ : Series k) : φ.map (RingHom.id k) = φ := by
  funext i
  simp [Series.map]

theorem finite_and_finrank_comp :
    Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X₀.varpi.comp X₀.varpi))) ∧
      Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X₀.varpi.comp X₀.varpi))) = q ^ 4 := by
  rw [X₀.varpi_comp_varpi]
  obtain ⟨hfin, -, hrank⟩ := X₀.hasHeight
  refine ⟨hfin, ?_⟩
  have := hrank k (RingHom.id k)
  rwa [map_id] at this

theorem finite : Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range X₀.varpi)) := by
  haveI := (finite_and_finrank_comp X₀).1
  exact Module.Finite.of_surjective
    (Ideal.Quotient.factorₐ k (span_comp_le X₀) :
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X₀.varpi.comp X₀.varpi))) →ₐ[k]
        (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range X₀.varpi))).toLinearMap
    (Ideal.Quotient.factor_surjective (span_comp_le X₀))

theorem finrank_eq : Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range X₀.varpi)) = q ^ 2 := by
  have hfin := finite X₀
  have h := (MvPowerSeries.finite_and_finrank_quotient_span_range_subst_eq_mul X₀.varpi X₀.varpi
    (constantCoeff_varpi X₀) (constantCoeff_varpi X₀) hfin hfin).2
  have h4 := (finite_and_finrank_comp X₀).2
  change Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range fun i => subst X₀.varpi (X₀.varpi i)))
    = q ^ 4 at h4
  rw [h4, show q ^ 4 = q ^ 2 * q ^ 2 by ring] at h
  exact (Nat.mul_self_inj.1 h.symm)

end KerDegSol

end

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) :
    Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range X₀.varpi)) ∧
      Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range X₀.varpi)) = q ^ 2 :=
  ⟨KerDegSol.finite X₀, KerDegSol.finrank_eq X₀⟩

end S_CerednikDrinfeld_SpecialFormalODModule_finite_and_finrank_kerAlgebra_varpi
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_finite_and_finrank_kerAlgebra_varpi (solution)
