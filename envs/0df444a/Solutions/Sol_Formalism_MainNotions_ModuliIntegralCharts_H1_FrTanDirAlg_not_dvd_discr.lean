-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.not_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:58.397893+00:00
-- url     : https://prove2.me/submissions/7b9eb111-e9c3-401d-8ad5-4ec2ccd2dc15

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
open NumberField Matrix
variable (E : Type) [Field E] [NumberField E]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
theorem _root_.solution (g : ℕ) (hg : g.Prime)
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup) :
    ¬ (g : ℤ) ∣ discr E := by
  classical
  intro h
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hgN : g ∣ Ideal.absNorm D := by
    rw [hD, NumberField.absNorm_differentIdeal E (𝓞 E)]
    exact Int.natCast_dvd.mp h

  obtain ⟨P, hPmem, hgP⟩ :
      ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, g ∣ Ideal.absNorm P := by
    have hprod := UniqueFactorizationMonoid.prod_normalizedFactors hD0
    rw [← associated_iff_eq.mp hprod, map_multiset_prod] at hgN
    obtain ⟨n, hn, hgn⟩ := (Nat.prime_iff.mp hg).exists_mem_multiset_dvd hgN
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hn
    exact ⟨P, hP, hgn⟩
  have hPp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hPmem
  have hP0 : P ≠ ⊥ := hPp.ne_zero
  haveI hPI : P.IsPrime := Ideal.isPrime_of_prime hPp
  have hPD : P ∣ D := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPmem

  have hN0 : Ideal.absNorm P ≠ 0 := fun h0 => hP0 (Ideal.absNorm_eq_zero_iff.mp h0)
  have hU0 : P.under ℤ ≠ ⊥ := by
    intro h0
    have hm : ((Ideal.absNorm P : ℕ) : ℤ) ∈ P.under ℤ := by
      change algebraMap ℤ (𝓞 E) ((Ideal.absNorm P : ℕ) : ℤ) ∈ P
      rw [map_natCast]
      exact Ideal.absNorm_mem P
    rw [h0, Ideal.mem_bot] at hm
    exact hN0 (by exact_mod_cast hm)
  have hqp : Prime (Submodule.IsPrincipal.generator (P.under ℤ)) :=
    Submodule.IsPrincipal.prime_generator_of_isPrime (P.under ℤ) hU0
  have hUq : P.under ℤ = Ideal.span {Submodule.IsPrincipal.generator (P.under ℤ)} :=
    (Ideal.span_singleton_generator (P.under ℤ)).symm
  haveI hLO : P.LiesOver (Ideal.span {Submodule.IsPrincipal.generator (P.under ℤ)}) := ⟨hUq.symm⟩
  have hnorm := Ideal.absNorm_eq_pow_inertiaDeg P hqp
  have hgq : g = (Submodule.IsPrincipal.generator (P.under ℤ)).natAbs := by
    rw [hnorm] at hgP
    have hq' := Int.prime_iff_natAbs_prime.mp hqp
    exact (Nat.prime_dvd_prime_iff_eq hg hq').mp (hg.dvd_of_dvd_pow hgP)
  have hspan : Ideal.span {(g : ℤ)} = P.under ℤ := by
    rw [hUq, hgq, Ideal.span_singleton_eq_span_singleton]
    exact (Int.associated_natAbs _).symm
  haveI : P.LiesOver (Ideal.span {(g : ℤ)}) := ⟨hspan⟩

  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(g : ℤ)}) = Ideal.span {(g : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hI0 : Ideal.span {(g : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg.ne_zero
  have hgP' : P ∣ Ideal.span {(g : 𝓞 E)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    have hm : (g : ℤ) ∈ P.under ℤ := hspan ▸ Ideal.mem_span_singleton_self _
    change algebraMap ℤ (𝓞 E) (g : ℤ) ∈ P at hm
    rwa [map_natCast] at hm
  have hPnf : P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)}) := by
    obtain ⟨Q, hQ, hPQ⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hI0 hPp.irreducible hgP'
    rwa [associated_iff_eq.mp hPQ]
  have he : P.ramificationIdx ℤ = 1 := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(g : ℤ)}) P
      (hmap ▸ hI0), hmap]
    exact Multiset.count_eq_one_of_mem hnd hPnf
  have hunr : Algebra.IsUnramifiedAt ℤ P := Algebra.isUnramifiedAt_iff_of_isDedekindDomain.mpr he
  exact (dvd_differentIdeal_iff.mp hPD) hunr
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
