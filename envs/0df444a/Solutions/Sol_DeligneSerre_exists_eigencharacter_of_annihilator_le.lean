-- Prove2me | solution 1 for DeligneSerre.exists_eigencharacter_of_annihilator_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1fdc8319-f32a-5b0b-9efc-a9c6e7458df3

import Theorems.Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_exists_eigencharacter_of_annihilator_le

set_option autoImplicit false

namespace DeligneSerre
p2m_export "DeligneSerre" "exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul"
p2m_open "DeligneSerre"

private theorem exists_isMaximal_comap_eq_of_ker_le'
    (T : Type*) [CommRing T] (𝔪 : Ideal T) [𝔪.IsMaximal]
    (φ : T →+* integralClosure ℤ ℂ) (hφ : RingHom.ker φ ≤ 𝔪) :
    ∃ 𝔪' : Ideal (integralClosure ℤ ℂ), 𝔪'.IsMaximal ∧ 𝔪'.comap φ = 𝔪 := by
  letI : Algebra T (integralClosure ℤ ℂ) := φ.toAlgebra
  haveI : Algebra.IsIntegral T (integralClosure ℤ ℂ) := ⟨fun x => by
    obtain ⟨p, hp, hpx⟩ := integralClosure.isIntegral (R := ℤ) (A := ℂ) x
    refine ⟨p.map (algebraMap ℤ T), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra,
      RingHom.ext_int (φ.comp (algebraMap ℤ T)) (algebraMap ℤ (integralClosure ℤ ℂ))]
    exact hpx⟩
  obtain ⟨𝔪', h𝔪'max, h𝔪'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := integralClosure ℤ ℂ) 𝔪 (by rwa [RingHom.algebraMap_toAlgebra])
  exact ⟨𝔪', h𝔪'max, by rwa [RingHom.algebraMap_toAlgebra] at h𝔪'⟩

theorem exists_eigencharacter_of_annihilator_le_impl
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T ℂ V] [Module.Finite ℤ T]
    (𝔪 : Ideal T) [h𝔪 : 𝔪.IsMaximal] (hsupp : Module.annihilator T V ≤ 𝔪) :
    ∃ (χ : T →+* integralClosure ℤ ℂ) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      𝔪'.IsMaximal ∧ 𝔪'.comap χ = 𝔪 ∧
      ∃ x : V, x ≠ 0 ∧ ∀ t : T, t • x = ((χ t : integralClosure ℤ ℂ) : ℂ) • x := by
  classical
  set I : Ideal T := Module.annihilator T V with hI

  letI : Module (T ⧸ I) V := Module.quotientAnnihilator
  have hmk : ∀ (t : T) (v : V), Ideal.Quotient.mk I t • v = t • v := fun t v => rfl
  haveI : SMulCommClass (T ⧸ I) ℂ V := ⟨fun t' c v => by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
    rw [hmk, hmk, smul_comm]⟩
  haveI : FaithfulSMul (T ⧸ I) V := ⟨fun {t₁' t₂'} h => by
    obtain ⟨t₁, rfl⟩ := Ideal.Quotient.mk_surjective t₁'
    obtain ⟨t₂, rfl⟩ := Ideal.Quotient.mk_surjective t₂'
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I)]
    refine Module.mem_annihilator.mpr fun v => ?_
    rw [sub_smul, sub_eq_zero, ← hmk, ← hmk]
    exact h v⟩

  set 𝔪b : Ideal (T ⧸ I) := 𝔪.map (Ideal.Quotient.mk I) with h𝔪b
  have hcomap𝔪 : 𝔪b.comap (Ideal.Quotient.mk I) = 𝔪 := by
    rw [h𝔪b, Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hsupp]
  haveI h𝔪bmax : 𝔪b.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective h𝔪 with h | h
    · exact absurd (by rw [← hcomap𝔪, h𝔪b, h, Ideal.comap_top]) h𝔪.ne_top
    · exact h

  obtain ⟨𝔭, h𝔭min, h𝔭le⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (T ⧸ I))) (J := 𝔪b) bot_le
  obtain ⟨χ₀, hker₀, x, hx0, -, -, heig⟩ :=
    exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul (K := ℂ) (V := V) (T := T ⧸ I) h𝔭min

  let χℂ : T →+* ℂ := χ₀.comp (Ideal.Quotient.mk I)
  haveI : Algebra.IsIntegral ℤ T := Algebra.IsIntegral.of_finite ℤ T
  have hint : ∀ t : T, χℂ t ∈ integralClosure ℤ ℂ := fun t =>
    show IsIntegral ℤ (χℂ t) from (Algebra.IsIntegral.isIntegral (R := ℤ) t).map χℂ.toIntAlgHom
  let χ : T →+* integralClosure ℤ ℂ := χℂ.codRestrict (integralClosure ℤ ℂ) hint
  have hχ : ∀ t : T, ((χ t : integralClosure ℤ ℂ) : ℂ) = χ₀ (Ideal.Quotient.mk I t) :=
    fun _ => rfl
  have hkerχ : RingHom.ker χ ≤ 𝔪 := by
    intro t ht
    rw [RingHom.mem_ker, Subtype.ext_iff, hχ] at ht
    have h𝔭t : Ideal.Quotient.mk I t ∈ 𝔭 := by rw [← hker₀]; exact ht
    rw [← hcomap𝔪, Ideal.mem_comap]
    exact h𝔭le h𝔭t

  obtain ⟨𝔪', h𝔪'max, h𝔪'comap⟩ := exists_isMaximal_comap_eq_of_ker_le' T 𝔪 χ hkerχ
  refine ⟨χ, 𝔪', h𝔪'max, h𝔪'comap, x, hx0, fun t => ?_⟩
  calc t • x = Ideal.Quotient.mk I t • x := (hmk t x).symm
    _ = χ₀ (Ideal.Quotient.mk I t) • x := heig _
    _ = ((χ t : integralClosure ℤ ℂ) : ℂ) • x := by rw [hχ]

end DeligneSerre

theorem solution
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T ℂ V] [Module.Finite ℤ T]
    (𝔪 : Ideal T) [h𝔪 : 𝔪.IsMaximal] (hsupp : Module.annihilator T V ≤ 𝔪) :
    ∃ (χ : T →+* integralClosure ℤ ℂ) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      𝔪'.IsMaximal ∧ 𝔪'.comap χ = 𝔪 ∧
      ∃ x : V, x ≠ 0 ∧ ∀ t : T, t • x = ((χ t : integralClosure ℤ ℂ) : ℂ) • x :=
  DeligneSerre.exists_eigencharacter_of_annihilator_le_impl (𝔪 := 𝔪) (hsupp := hsupp)

#print axioms solution

end S_DeligneSerre_exists_eigencharacter_of_annihilator_le
end P2MW
export P2MW.S_DeligneSerre_exists_eigencharacter_of_annihilator_le (solution)
