-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.idealConjugateFactorizationUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:22.243659+00:00
-- url     : https://prove2.me/submissions/5fefc753-2bbb-4049-8fac-00f6cefb4184

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_nf_map
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
open Ideal UniqueFactorizationMonoid
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
theorem _root_.solution {S : Type*} [CommRing S] [IsDedekindDomain S] (D : Ideal S) (hD0 : D ≠ ⊥)
    (f : Ideal S ≃* Ideal S) (hfD : f D = D) (p : Ideal S → Prop)
    (hp : ∀ P ∈ normalizedFactors D, (p (f P) ↔ ¬ p P)) :
    ∃ B : Ideal S, D = B * f B ∧ (∀ P : Ideal S, P.IsPrime → P ∣ B → p P) ∧ B ⊔ f B = ⊤ ∧
      (∀ g : Ideal S ≃* Ideal S, g D = D → (∀ P ∈ normalizedFactors D, (p (g P) ↔ p P)) → g B = B) ∧
      ∀ B' : Ideal S, D = B' * f B' → (∀ P : Ideal S, P.IsPrime → P ∣ B' → p P) → B' = B := by
  classical
  set F := normalizedFactors D with hF
  have hprime : ∀ P ∈ F, Prime P := fun P hP => prime_of_normalized_factor P hP
  have hFf : ∀ g : Ideal S ≃* Ideal S, g D = D → F.map g = F := by
    intro g hg
    rw [hF, ← nf_map D hD0 g, hg]
  have hmax : ∀ P ∈ F, P.IsMaximal := by
    intro P hP
    have hp := hprime P hP
    exact Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hp)
      (by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero)
  refine ⟨(F.filter p).prod, ?_, ?_, ?_, ?_, ?_⟩
  · have hsplit : F.filter (fun P => ¬ p P) = (F.filter p).map f := by
      conv_lhs => rw [← hFf f hfD]
      rw [Multiset.filter_map]
      congr 1
      apply Multiset.filter_congr
      intro P hP
      simp only [Function.comp_apply, hp P hP, not_not]
    calc D = F.prod := (Ideal.prod_normalizedFactors_eq_self hD0).symm
      _ = (F.filter p).prod * (F.filter (fun P => ¬ p P)).prod := by
          rw [← Multiset.prod_add, Multiset.filter_add_not]
      _ = _ := by rw [hsplit, map_multiset_prod]
  · intro P hP hdvd
    obtain ⟨Q, hQ, hQP⟩ := hP.multiset_prod_le.mp (Ideal.dvd_iff_le.mp hdvd)
    rw [Multiset.mem_filter] at hQ
    rw [← (hmax Q hQ.1).eq_of_le hP.ne_top hQP]
    exact hQ.2
  · by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hMp := hM.isPrime
    have h1 : (F.filter p).prod ≤ M := le_trans le_sup_left hle
    have h2 : f (F.filter p).prod ≤ M := le_trans le_sup_right hle
    rw [map_multiset_prod] at h2
    obtain ⟨P, hP, hPM⟩ := hMp.multiset_prod_le.mp h1
    obtain ⟨Q, hQ, hQM⟩ := hMp.multiset_prod_le.mp h2
    obtain ⟨P', hP', rfl⟩ := Multiset.mem_map.mp hQ
    rw [Multiset.mem_filter] at hP hP'
    have eqP : P = M := (hmax P hP.1).eq_of_le hM.ne_top hPM
    have hfP' : f P' ∈ F := by rw [← hFf f hfD]; exact Multiset.mem_map_of_mem f hP'.1
    have eqQ : f P' = M := (hmax _ hfP').eq_of_le hM.ne_top hQM
    have := (hp P' hP'.1).mp (by rw [eqQ, ← eqP]; exact hP.2)
    exact this hP'.2
  · intro g hg hpg
    rw [map_multiset_prod]
    congr 1
    conv_rhs => rw [← hFf g hg]
    rw [Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro P hP
    simp only [Function.comp_apply, hpg P hP]
  · intro B' hB' hpB'
    have hB0 : B' ≠ ⊥ := by
      rintro rfl
      apply hD0
      rw [hB', ← Ideal.zero_eq_bot, zero_mul]
    have hfB0 : f B' ≠ ⊥ := by
      intro h0
      apply hD0
      rw [hB', h0, ← Ideal.zero_eq_bot, mul_zero]
    have hsum : F = normalizedFactors B' + (normalizedFactors B').map f := by
      rw [hF, hB', normalizedFactors_mul hB0 hfB0, nf_map B' hB0 f]
    have hall : ∀ P ∈ normalizedFactors B', p P := by
      intro P hP
      exact hpB' P (Ideal.isPrime_of_prime (prime_of_normalized_factor P hP))
        (dvd_of_mem_normalizedFactors hP)
    have e1 : (normalizedFactors B').filter p = normalizedFactors B' :=
      Multiset.filter_eq_self.mpr hall
    have e2 : ((normalizedFactors B').map f).filter p = 0 := by
      rw [Multiset.filter_eq_nil]
      intro Q hQ
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hQ
      have hPF : P ∈ F := by rw [hsum]; exact Multiset.mem_add.mpr (Or.inl hP)
      rw [hp P hPF, not_not]
      exact hall P hP
    rw [hsum, Multiset.filter_add, e1, e2, add_zero, Ideal.prod_normalizedFactors_eq_self hB0]
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
