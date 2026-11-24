-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:43:45.873561+00:00
-- url     : https://prove2.me/submissions/92e1340f-a281-4435-aaf3-a699e8afc534

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
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
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
open Formalism.FrobeniusOrbits.Principal
namespace Formalism.FrobeniusOrbits.Principal
theorem _root_.solution {S : Type*} [CommRing S] [IsDedekindDomain S] (D : Ideal S) (hD0 : D ≠ ⊥)
    (f : Ideal S ≃* Ideal S) (hfD : f D = D) (hff : ∀ I, f (f I) = I)
    (hfix : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors D, f P ≠ P) :
    ∃ B : Ideal S, D = B * f B ∧ B ⊔ f B = ⊤ := by
  classical
  let r : Ideal S → Ideal S → Prop := WellOrderingRel
  set F := UniqueFactorizationMonoid.normalizedFactors D with hF
  have hprime : ∀ P ∈ F, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hprod : F.prod = D :=
    associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hD0)
  have hprimeMap : ∀ P ∈ F.map f, Prime P := by
    intro P hP
    obtain ⟨P', hP', rfl⟩ := Multiset.mem_map.mp hP
    first
    | exact (MulEquiv.prime_iff f).mpr (hprime P' hP')
    | exact (hprime P' hP').map_mulEquiv f
  have hmapF : F.map f = F := by
    have h1 : (F.map f).prod = D := by rw [← map_multiset_prod, hprod, hfD]
    have h2 := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hprimeMap
    rw [h1] at h2
    exact h2.symm
  let p : Ideal S → Prop := fun P => r P (f P)
  let G := F.filter p
  have hq : F.filter (fun Q => r (f Q) Q) = G.map f := by
    calc F.filter (fun Q => r (f Q) Q) = (F.map f).filter (fun Q => r (f Q) Q) := by rw [hmapF]
      _ = (F.filter ((fun Q => r (f Q) Q) ∘ f)).map f := Multiset.filter_map _ _ _
      _ = G.map f := by
        congr 1
        apply Multiset.filter_congr
        intro P _
        simp only [Function.comp_apply, hff, p]
  have hnot : F.filter (fun Q => r (f Q) Q) = F.filter (fun P => ¬ p P) := by
    apply Multiset.filter_congr
    intro P hP
    have hne : P ≠ f P := fun h => hfix P hP h.symm
    constructor
    · intro h1 h2
      exact asymm h1 h2
    · intro h1
      rcases trichotomous_of r P (f P) with h | h | h
      · exact absurd h h1
      · exact absurd h hne
      · exact h
  have hsplit : F = G + G.map f := by
    rw [← hq, hnot]
    exact (Multiset.filter_add_not p F).symm
  refine ⟨G.prod, ?_, ?_⟩
  · rw [map_multiset_prod, ← Multiset.prod_add, ← hsplit, hprod]
  · by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hB : G.prod ≤ M := le_trans le_sup_left hle
    have hfB : (G.map f).prod ≤ M := by
      rw [← map_multiset_prod]
      exact le_trans le_sup_right hle
    have hmaxOf : ∀ P ∈ F, P ≤ M → P = M := by
      intro P hPF hPM
      have hP := hprime P hPF
      have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
      exact (hPp.isMaximal hP.ne_zero).eq_of_le hM.ne_top hPM
    obtain ⟨P, hPG, hPM⟩ := (Ideal.IsPrime.multiset_prod_le hM.isPrime).mp hB
    obtain ⟨Q, hQG, hQM⟩ := (Ideal.IsPrime.multiset_prod_le hM.isPrime).mp hfB
    obtain ⟨P', hP'G, rfl⟩ := Multiset.mem_map.mp hQG
    have hPF := (Multiset.mem_filter.mp hPG).1
    have hpP : p P := (Multiset.mem_filter.mp hPG).2
    have hP'F := (Multiset.mem_filter.mp hP'G).1
    have hpP' : p P' := (Multiset.mem_filter.mp hP'G).2
    have hfP'F : f P' ∈ F := by
      rw [← hmapF]
      exact Multiset.mem_map_of_mem f hP'F
    have e : f P' = P := (hmaxOf _ hfP'F hQM).trans (hmaxOf P hPF hPM).symm
    have h1 : r P' P := by
      have := hpP'
      simp only [p, e] at this
      exact this
    have h2 : r P P' := by
      have := hpP
      simp only [p, ← e, hff] at this
      rw [← e]
      exact this
    exact asymm h1 h2
end Formalism.FrobeniusOrbits.Principal
