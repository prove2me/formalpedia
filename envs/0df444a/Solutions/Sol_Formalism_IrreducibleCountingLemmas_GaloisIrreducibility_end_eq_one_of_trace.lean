-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.end_eq_one_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:10.860797+00:00
-- url     : https://prove2.me/submissions/c632e298-68af-4bc7-8063-50eea0130f71

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Module
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (s : Module.End ℂ V) (m : ℕ) (hm : 0 < m) (hsm : s ^ m = 1)
    (htr : LinearMap.trace ℂ V s = (Module.finrank ℂ V : ℂ)) : s = 1 := by
  classical
  set p := LinearMap.charpoly s with hp
  have hspl : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := Polynomial.splits_iff_card_roots.1 hspl
  have hdeg : p.natDegree = Module.finrank ℂ V := LinearMap.charpoly_natDegree s
  have hsum : p.roots.sum = (Module.finrank ℂ V : ℂ) := by
    rw [← htr, Module.End.trace_eq_sum_roots_charpoly_of_splits hspl]
  have hroot : ∀ μ ∈ p.roots, μ ^ m = 1 := by
    intro μ hμ
    have hr : p.IsRoot μ := (Polynomial.mem_roots (LinearMap.charpoly_monic s).ne_zero).1 hμ
    have hev : s.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly s μ).2 hr
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := hv.pow_apply m
    rw [hsm] at h1
    change v = μ ^ m • v at h1
    have hv0 : v ≠ 0 := hv.2
    have h2 : (μ ^ m - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv0
  have hnorm : ∀ μ ∈ p.roots, ‖μ‖ = 1 := by
    intro μ hμ
    have h2 : ‖μ‖ ^ m = 1 := by rw [← norm_pow, hroot μ hμ, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h2
  have hre_le : ∀ μ ∈ p.roots, μ.re ≤ 1 := fun μ hμ =>
    (Complex.re_le_norm μ).trans (hnorm μ hμ).le
  have hresum : ∀ t : Multiset ℂ, t.sum.re = (t.map Complex.re).sum := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih => simp [ih]
  have hsumre : (p.roots.map Complex.re).sum = Module.finrank ℂ V := by
    rw [← hresum, hsum]
    simp
  have hall : ∀ μ ∈ p.roots, μ = 1 := by
    intro μ hμ
    have hμ' := hμ
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hμ
    have hle : (t.map Complex.re).sum ≤ t.card := by
      have h3 := Multiset.sum_map_le_sum_map (s := t) (f := Complex.re) (g := fun _ => (1 : ℝ))
        (fun x hx => hre_le x (by rw [ht]; exact Multiset.mem_cons_of_mem hx))
      simpa using h3
    have hc : t.card + 1 = Module.finrank ℂ V := by
      rw [← hdeg, ← hcard, ht, Multiset.card_cons]
    rw [ht, Multiset.map_cons, Multiset.sum_cons] at hsumre
    have hre1 : μ.re = 1 := by
      have h4 := hre_le μ hμ'
      have h5 : ((t.card + 1 : ℕ) : ℝ) = (Module.finrank ℂ V : ℝ) := by exact_mod_cast hc
      push_cast at h5
      linarith
    have hn1 := hnorm μ hμ'
    have h6 : μ.im = 0 := by
      have h7 : ‖μ‖ ^ 2 = μ.re * μ.re + μ.im * μ.im := by
        rw [Complex.sq_norm, Complex.normSq_apply]
      rw [hn1, hre1] at h7
      nlinarith [sq_nonneg μ.im]
    exact Complex.ext (by simp [hre1]) (by simp [h6])
  have hroots : p.roots = Multiset.replicate (Module.finrank ℂ V) 1 :=
    Multiset.eq_replicate.2 ⟨by rw [hcard, hdeg], hall⟩
  have hpoly : p = (X - C (1 : ℂ)) ^ Module.finrank ℂ V := by
    have h8 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
    rw [(LinearMap.charpoly_monic s).leadingCoeff, C_1, one_mul, hroots, Multiset.map_replicate,
      Multiset.prod_replicate] at h8
    exact h8.symm
  have hae : Polynomial.aeval s ((X - C (1 : ℂ)) ^ Module.finrank ℂ V) = 0 := by
    rw [← hpoly]
    exact LinearMap.aeval_self_charpoly s
  have hmin1 : minpoly ℂ s ∣ (X - C (1 : ℂ)) ^ Module.finrank ℂ V := minpoly.dvd ℂ s hae
  have hmin2 : minpoly ℂ s ∣ X ^ m - C (1 : ℂ) := minpoly.dvd ℂ s (by simp [hsm])
  have hsep : (minpoly ℂ s).Separable :=
    (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm.ne') one_ne_zero).of_dvd hmin2
  obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) _).1 hmin1
  have hint : IsIntegral ℂ s := IsIntegral.of_finite ℂ s
  have heq : minpoly ℂ s = (X - C (1 : ℂ)) ^ i :=
    Polynomial.eq_of_monic_of_associated (minpoly.monic hint) ((monic_X_sub_C 1).pow i) hassoc
  have hi1 : i ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsq := hsep.squarefree
    rw [heq] at hsq
    have h9 : (X - C (1 : ℂ)) * (X - C (1 : ℂ)) ∣ (X - C (1 : ℂ)) ^ i := by
      rw [← pow_two]
      exact pow_dvd_pow _ hcon
    exact (Polynomial.prime_X_sub_C (1 : ℂ)).not_unit (hsq _ h9)
  have hae2 := minpoly.aeval ℂ s
  rw [heq] at hae2
  interval_cases i
  · have h10 : (1 : Module.End ℂ V) = 0 := by simpa using hae2
    haveI := subsingleton_of_zero_eq_one h10.symm
    exact Subsingleton.elim _ _
  · simpa [sub_eq_zero] using hae2
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
