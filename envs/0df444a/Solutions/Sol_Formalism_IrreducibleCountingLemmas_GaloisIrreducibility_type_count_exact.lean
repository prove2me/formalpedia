-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.type_count_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:02.521582+00:00
-- url     : https://prove2.me/submissions/658452fa-d6bb-421d-b97f-058e23cd8192

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_coeff
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_coeffs
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_injective
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial UniqueFactorizationMonoid
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
set_option maxHeartbeats 800000
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : TypeCountExact := by
  classical
  intro K _ _ N n hN
  suffices H : ((Finset.univ : Finset (Fin N → K)).filter (fun c =>
      Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧
      ∀ d ∈ Finset.Icc 1 N, ((normalizedFactors (monicOf c)).map
        Polynomial.natDegree).count d = n d)).card =
      ∏ d ∈ Finset.Icc 1 N,
        (((Finset.univ : Finset (Fin d → K)).filter
          (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card).choose (n d) by
    convert H
  have L1 : ∀ m : Multiset K[X], (∀ q ∈ m, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0) →
      m.prod.Monic ∧ normalizedFactors m.prod = m ∧
        m.prod.natDegree = (m.map Polynomial.natDegree).sum ∧ m.prod.coeff 0 ≠ 0 := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro h
      have ha := h a (by simp)
      obtain ⟨h1, h2, h3, h4⟩ := ih (fun q hq => h q (by simp [hq]))
      have hna : normalize a = a := by
        first
          | exact ha.1.normalize_eq_self
          | exact Polynomial.Monic.normalize_eq_self ha.1
          | simp [normalize_apply, Polynomial.coe_normUnit, ha.1.leadingCoeff]
      rw [Multiset.prod_cons]
      refine ⟨ha.1.mul h1, ?_, ?_, ?_⟩
      · rw [normalizedFactors_mul ha.2.1.ne_zero h1.ne_zero, normalizedFactors_irreducible ha.2.1,
          hna, h2, Multiset.singleton_add]
      · rw [ha.1.natDegree_mul h1, h3, Multiset.map_cons, Multiset.sum_cons]
      · rw [Polynomial.mul_coeff_zero]
        exact mul_ne_zero ha.2.2 h4
  have L2 : ∀ (T : Finset K[X]) (d : ℕ), (T.val.map Polynomial.natDegree).count d =
      (T.filter (fun q => q.natDegree = d)).card := by
    intro T d
    rw [Multiset.count_map]
    exact congrArg Multiset.card (Multiset.filter_congr (fun x _ => eq_comm))
  have F : ∀ c : Fin N → K, (monicOf c).coeff 0 ≠ 0 → ∀ q ∈ normalizedFactors (monicOf c),
      q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧ 1 ≤ q.natDegree ∧ q.natDegree ≤ N := by
    intro c hc q hq
    have hirr : Irreducible q := by
      first
        | exact irreducible_of_normalized_factor q hq
        | exact UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hq0 : q ≠ 0 := hirr.ne_zero
    have hnq : normalize q = q := by
      first
        | exact normalize_normalized_factor q hq
        | exact UniqueFactorizationMonoid.normalize_normalized_factor q hq
    have hmon : q.Monic := by
      have h := Polynomial.monic_normalize hq0
      rwa [hnq] at h
    have hdvd : q ∣ monicOf c := by
      first
        | exact dvd_of_mem_normalizedFactors hq
        | exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq
    have hp0 : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
    refine ⟨hmon, hirr, ?_, ?_, ?_⟩
    · intro h0
      apply hc
      exact Polynomial.X_dvd_iff.mp ((Polynomial.X_dvd_iff.mpr h0).trans hdvd)
    · by_contra hlt
      have hz : q.natDegree = 0 := by omega
      have h1 : q = 1 := by
        first
          | exact hmon.natDegree_eq_zero_iff_eq_one.mp hz
          | exact Polynomial.eq_one_of_monic_natDegree_zero hmon hz
      apply hirr.not_isUnit
      rw [h1]
      exact isUnit_one
    · have h := Polynomial.natDegree_le_of_dvd hdvd hp0
      rwa [monicOf_natDegree] at h
  have P : ∀ c : Fin N → K, (monicOf c).coeff 0 ≠ 0 →
      (normalizedFactors (monicOf c)).prod = monicOf c := by
    intro c hc
    have hp0 : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
    have hm := (L1 _ (fun q hq => ⟨(F c hc q hq).1, (F c hc q hq).2.1, (F c hc q hq).2.2.1⟩)).1
    apply Polynomial.eq_of_monic_of_associated hm (monicOf_monic c)
    first
      | exact prod_normalizedFactors hp0
      | exact normalizedFactors_prod hp0
      | exact UniqueFactorizationMonoid.prod_normalizedFactors hp0
      | exact UniqueFactorizationMonoid.normalizedFactors_prod hp0
  set Irr : ℕ → Finset K[X] := fun d => ((Finset.univ : Finset (Fin d → K)).filter
    (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).image monicOf with hIrrdef
  have hIrr : ∀ (d : ℕ) (q : K[X]), q ∈ Irr d ↔
      q.Monic ∧ q.natDegree = d ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := by
    intro d q
    simp only [Irr, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      exact ⟨monicOf_monic c, monicOf_natDegree c, h1, h2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i => q.coeff i, ?_, monicOf_coeffs h1 h2⟩
      rw [monicOf_coeffs h1 h2]
      exact ⟨h3, h4⟩
  set U : ((d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) → Finset K[X] :=
    fun f => (Finset.Icc 1 N).attach.biUnion (fun x => f x.1 x.2) with hUdef
  have hmemT : ∀ (f : (d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) (q : K[X]),
      q ∈ U f ↔ ∃ d, ∃ hd : d ∈ Finset.Icc 1 N, q ∈ f d hd := by
    intro f q
    simp only [U]
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨x, _, hx⟩
      exact ⟨x.1, x.2, hx⟩
    · rintro ⟨d, hd, hq⟩
      exact ⟨⟨d, hd⟩, Finset.mem_attach _ _, hq⟩
  have key : ∀ f : ((d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]),
      (∀ d (hd : d ∈ Finset.Icc 1 N), f d hd ∈ (Irr d).powersetCard (n d)) →
      (U f).val.prod.Monic ∧ normalizedFactors (U f).val.prod = (U f).val ∧
        (U f).val.prod.natDegree = N ∧ (U f).val.prod.coeff 0 ≠ 0 ∧
        ∀ d (hd : d ∈ Finset.Icc 1 N), (U f).filter (fun q => q.natDegree = d) = f d hd := by
    intro f hf
    have hprop : ∀ d (hd : d ∈ Finset.Icc 1 N) q, q ∈ f d hd →
        q.Monic ∧ q.natDegree = d ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := fun d hd q hq =>
      (hIrr d q).mp ((Finset.mem_powersetCard.mp (hf d hd)).1 hq)
    have hfib : ∀ d (hd : d ∈ Finset.Icc 1 N),
        (U f).filter (fun q => q.natDegree = d) = f d hd := by
      intro d hd
      ext q
      rw [Finset.mem_filter, hmemT]
      constructor
      · rintro ⟨⟨d', hd', hq⟩, hdeg⟩
        have hdd : d' = d := (hprop d' hd' q hq).2.1.symm.trans hdeg
        subst hdd
        exact hq
      · intro hq
        exact ⟨⟨d, hd, hq⟩, (hprop d hd q hq).2.1⟩
    have hall : ∀ q ∈ (U f).val, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := by
      intro q hq
      obtain ⟨d, hd, hq'⟩ := (hmemT f q).mp hq
      obtain ⟨h1, _, h3, h4⟩ := hprop d hd q hq'
      exact ⟨h1, h3, h4⟩
    obtain ⟨hmon, hnf, hdeg, hc0⟩ := L1 _ hall
    refine ⟨hmon, hnf, ?_, hc0, hfib⟩
    rw [hdeg, ← hN]
    have hmaps : ∀ q ∈ U f, q.natDegree ∈ Finset.Icc 1 N := by
      intro q hq
      obtain ⟨d, hd, hq'⟩ := (hmemT f q).mp hq
      rw [(hprop d hd q hq').2.1]
      exact hd
    have hsum : ((U f).val.map Polynomial.natDegree).sum = ∑ q ∈ U f, q.natDegree := rfl
    rw [hsum, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [hfib d hd, Finset.sum_const_nat (fun q hq => (hprop d hd q hq).2.1),
      (Finset.mem_powersetCard.mp (hf d hd)).2, mul_comm]
  have hTval : ∀ c : Fin N → K, Squarefree (monicOf c) →
      (normalizedFactors (monicOf c)).toFinset.val = normalizedFactors (monicOf c) := by
    intro c hsq
    rw [Multiset.toFinset_val]
    exact Multiset.dedup_eq_self.mpr
      ((squarefree_iff_nodup_normalizedFactors (monicOf_monic c).ne_zero).mp hsq)
  refine (Finset.card_nbij' (t := (Finset.Icc 1 N).pi (fun d => (Irr d).powersetCard (n d)))
    (fun (c : Fin N → K) (d : ℕ) (_ : d ∈ Finset.Icc 1 N) =>
      (normalizedFactors (monicOf c)).toFinset.filter (fun q => q.natDegree = d))
    (fun (f : (d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) (k : Fin N) => ((U f).val.prod).coeff k)
    ?_ ?_ ?_ ?_).trans ?_
  · intro c hc
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter] at hc
    obtain ⟨_, hsq, hc0, hcount⟩ := hc
    rw [Finset.mem_coe, Finset.mem_pi]
    intro d hd
    rw [Finset.mem_powersetCard]
    constructor
    · intro q hq
      rw [Finset.mem_filter, Multiset.mem_toFinset] at hq
      obtain ⟨h1, h2, h3, _, _⟩ := F c hc0 q hq.1
      exact (hIrr d q).mpr ⟨h1, hq.2, h2, h3⟩
    · have h := L2 (normalizedFactors (monicOf c)).toFinset d
      rw [hTval c hsq] at h
      rw [← h]
      exact hcount d hd
  · intro f hf
    rw [Finset.mem_coe, Finset.mem_pi] at hf
    obtain ⟨hmon, hnf, hdeg, hc0, hfib⟩ := key f hf
    have hp := monicOf_coeffs hmon hdeg
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter]
    dsimp only
    rw [hp]
    refine ⟨Finset.mem_univ _, (squarefree_iff_nodup_normalizedFactors hmon.ne_zero).mpr ?_, hc0, ?_⟩
    · rw [hnf]
      exact (U f).nodup
    · intro d hd
      rw [hnf, L2, hfib d hd]
      exact (Finset.mem_powersetCard.mp (hf d hd)).2
  · intro c hc
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter] at hc
    obtain ⟨_, hsq, hc0, _⟩ := hc
    have hU : U (fun d _ => (normalizedFactors (monicOf c)).toFinset.filter
        (fun q => q.natDegree = d)) = (normalizedFactors (monicOf c)).toFinset := by
      ext q
      simp only [U]
      rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨x, _, hq⟩
        exact (Finset.mem_filter.mp hq).1
      · intro hq
        obtain ⟨_, _, _, h4, h5⟩ := F c hc0 q (Multiset.mem_toFinset.mp hq)
        exact ⟨⟨q.natDegree, Finset.mem_Icc.mpr ⟨h4, h5⟩⟩, Finset.mem_attach _ _,
          Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
    funext k
    dsimp only
    rw [hU, hTval c hsq, P c hc0, monicOf_coeff]
  · intro f hf
    rw [Finset.mem_coe, Finset.mem_pi] at hf
    obtain ⟨hmon, hnf, hdeg, _, hfib⟩ := key f hf
    funext d hd
    dsimp only
    rw [monicOf_coeffs hmon hdeg, hnf, Finset.val_toFinset, hfib d hd]
  · rw [Finset.card_pi]
    refine Finset.prod_congr rfl ?_
    intro d _
    rw [Finset.card_powersetCard]
    simp only [Irr]
    rw [Finset.card_image_of_injective _ monicOf_injective]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
