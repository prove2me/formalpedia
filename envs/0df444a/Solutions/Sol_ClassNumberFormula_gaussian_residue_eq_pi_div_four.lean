-- Prove2me | solution 1 for ClassNumberFormula.gaussian_residue_eq_pi_div_four
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:35:33.430833+00:00
-- url     : https://prove2.me/submissions/41b56955-79d2-451d-8fba-8d6eec15b93a

import Mathlib

open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace CNGR

lemma cyc (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (i : K)
    (hi : i ^ 2 = -1) : IsCyclotomicExtension {4} ℚ K := by
  have hprim : IsPrimitiveRoot i 4 := by
    apply IsPrimitiveRoot.mk_of_lt i (by norm_num)
    · calc i ^ 4 = (i ^ 2) ^ 2 := by ring
        _ = 1 := by rw [hi]; norm_num
    · intro l hl0 hl4
      interval_cases l
      · intro h; rw [pow_one] at h; rw [h] at hi; norm_num at hi
      · rw [hi]; norm_num
      · intro h
        have : i ^ 3 = -i := by rw [pow_succ, hi]; ring
        rw [this] at h
        have h2 : i = -1 := by linear_combination -h
        rw [h2] at hi; norm_num at hi
  have hnot : ∀ q : ℚ, algebraMap ℚ K q ≠ i := by
    intro q hq
    have : algebraMap ℚ K (q ^ 2) = algebraMap ℚ K (-1) := by
      rw [map_pow, hq, hi, map_neg, map_one]
    have h2 := (algebraMap ℚ K).injective this
    nlinarith [sq_nonneg q]
  have htop : IntermediateField.adjoin ℚ {i} = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.finrank_top', hK]
    have hd : Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) ∣ 2 := by
      rw [← hK, ← IntermediateField.finrank_top' (F := ℚ) (E := K)]
      exact IntermediateField.finrank_dvd_of_le_right le_top
    have hne : Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) ≠ 1 := by
      rw [Ne, IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff,
        IntermediateField.mem_bot]
      rintro ⟨q, hq⟩
      exact hnot q hq
    have hpos : 0 < Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) := Module.finrank_pos
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) <;> simp_all
  have halg : Algebra.adjoin ℚ {i} = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic i)).mp htop
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨i, hprim⟩, fun x => ?_⟩
  have : x ∈ Algebra.adjoin ℚ {i} := by rw [halg]; trivial
  refine Algebra.adjoin_mono ?_ this
  intro b hb
  rw [Set.mem_singleton_iff] at hb
  subst hb
  exact hprim.pow_eq_one


theorem main (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hi : ∃ i : K, i ^ 2 = -1) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 ((π / 4 : ℝ) : ℂ)) := by
  classical
  obtain ⟨i, hi⟩ := hi
  haveI := cyc K hK i hi
  have hr : nrRealPlaces K = 0 := IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 4) K (by norm_num)
  have hc : nrComplexPlaces K = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 4)]; decide
  have hdisc : discr K = -4 := by
    have ht : Nat.totient 4 = 2 := by decide
    have hp : Nat.primeFactors 4 = {2} := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
    rw [IsCyclotomicExtension.Rat.discr 4 K, ht, hp]; norm_num
  have htor : torsionOrder K = 4 := by
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 4)]; decide
  have hreg : regulator K = 1 := by
    have h0 : rank K = 0 := by
      rw [rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, hc]
    obtain ⟨w'⟩ : Nonempty (InfinitePlace K) := inferInstance
    have : IsEmpty (Fin (rank K)) := by rw [h0]; infer_instance
    have hsub : IsEmpty {w : InfinitePlace K // w ≠ w'} := by
      have hcard : Fintype.card {w : InfinitePlace K // w ≠ w'} = 0 := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        unfold rank at h0
        omega
      exact Fintype.card_eq_zero_iff.mp hcard
    rw [regulator_eq_det K w' (Equiv.equivOfIsEmpty _ _), Matrix.det_isEmpty, abs_one]
  have hcl : classNumber K = 1 := by
    rw [classNumber_eq_one_iff]
    apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
    rw [hdisc, hc, hK]
    norm_num [Nat.factorial]
    nlinarith [pi_gt_three]
  have h := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hres : dedekindZeta_residue K = π / 4 := by
    rw [dedekindZeta_residue_def, hr, hc, hreg, hcl, htor, hdisc]
    have : Real.sqrt |((-4 : ℤ) : ℝ)| = 2 := by
      rw [show |((-4 : ℤ) : ℝ)| = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [this]; ring
  rw [hres] at h
  convert h using 2

end CNGR

theorem solution (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hi : ∃ i : K, i ^ 2 = -1) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 ((π / 4 : ℝ) : ℂ)) :=
  CNGR.main K hK hi
