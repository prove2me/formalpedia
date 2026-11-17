-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_iid_zero_one_finite_sum_has_binomial_law_20261116
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:14:26.204759+00:00
-- url     : https://prove2.me/submissions/42e45779-bd19-45da-b784-f8cdf6fd93fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem AvramDividend.Classical.avram_a26_iid_zero_one_finite_sum_has_binomial_law_20261116
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℕ)
    (hMeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hIndep : iIndepFun Y P)
    (p : unitInterval)
    (hP : ∀ i : Fin n, (P {ω : Ω | Y i ω = 1}).toReal = (p : ℝ)) :
    P.map (fun ω : Ω => ∑ i : Fin n, Y i ω) = Bin(n, p) := by
  classical
  have hSm : Measurable (fun ω => ∑ i : Fin n, Y i ω) :=
    Finset.measurable_sum _ (fun i _ => hMeas i)
  have h1 : ∀ i, P (Y i ⁻¹' {1}) = ENNReal.ofReal (p : ℝ) := by
    intro i
    rw [← hP i, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  have h0 : ∀ i, P (Y i ⁻¹' {0}) = ENNReal.ofReal (1 - (p : ℝ)) := by
    intro i
    have : Y i ⁻¹' {0} = (Y i ⁻¹' {1})ᶜ := by
      ext ω; rcases h01 i ω with h | h <;> simp [h]
    rw [this, prob_compl_eq_one_sub ((measurableSet_singleton 1).preimage (hMeas i)), h1,
      ENNReal.ofReal_sub _ p.2.1, ENNReal.ofReal_one]
  let F : Ω → Finset (Fin n) := fun ω => Finset.univ.filter (fun i => Y i ω = 1)
  have hS : ∀ ω, ∑ i : Fin n, Y i ω = (F ω).card := by
    intro ω
    have : ∀ i, Y i ω = if Y i ω = 1 then 1 else 0 := by
      intro i; rcases h01 i ω with h | h <;> simp [h]
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_boole]
    simp [F]
  let E : Finset (Fin n) → Set Ω := fun T =>
    ⋂ i ∈ (Finset.univ : Finset (Fin n)), Y i ⁻¹' (if i ∈ T then {1} else {0})
  have hEmem : ∀ T ω, ω ∈ E T ↔ F ω = T := by
    intro T ω
    simp only [E, F, Set.mem_iInter, Set.mem_preimage, Finset.mem_univ, true_implies,
      Finset.ext_iff, Finset.mem_filter, true_and]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ T <;> rcases h01 i ω with h | h <;> simp [hi, h]
  have hEm : ∀ T, MeasurableSet (E T) := by
    intro T
    refine Finset.measurableSet_biInter _ (fun i _ => ?_)
    split_ifs <;> exact (measurableSet_singleton _).preimage (hMeas i)
  have hEP : ∀ T : Finset (Fin n), P (E T) =
      ENNReal.ofReal (p : ℝ) ^ T.card * ENNReal.ofReal (1 - (p : ℝ)) ^ (n - T.card) := by
    intro T
    rw [hIndep.measure_inter_preimage_eq_mul Finset.univ
      (fun i _ => by split_ifs <;> exact measurableSet_singleton _)]
    have : ∀ i, P (Y i ⁻¹' (if i ∈ T then {1} else {0})) =
        if i ∈ T then ENNReal.ofReal (p : ℝ) else ENNReal.ofReal (1 - (p : ℝ)) := by
      intro i; split_ifs <;> simp [h1, h0]
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_ite, Finset.prod_const,
      Finset.prod_const]
    congr 2
    · simp
    · rw [show (Finset.univ.filter fun x => x ∉ T) = Tᶜ by ext; simp, Finset.card_compl,
        Fintype.card_fin]
  refine Measure.ext_of_singleton (fun k => ?_)
  rw [Measure.map_apply hSm (measurableSet_singleton k), binomial_singleton]
  have hset : (fun ω => ∑ i : Fin n, Y i ω) ⁻¹' {k} =
      ⋃ T ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), E T := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, exists_prop, hS, hEmem]
    constructor
    · intro h; exact ⟨F ω, h, rfl⟩
    · rintro ⟨T, hT, rfl⟩; exact hT
  rw [hset, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun T hT => by
        rw [hEP T, (Finset.mem_powersetCard.1 hT).2]), Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg p.2.1 _)),
      ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_pow p.2.1, ENNReal.ofReal_pow (by linarith [p.2.2]), ENNReal.ofReal_natCast,
      mul_assoc]
  · intro T _ T' _ hTT'
    refine Set.disjoint_left.2 (fun ω hω hω' => hTT' ?_)
    rw [← (hEmem T ω).1 hω, (hEmem T' ω).1 hω']
  · intro T _; exact hEm T

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℕ)
    (hMeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hIndep : iIndepFun Y P)
    (p : unitInterval)
    (hP : ∀ i : Fin n, (P {ω : Ω | Y i ω = 1}).toReal = (p : ℝ)) :
    P.map (fun ω : Ω => ∑ i : Fin n, Y i ω) = Bin(n, p) :=
  AvramDividend.Classical.avram_a26_iid_zero_one_finite_sum_has_binomial_law_20261116
    P n Y hMeas h01 hIndep p hP
