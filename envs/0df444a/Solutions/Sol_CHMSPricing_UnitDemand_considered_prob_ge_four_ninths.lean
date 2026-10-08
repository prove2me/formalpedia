-- Prove2me | solution 1 for CHMSPricing.UnitDemand.considered_prob_ge_four_ninths
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:24:27.94333+00:00
-- url     : https://prove2.me/submissions/d0fe8f48-5efe-4c9e-b859-3696edef9033

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_ValueDist
import Definitions.Def_CHMSPricing_UnitDemand_SetSystem



namespace CHMSPricing.UnitDemand

open MeasureTheory

theorem law_prob (D : ValueDist) : IsProbabilityMeasure D.law := by
  constructor
  unfold ValueDist.law
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : IntegrableOn D.f (Set.Icc D.lo D.hi) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le D.lo_lt_hi.le,
      D.f_integral]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using (D.f_pos x hx).le

theorem law_singleton (D : ValueDist) (x : ℝ) : D.law {x} = 0 := by
  unfold ValueDist.law
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null Set.inter_subset_left (Real.volume_singleton)

theorem law_split (D : ValueDist) (x : ℝ) :
    (D.law (Set.Iio x)).toReal + (D.law (Set.Ici x)).toReal = 1 ∧
    D.cdf x = (D.law (Set.Iio x)).toReal := by
  haveI := law_prob D
  constructor
  · have h1 : D.law (Set.Iio x) + D.law (Set.Ici x) = 1 := by
      rw [← Set.compl_Iio, measure_add_measure_compl measurableSet_Iio, measure_univ]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h1]; simp
  · unfold ValueDist.cdf
    rw [← Set.Iio_insert, Set.insert_eq, measure_union (by simp) measurableSet_Iio,
      law_singleton, zero_add]

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → ValueDist) (p : ι → ℝ)

noncomputable def qq (j : ι) : ℝ := ((D j).law (Set.Ici (p j))).toReal

noncomputable def mu (S : Finset ι) : ℝ := ∏ j, (if j ∈ S then qq D p j else 1 - qq D p j)

theorem qq_eq (j : ι) : qq D p j = 1 - (D j).cdf (p j) := by
  obtain ⟨h1, h2⟩ := law_split (D j) (p j)
  unfold qq; linarith

theorem qq_nonneg (j : ι) : 0 ≤ qq D p j := ENNReal.toReal_nonneg

theorem qq_le (j : ι) : qq D p j ≤ 1 := by
  obtain ⟨h1, _⟩ := law_split (D j) (p j)
  unfold qq; linarith [ENNReal.toReal_nonneg (a := (D j).law (Set.Iio (p j)))]

theorem mu_nonneg (S : Finset ι) : 0 ≤ mu D p S := by
  unfold mu
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · exact qq_nonneg D p j
  · linarith [qq_le D p j]

theorem fiber_eq (S : Finset ι) : {v : ι → ℝ | desiring p v = S} =
    Set.pi Set.univ (fun j => if j ∈ S then Set.Ici (p j) else Set.Iio (p j)) := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Finset.ext_iff, desiring,
    Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro j
  split_ifs with hj <;> simp [hj]

theorem fiber_meas (S : Finset ι) : MeasurableSet {v : ι → ℝ | desiring p v = S} := by
  rw [fiber_eq]
  apply MeasurableSet.univ_pi
  intro j
  split_ifs
  · exact measurableSet_Ici
  · exact measurableSet_Iio

theorem prior_fiber (S : Finset ι) : (prior D {v | desiring p v = S}).toReal = mu D p S := by
  haveI := fun j => law_prob (D j)
  rw [fiber_eq]
  unfold prior
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  unfold mu
  apply Finset.prod_congr rfl
  intro j _
  split_ifs
  · rfl
  · obtain ⟨h1, _⟩ := law_split (D j) (p j)
    unfold qq; linarith

theorem prior_pred (P : Finset ι → Prop) [DecidablePred P] :
    (prior D {v | P (desiring p v)}).toReal = ∑ S, mu D p S * (if P S then 1 else 0) := by
  haveI := fun j => law_prob (D j)
  haveI : IsProbabilityMeasure (prior D) := by unfold prior; infer_instance
  have hset : {v : ι → ℝ | P (desiring p v)} =
      ⋃ S ∈ Finset.univ.filter P, {v | desiring p v = S} := by
    ext v; simp
  rw [hset, measure_biUnion_finset]
  · rw [ENNReal.toReal_sum (fun S _ => measure_ne_top _ _)]
    simp only [prior_fiber, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_filter]
  · intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro v ha hb
    exact hab (ha.symm.trans hb)
  · intro S _; exact fiber_meas p S

theorem mu_sum : ∑ S, mu D p S = 1 := by
  haveI := fun j => law_prob (D j)
  have := prior_pred D p (fun _ => True)
  simp only [Set.setOf_true, if_true, mul_one] at this
  rw [← this]
  unfold prior; simp

theorem mu_marg (j : ι) : ∑ S, mu D p S * (if j ∈ S then 1 else 0) = qq D p j := by
  haveI := fun j => law_prob (D j)
  rw [← prior_pred D p (fun S => j ∈ S)]
  have hset : {v : ι → ℝ | j ∈ desiring p v} =
      Set.pi Set.univ (Function.update (fun _ => Set.univ) j (Set.Ici (p j))) := by
    ext v
    simp only [Set.mem_setOf_eq, desiring, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h k
      by_cases hk : k = j
      · subst hk; simpa using h
      · simp [Function.update_of_ne hk]
    · intro h; simpa using h j
  rw [hset]
  unfold prior
  rw [Measure.pi_pi, Finset.prod_eq_single j]
  · simp [qq]
  · intro k _ hk; simp [Function.update_of_ne hk]
  · simp

theorem mu_mul (a b : Finset ι) : mu D p a * mu D p b = mu D p (a ∩ b) * mu D p (a ∪ b) := by
  unfold mu
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases ha : j ∈ a <;> by_cases hb : j ∈ b <;> simp [ha, hb, mul_comm]

/-- Markov: the probability (under `mu`) that at least `k` members of `T` lie in `S`. -/
theorem markov (T : Finset ι) (k : ℕ) (hk : 1 ≤ k) (hT : ∑ j ∈ T, qq D p j ≤ (k : ℝ) / 3) :
    (2 / 3 : ℝ) ≤ ∑ S, mu D p S * (if (S.filter (· ∈ T)).card ≤ k - 1 then 1 else 0) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hpt : ∀ S : Finset ι, (if (S.filter (· ∈ T)).card ≤ k - 1 then (1 : ℝ) else 0) ≥
      1 - ((S.filter (· ∈ T)).card : ℝ) / k := by
    intro S
    split_ifs with h
    · have : (0 : ℝ) ≤ ((S.filter (· ∈ T)).card : ℝ) / k := by positivity
      linarith
    · have h' : k ≤ (S.filter (· ∈ T)).card := by omega
      have : (k : ℝ) ≤ (S.filter (· ∈ T)).card := by exact_mod_cast h'
      rw [ge_iff_le, sub_nonpos, le_div_iff₀ hkpos]; linarith
  have hcard : ∀ S : Finset ι, ((S.filter (· ∈ T)).card : ℝ) =
      ∑ j ∈ T, (if j ∈ S then 1 else 0) := by
    intro S
    rw [Finset.sum_boole]
    congr 2
    ext j; simp [and_comm]
  have hexp : ∑ S, mu D p S * ((S.filter (· ∈ T)).card : ℝ) = ∑ j ∈ T, qq D p j := by
    simp only [hcard, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact mu_marg D p j
  calc (2 / 3 : ℝ) ≤ 1 - (∑ j ∈ T, qq D p j) / k := by
        have : (∑ j ∈ T, qq D p j) / k ≤ 1 / 3 := by
          rw [div_le_iff₀ hkpos]; linarith
        linarith
    _ = ∑ S, mu D p S * (1 - ((S.filter (· ∈ T)).card : ℝ) / k) := by
        simp only [mul_sub, Finset.sum_sub_distrib, mu_sum, mul_div_assoc', ← Finset.sum_div, hexp,
          mul_one]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro S _
        exact mul_le_mul_of_nonneg_left (hpt S) (mu_nonneg D p S)

theorem harris (f g : Finset ι → ℝ) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hf : Antitone f) (hg : Antitone g) :
    (∑ S, mu D p S * f S) * (∑ S, mu D p S * g S) ≤ ∑ S, mu D p S * (f S * g S) := by
  have := fkg (α := (Finset ι)ᵒᵈ) (μ := fun a => mu D p (OrderDual.ofDual a))
    (f := fun a => f (OrderDual.ofDual a)) (g := fun a => g (OrderDual.ofDual a))
    (fun a => mu_nonneg D p _) (fun a => hf0 _) (fun a => hg0 _)
    (fun a b h => hf h) (fun a b h => hg h)
    (fun a b => by
      rw [mu_mul D p (OrderDual.ofDual a) (OrderDual.ofDual b)]
      show _ ≤ mu D p (OrderDual.ofDual a ∪ OrderDual.ofDual b) * mu D p (OrderDual.ofDual a ∩ OrderDual.ofDual b)
      rw [mul_comm])
  have hs : ∑ a : (Finset ι)ᵒᵈ, mu D p (OrderDual.ofDual a) = 1 := mu_sum D p
  rw [hs, one_mul] at this
  exact this

end

theorem hT_lem {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β] (D : ι → ValueDist)
    (p : ι → ℝ) (i : ι) (part : ι → β) (cap : β → ℕ)
    (h : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part i' = b), (1 - (D i').cdf (p i'))
        ≤ (cap b : ℝ) / 3) :
    ∑ j ∈ Finset.univ.filter (fun i' => i' ≠ i ∧ part i' = part i), qq D p j ≤ (cap (part i) : ℝ) / 3 := by
  refine le_trans ?_ (h (part i))
  simp only [← qq_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩
  · intro j _ _; exact qq_nonneg D p j

theorem cp_core {ι β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β₁] [DecidableEq β₂]
    (D : ι → ValueDist) (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ)
    (p : ι → ℝ)
    (hq₁ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₁ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₁ b : ℝ) / 3)
    (hq₂ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₂ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₂ b : ℝ) / 3)
    (i : ι) (hk₁ : 1 ≤ cap₁ (part₁ i)) (hk₂ : 1 ≤ cap₂ (part₂ i)) :
    (4 / 9 : ℝ) ≤ (prior D {v |
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1}).toReal := by
  classical
  set T₁ := Finset.univ.filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)
  set T₂ := Finset.univ.filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)
  have e1 : ∀ S : Finset ι, S.filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i) = S.filter (· ∈ T₁) := by
    intro S; ext x; simp [T₁]
  have e2 : ∀ S : Finset ι, S.filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i) = S.filter (· ∈ T₂) := by
    intro S; ext x; simp [T₂]
  have m1 := markov D p T₁ _ hk₁ (hT_lem D p i part₁ cap₁ hq₁)
  have m2 := markov D p T₂ _ hk₂ (hT_lem D p i part₂ cap₂ hq₂)
  have hP := prior_pred D p (fun S => (S.filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 ∧
    (S.filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1)
  have hsetEq : {v : ι → ℝ |
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1} =
      {v | ((desiring p v).filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 ∧
        ((desiring p v).filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1} := by
    simp only [e1, e2]
  rw [hsetEq, hP]
  have H := harris D p (fun S => if (S.filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 then 1 else 0)
    (fun S => if (S.filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1 then 1 else 0)
    (fun S => by simp only [Pi.zero_apply]; split_ifs <;> norm_num)
    (fun S => by simp only [Pi.zero_apply]; split_ifs <;> norm_num)
    (fun a b hab => by
      have : (a.filter (· ∈ T₁)).card ≤ (b.filter (· ∈ T₁)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hab)
      simp only; split_ifs <;> first | (exfalso; rename_i h1 h2; exact h2 (this.trans h1)) | norm_num)
    (fun a b hab => by
      have : (a.filter (· ∈ T₂)).card ≤ (b.filter (· ∈ T₂)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hab)
      simp only; split_ifs <;> first | (exfalso; rename_i h1 h2; exact h2 (this.trans h1)) | norm_num)
  have hprod : (4 / 9 : ℝ) ≤ (∑ S, mu D p S * (if (S.filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 then 1 else 0)) *
      (∑ S, mu D p S * (if (S.filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1 then 1 else 0)) := by
    have := mul_le_mul m1 m2 (by norm_num) (by linarith)
    linarith
  refine hprod.trans (H.trans (le_of_eq ?_))
  apply Finset.sum_congr rfl
  intro S _
  by_cases hA : (S.filter (· ∈ T₁)).card ≤ cap₁ (part₁ i) - 1 <;>
    by_cases hB : (S.filter (· ∈ T₂)).card ≤ cap₂ (part₂ i) - 1 <;> simp [hA, hB]

end CHMSPricing.UnitDemand

open CHMSPricing.UnitDemand


theorem solution {ι β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β₁] [DecidableEq β₂]
    (D : ι → ValueDist) (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ)
    (p : ι → ℝ)
    (hq₁ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₁ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₁ b : ℝ) / 3)
    (hq₂ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₂ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₂ b : ℝ) / 3)
    (i : ι) (hk₁ : 1 ≤ cap₁ (part₁ i)) (hk₂ : 1 ≤ cap₂ (part₂ i)) :
    (4 / 9 : ℝ) ≤ (prior D {v |
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1}).toReal := by
  exact cp_core D part₁ cap₁ part₂ cap₂ p hq₁ hq₂ i hk₁ hk₂
