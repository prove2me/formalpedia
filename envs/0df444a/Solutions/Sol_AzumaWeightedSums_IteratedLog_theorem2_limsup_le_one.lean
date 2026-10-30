-- Prove2me | solution 1 for AzumaWeightedSums.IteratedLog.theorem2_limsup_le_one
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T05:18:56.630656+00:00
-- url     : https://prove2.me/submissions/6822b831-8eeb-4c94-90d9-bb872621174b

import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_IteratedLog_WeightedSums

-- BEGIN MODULE AWProof.SharedBasics

-- END MODULE AWProof.SharedBasics

-- BEGIN MODULE AWProof.VarianceEpochs

namespace AzumaWeightedSums.IteratedLog.AWFresh
open Filter Topology

theorem exists_variance_cutoff (V : ℕ → ℝ) (hV : Monotone V) (h0 : V 0 = 0)
    (hdiv : Tendsto V atTop atTop) (U : ℝ) (hU : 0 < U) :
    ∃ N : ℕ, V N ≤ U ∧ ∀ n, V n ≤ U → n ≤ N := by
  have hex : ∃ n, U < V n := (hdiv.eventually (eventually_gt_atTop U)).exists
  let j := Nat.find hex
  have hj : U < V j := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra hh
    have he : j = 0 := by omega
    rw [he, h0] at hj
    linarith
  refine ⟨j - 1, ?_, ?_⟩
  · apply le_of_not_gt
    exact Nat.find_min hex (show j - 1 < Nat.find hex by change j - 1 < j; omega)
  · intro n hn
    by_contra hh
    have hjn : j ≤ n := by omega
    exact (not_lt_of_ge hn) (hj.trans_le (hV hjn))

theorem geometric_epoch (r v : ℝ) (hr : 1 < r) (hv : 1 ≤ v) :
    ∃ k : ℕ, r ^ k ≤ v ∧ v < r ^ (k + 1) := exists_nat_pow_near hv hr

theorem epoch_index_large {r v : ℝ} (hr : 1 < r) {k K : ℕ}
    (hv : r ^ (K + 1) ≤ v) (hk : v < r ^ (k + 1)) : K ≤ k := by
  by_contra hh
  have hpow : r ^ (k + 1) ≤ r ^ (K + 1) := pow_le_pow_right₀ hr.le (by omega)
  exact (not_lt_of_ge hv) (hk.trans_le hpow)

theorem lil_scale_mono {u v : ℝ} (hu : Real.exp 1 < u) (huv : u ≤ v) :
    Real.sqrt (2 * u * Real.log (Real.log u)) ≤
      Real.sqrt (2 * v * Real.log (Real.log v)) := by
  have hu0 : 0 < u := (Real.exp_pos 1).trans hu
  have hlog : 1 < Real.log u := by
    have h := Real.log_lt_log (Real.exp_pos 1) hu
    simpa only [Real.log_exp] using h
  have hl : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  have hll : Real.log (Real.log u) ≤ Real.log (Real.log v) :=
    Real.log_le_log (by linarith) hl
  have hll0 : 0 ≤ Real.log (Real.log u) := (Real.log_pos hlog).le
  have hv0 : 0 < v := hu0.trans_le huv
  apply Real.sqrt_le_sqrt
  exact mul_le_mul (mul_le_mul_of_nonneg_left huv (by norm_num)) hll hll0 (by positivity)

end AzumaWeightedSums.IteratedLog.AWFresh
-- END MODULE AWProof.VarianceEpochs

-- BEGIN MODULE AWProof.EpochSeries

namespace AzumaWeightedSums.IteratedLog.AWFresh
open Filter Topology

noncomputable def epochThreshold (c r : ℝ) (k : ℕ) : ℝ :=
  c * Real.sqrt (2 * r ^ k * Real.log (Real.log (r ^ k)))

noncomputable def epochTail (c r : ℝ) (k : ℕ) : ℝ :=
  if Real.exp 1 < r ^ k then
    2 * Real.exp (-(epochThreshold c r k ^ 2) / (2 * r ^ (k + 1))) else 0

theorem epochThreshold_pos {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {k : ℕ}
    (hk : Real.exp 1 < r ^ k) : 0 < epochThreshold c r k := by
  have hl : 1 < Real.log (r ^ k) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hk
  have hr0 : 0 < r := by linarith
  exact mul_pos hc (Real.sqrt_pos.2 (mul_pos (by positivity) (Real.log_pos hl)))

theorem epochTail_nonneg (c r : ℝ) (k : ℕ) : 0 ≤ epochTail c r k := by
  unfold epochTail
  split_ifs <;> positivity

theorem epoch_tail_identity {c r : ℝ} (hr : 1 < r) {k : ℕ}
    (hk : Real.exp 1 < r ^ k) :
    epochTail c r k = (2 * (Real.log r) ^ (-(c ^ 2 / r))) * (k : ℝ) ^ (-(c ^ 2 / r)) := by
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos hr
  have hkne : k ≠ 0 := by
    intro he
    subst k
    simp only [pow_zero] at hk
    have he := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hkne
  have hl : 1 < Real.log (r ^ k) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hk
  have hll := Real.log_pos hl
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * r ^ k * Real.log (Real.log (r ^ k)) by positivity)
  have hexp : -(epochThreshold c r k ^ 2) / (2 * r ^ (k + 1)) =
      -(c ^ 2 / r) * Real.log (Real.log (r ^ k)) := by
    unfold epochThreshold
    rw [mul_pow, hsq, pow_succ]
    field_simp
    ring
  rw [epochTail, if_pos hk, hexp, Real.log_pow,
    Real.log_mul (ne_of_gt hkpos) (ne_of_gt hlr),
    Real.rpow_def_of_pos hlr, Real.rpow_def_of_pos hkpos]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring

theorem epochTail_summable {c r : ℝ} (hr : 1 < r) (hcr : r < c ^ 2) :
    Summable (epochTail c r) := by
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos hr
  have hp : 1 < c ^ 2 / r := (lt_div_iff₀ hr0).2 (by simpa using hcr)
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ (-(c ^ 2 / r))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply Summable.of_nonneg_of_le (epochTail_nonneg c r) _
    (hs.mul_left (2 * (Real.log r) ^ (-(c ^ 2 / r))))
  intro k
  by_cases hk : Real.exp 1 < r ^ k
  · exact (epoch_tail_identity hr hk).le
  · simp only [epochTail, if_neg hk]
    positivity

end AzumaWeightedSums.IteratedLog.AWFresh
-- END MODULE AWProof.EpochSeries

-- BEGIN MODULE AWProof.EpochTransfer

namespace AzumaWeightedSums.IteratedLog.AWFresh
open MeasureTheory Filter Topology

 theorem lil_of_finite_tail {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (S : ℕ → Ω → ℝ) (V : ℕ → ℝ) (hV : Monotone V) (h0 : V 0 = 0)
    (hdiv : Tendsto V atTop atTop)
    (htail : ∀ (N : ℕ) (U z : ℝ), 0 < U → 0 < z → V N ≤ U →
      μ {ω | ∃ n ≤ N, z ≤ |S n ω|} ≤ ENNReal.ofReal (2 * Real.exp (-(z ^ 2) / (2 * U))))
    (c : ℝ) (hc : 1 < c) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      |S n ω| ≤ c * Real.sqrt (2 * V n * Real.log (Real.log (V n))) := by
  classical
  obtain ⟨r, hr, hcr⟩ := exists_between (show (1 : ℝ) < c ^ 2 by nlinarith)
  have hr0 : 0 < r := by linarith
  have hc0 : 0 < c := by linarith
  have hcut (k : ℕ) : ∃ N : ℕ, V N ≤ r ^ (k + 1) ∧
      ∀ n, V n ≤ r ^ (k + 1) → n ≤ N :=
    exists_variance_cutoff V hV h0 hdiv _ (by positivity)
  choose N hN hcover using hcut
  let E : ℕ → Set Ω := fun k => if Real.exp 1 < r ^ k then
    {ω | ∃ n ≤ N k, epochThreshold c r k ≤ |S n ω|} else ∅
  have hE (k : ℕ) : μ (E k) ≤ ENNReal.ofReal (epochTail c r k) := by
    by_cases hk : Real.exp 1 < r ^ k
    · simpa only [E, epochTail, if_pos hk] using
        htail (N k) (r ^ (k + 1)) (epochThreshold c r k) (by positivity)
          (epochThreshold_pos hc0 hr hk) (hN k)
    · simp [E, epochTail, hk]
  have hsum : (∑' k, μ (E k)) ≠ ⊤ :=
    ne_of_lt ((ENNReal.tsum_le_tsum hE).trans_lt (epochTail_summable hr hcr).tsum_ofReal_lt_top)
  have hgood := MeasureTheory.ae_eventually_notMem hsum
  have hpow : ∀ᶠ k : ℕ in atTop, Real.exp 1 < r ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).eventually (eventually_gt_atTop (Real.exp 1))
  filter_upwards [hgood] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hω.and hpow)
  filter_upwards [hdiv.eventually (eventually_ge_atTop (max 1 (r ^ (K + 1))))] with n hn
  have hv1 : 1 ≤ V n := (le_max_left _ _).trans hn
  obtain ⟨k, hklo, hkhi⟩ := geometric_epoch r (V n) hr hv1
  have hKk : K ≤ k := epoch_index_large hr ((le_max_right _ _).trans hn) hkhi
  obtain ⟨hnot, hkexp⟩ := hK k hKk
  have hnN : n ≤ N k := hcover k n hkhi.le
  have habs : |S n ω| < epochThreshold c r k := by
    apply lt_of_not_ge
    intro hh
    apply hnot
    simp only [E, if_pos hkexp, Set.mem_ofPred_eq]
    exact ⟨n, hnN, hh⟩
  exact habs.le.trans (mul_le_mul_of_nonneg_left (lil_scale_mono hkexp hklo) hc0.le)

end AzumaWeightedSums.IteratedLog.AWFresh
-- END MODULE AWProof.EpochTransfer

-- BEGIN MODULE AWProof.SumBasics
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace AzumaWeightedSums.IteratedLog.AWFresh
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}

@[simp] theorem weightedSum_zero (a : ℕ → ℝ) (x : ℕ → Ω → ℝ) (ω : Ω) :
    weightedSum a x 0 ω = 0 := by simp [weightedSum]
@[simp] theorem sqWeightSum_zero (a : ℕ → ℝ) : sqWeightSum a 0 = 0 := by
  simp [sqWeightSum]
theorem weightedSum_succ (a : ℕ → ℝ) (x : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    weightedSum a x (n+1) ω = weightedSum a x n ω + a (n+1)*x (n+1) ω := by
  simp only [weightedSum, Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]
theorem sqWeightSum_succ (a : ℕ → ℝ) (n : ℕ) :
    sqWeightSum a (n+1) = sqWeightSum a n + a (n+1)^2 := by
  simp only [sqWeightSum, Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]
theorem sqWeightSum_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ sqWeightSum a n := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem sqWeightSum_mono (a : ℕ → ℝ) : Monotone (sqWeightSum a) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [sqWeightSum_succ]
  exact le_add_of_nonneg_right (sq_nonneg _)

omit [IsProbabilityMeasure μ] in
theorem sum_stronglyMeasurable (hx : IsCondSubgaussianOne μ ℱ x) (a : ℕ → ℝ) (n : ℕ) :
    StronglyMeasurable[ℱ n] (weightedSum a x n) := by
  unfold weightedSum
  have h : StronglyMeasurable[ℱ n] (∑ k ∈ Finset.Icc 1 n, fun ω => a k*x k ω) := by
    apply Finset.stronglyMeasurable_sum
    intro k hk
    exact ((hx.1 k (Finset.mem_Icc.mp hk).1).1.mono
      (ℱ.mono (Finset.mem_Icc.mp hk).2)).const_mul _
  convert h using 1
  ext ω
  simp only [Finset.sum_apply]

omit [IsProbabilityMeasure μ] in
theorem sum_integrable (hx : IsCondSubgaussianOne μ ℱ x) (a : ℕ → ℝ) (n : ℕ) :
    Integrable (weightedSum a x n) μ := by
  unfold weightedSum
  apply integrable_finsetSum
  intro k hk
  exact ((hx.1 k (Finset.mem_Icc.mp hk).1).2.1).const_mul _

end AzumaWeightedSums.IteratedLog.AWFresh
-- END MODULE AWProof.SumBasics

-- BEGIN MODULE AWProof.ExpIntegrable
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace AzumaWeightedSums.IteratedLog.AWFresh
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
theorem exp_sum_stronglyMeasurable (hx : IsCondSubgaussianOne μ ℱ x)
    (a : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    StronglyMeasurable[ℱ n] (fun ω => Real.exp (t*weightedSum a x n ω)) :=
  (Real.continuous_exp.comp_stronglyMeasurable ((sum_stronglyMeasurable hx a n).const_mul t))

theorem exp_sum_integrable (hx : IsCondSubgaussianOne μ ℱ x)
    (a : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t*weightedSum a x n ω)) μ := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hA := ih (2*t)
    have hB := hx.2.1 (n+1) (by omega) (2*t*a (n+1))
    apply ((hA.add hB).div_const 2).mono_nonneg
      ((exp_sum_stronglyMeasurable hx a (n+1) t).mono (ℱ.le _)).aestronglyMeasurable
    · exact ae_of_all _ fun _ => (Real.exp_pos _).le
    · apply ae_of_all
      intro ω
      rw [weightedSum_succ]
      have heA : Real.exp (2*t*weightedSum a x n ω) =
          Real.exp (t*weightedSum a x n ω)^2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have heB : Real.exp (2*t*a (n+1)*x (n+1) ω) =
          Real.exp (t*a (n+1)*x (n+1) ω)^2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have he : Real.exp (t*(weightedSum a x n ω+a (n+1)*x (n+1) ω)) =
          Real.exp (t*weightedSum a x n ω)*Real.exp (t*a (n+1)*x (n+1) ω) := by
        rw [← Real.exp_add]
        congr 1
        ring
      change _ ≤ (Real.exp (2*t*weightedSum a x n ω) +
        Real.exp (2*t*a (n+1)*x (n+1) ω))/2
      rw [heA, heB, he]
      nlinarith [sq_nonneg (Real.exp (t*weightedSum a x n ω)-
        Real.exp (t*a (n+1)*x (n+1) ω))]
end AzumaWeightedSums.IteratedLog.AWFresh
-- END MODULE AWProof.ExpIntegrable

-- BEGIN MODULE AWProof.ConditionalExp
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace AzumaWeightedSums.IteratedLog.AWFresh
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}

theorem increment_exp_lower (hx : IsCondSubgaussianOne μ ℱ x) (n : ℕ) (t : ℝ) :
    (fun _ : Ω => (1 : ℝ)) ≤ᵐ[μ]
      μ[fun ω => Real.exp (t*x (n+1) ω) | ℱ n] := by
  have hi := (hx.1 (n+1) (by omega)).2.1
  have hz : μ[x (n+1) | ℱ n] =ᵐ[μ] (0 : Ω → ℝ) := by
    simpa using (hx.1 (n+1) (by omega)).2.2
  have he := hx.2.1 (n+1) (by omega) t
  have hle : (fun ω => 1+t*x (n+1) ω) ≤ᵐ[μ]
      (fun ω => Real.exp (t*x (n+1) ω)) :=
    ae_of_all _ fun ω => by linarith [Real.add_one_le_exp (t*x (n+1) ω)]
  have hc : μ[fun ω => 1+t*x (n+1) ω | ℱ n] ≤ᵐ[μ]
      μ[fun ω => Real.exp (t*x (n+1) ω) | ℱ n] :=
    condExp_mono ((integrable_const 1).add (hi.const_mul t)) he hle
  have ha := condExp_add (μ := μ) (integrable_const (1 : ℝ)) (hi.const_mul t) (ℱ n)
  have ht := condExp_smul (μ := μ) t (x (n+1)) (ℱ n)
  filter_upwards [hc, ha, ht, hz] with ω hc ha ht hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const (ℱ.le n)] at ha ht
  change μ[fun ω => 1+t*x (n+1) ω | ℱ n] ω =
    1+μ[fun ω => t*x (n+1) ω | ℱ n] ω at ha
  change μ[fun ω => t*x (n+1) ω | ℱ n] ω = t*μ[x (n+1) | ℱ n] ω at ht
  change μ[x (n+1) | ℱ n] ω = 0 at hz
  rw [ha, ht, hz] at hc
  simpa using hc

theorem exp_sum_conditional (hx : IsCondSubgaussianOne μ ℱ x)
    (a : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    μ[fun ω => Real.exp (t*weightedSum a x (n+1) ω) | ℱ n] =ᵐ[μ]
      (fun ω => Real.exp (t*weightedSum a x n ω) *
        μ[fun ω => Real.exp ((t*a (n+1))*x (n+1) ω) | ℱ n] ω) := by
  have heq : (fun ω => Real.exp (t*weightedSum a x (n+1) ω)) =
      (fun ω => Real.exp (t*weightedSum a x n ω)) *
      (fun ω => Real.exp ((t*a (n+1))*x (n+1) ω)) := by
    funext ω
    simp only [Pi.mul_apply, weightedSum_succ, mul_add, mul_assoc, Real.exp_add]
  rw [heq]
  exact condExp_mul_of_stronglyMeasurable_left (exp_sum_stronglyMeasurable hx a n t)
    (heq ▸ exp_sum_integrable hx a (n+1) t)
    (hx.2.1 (n+1) (by omega) (t*a (n+1)))

theorem exp_sum_submartingale (hx : IsCondSubgaussianOne μ ℱ x)
    (a : ℕ → ℝ) (t : ℝ) :
    Submartingale (fun n ω => Real.exp (t*weightedSum a x n ω)) ℱ μ := by
  apply submartingale_nat (fun n => exp_sum_stronglyMeasurable hx a n t)
    (fun n => exp_sum_integrable hx a n t)
  intro n
  filter_upwards [exp_sum_conditional hx a n t,
    increment_exp_lower hx n (t*a (n+1))] with ω he hl
  rw [he]
  exact le_mul_of_one_le_right (Real.exp_pos _).le hl

theorem exp_sum_conditional_upper (hx : IsCondSubgaussianOne μ ℱ x)
    (a : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    μ[fun ω => Real.exp (t*weightedSum a x (n+1) ω) | ℱ n] ≤ᵐ[μ]
      (fun ω => Real.exp (t*weightedSum a x n ω)*Real.exp ((t*a (n+1))^2/2)) := by
  have hu : μ[fun ω => Real.exp ((t*a (n+1))*x (n+1) ω) | ℱ n] ≤ᵐ[μ]
      (fun _ => Real.exp ((t*a (n+1))^2/2)) := by
    simpa using hx.2.2 (n+1) (by omega) (t*a (n+1))
  filter_upwards [exp_sum_conditional hx a n t, hu] with ω he hu
  rw [he]
  exact mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
end AzumaWeightedSums.IteratedLog.AWFresh
-- END MODULE AWProof.ConditionalExp

-- BEGIN MODULE AWProof.MGF
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace AzumaWeightedSums.IteratedLog.AWFresh
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}

theorem mgf_sum_le (hx : IsCondSubgaussianOne μ ℱ x)
    (a : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (∫ ω, Real.exp (t*weightedSum a x n ω) ∂μ) ≤
      Real.exp (t^2*sqWeightSum a n/2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := exp_sum_integrable hx a n t
    calc
      (∫ ω, Real.exp (t*weightedSum a x (n+1) ω) ∂μ) =
        ∫ ω, μ[fun ω => Real.exp (t*weightedSum a x (n+1) ω) | ℱ n] ω ∂μ :=
          (integral_condExp (ℱ.le n)).symm
      _ ≤ ∫ ω, Real.exp (t*weightedSum a x n ω)*Real.exp ((t*a (n+1))^2/2) ∂μ :=
        integral_mono_ae integrable_condExp (hi.mul_const _) (exp_sum_conditional_upper hx a n t)
      _ = (∫ ω, Real.exp (t*weightedSum a x n ω) ∂μ)*Real.exp ((t*a (n+1))^2/2) := by
        rw [integral_mul_const]
      _ ≤ Real.exp (t^2*sqWeightSum a n/2)*Real.exp ((t*a (n+1))^2/2) :=
        mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = Real.exp (t^2*sqWeightSum a (n+1)/2) := by
        rw [← Real.exp_add, sqWeightSum_succ]
        congr 1
        ring
end AzumaWeightedSums.IteratedLog.AWFresh
-- END MODULE AWProof.MGF

-- BEGIN MODULE AWProof.MaximalTail
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace AzumaWeightedSums.IteratedLog.AWFresh
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}

theorem exp_max_tail (hx : IsCondSubgaussianOne μ ℱ x)
    (a : ℕ → ℝ) (N : ℕ) (t z : ℝ) :
    μ {ω | ∃ n ≤ N, t*z ≤ t*weightedSum a x n ω} ≤
      ENNReal.ofReal (Real.exp (-t*z+t^2*sqWeightSum a N/2)) := by
  let Y : ℕ → Ω → ℝ := fun n ω => Real.exp (t*weightedSum a x n ω)
  let e : ℝ≥0 := ⟨Real.exp (t*z), (Real.exp_pos _).le⟩
  let E := {ω | (e : ℝ) ≤ (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
    (fun n => Y n ω)}
  have hsub : Submartingale Y ℱ μ := exp_sum_submartingale hx a t
  have hnon : 0 ≤ Y := fun n ω => (Real.exp_pos _).le
  have hm := maximal_ineq hsub hnon (ε := e) N
  have hbound : (e : ℝ≥0∞)*μ E ≤ ENNReal.ofReal (Real.exp (t^2*sqWeightSum a N/2)) := by
    exact hm.trans (ENNReal.ofReal_le_ofReal
      ((setIntegral_le_integral (exp_sum_integrable hx a N t)
        (ae_of_all _ fun _ => (Real.exp_pos _).le)).trans (mgf_sum_le hx a N t)))
  have hecast : (e : ℝ≥0∞) = ENNReal.ofReal (Real.exp (t*z)) :=
    (ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le).symm
  have he0 : (e : ℝ≥0∞) ≠ 0 := by
    rw [hecast]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have heT : (e : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hdiv : μ E ≤ ENNReal.ofReal (Real.exp (t^2*sqWeightSum a N/2)) / e :=
    (ENNReal.le_div_iff_mul_le (Or.inl he0) (Or.inl heT)).mpr (by
      simpa only [mul_comm] using hbound)
  have hset : {ω | ∃ n ≤ N, t*z ≤ t*weightedSum a x n ω} ⊆ E := by
    intro ω hω
    obtain ⟨n, hn, h⟩ := hω
    exact (Real.exp_le_exp.mpr h).trans
      (Finset.le_sup' (fun n => Y n ω) (Finset.mem_range.mpr (by omega)))
  refine (measure_mono hset).trans (hdiv.trans_eq ?_)
  rw [hecast]
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  congr 2
  ring

theorem one_sided_tail (hx : IsCondSubgaussianOne μ ℱ x)
    (a : ℕ → ℝ) (N : ℕ) (U z : ℝ) (hU : 0 < U) (hz : 0 < z)
    (hV : sqWeightSum a N ≤ U) (sign : ℝ) (hs : sign^2 = 1) :
    μ {ω | ∃ n ≤ N, z ≤ sign*weightedSum a x n ω} ≤
      ENNReal.ofReal (Real.exp (-(z^2)/(2*U))) := by
  have ht : 0 < z/U := div_pos hz hU
  have hset : {ω | ∃ n ≤ N, z ≤ sign*weightedSum a x n ω} ⊆
      {ω | ∃ n ≤ N, (sign*(z/U))*(sign*z) ≤ (sign*(z/U))*weightedSum a x n ω} := by
    intro ω hω
    obtain ⟨n, hn, hh⟩ := hω
    refine ⟨n, hn, ?_⟩
    have h := mul_le_mul_of_nonneg_left hh ht.le
    have he : sign*(z/U)*(sign*z) = (z/U)*z := by
      calc
        _ = sign^2*((z/U)*z) := by ring
        _ = _ := by rw [hs, one_mul]
    rw [he]
    nlinarith only [h]
  refine (measure_mono hset).trans ((exp_max_tail hx a N (sign*(z/U)) (sign*z)).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hV (sq_nonneg (z/U))
  field_simp at *
  nlinarith [hs]
theorem finite_tail_bound (hx : IsCondSubgaussianOne μ ℱ x)
    (a : ℕ → ℝ) (N : ℕ) (U z : ℝ) (hU : 0 < U) (hz : 0 < z)
    (hV : sqWeightSum a N ≤ U) :
    μ {ω | ∃ n ≤ N, z ≤ |weightedSum a x n ω|} ≤
      ENNReal.ofReal (2*Real.exp (-(z^2)/(2*U))) := by
  let P := {ω | ∃ n ≤ N, z ≤ (1 : ℝ)*weightedSum a x n ω}
  let Q := {ω | ∃ n ≤ N, z ≤ (-1 : ℝ)*weightedSum a x n ω}
  have hp : μ P ≤ ENNReal.ofReal (Real.exp (-(z^2)/(2*U))) :=
    one_sided_tail hx a N U z hU hz hV 1 (by norm_num)
  have hq : μ Q ≤ ENNReal.ofReal (Real.exp (-(z^2)/(2*U))) :=
    one_sided_tail hx a N U z hU hz hV (-1) (by norm_num)
  have hs : {ω | ∃ n ≤ N, z ≤ |weightedSum a x n ω|} ⊆ P ∪ Q := by
    intro ω hω
    obtain ⟨n, hn, hh⟩ := hω
    rcases le_abs.mp hh with h | h
    · exact Or.inl ⟨n, hn, by simpa using h⟩
    · exact Or.inr ⟨n, hn, by simpa using h⟩
  calc
    _ ≤ μ (P ∪ Q) := measure_mono hs
    _ ≤ μ P + μ Q := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(z^2)/(2*U))) +
        ENNReal.ofReal (Real.exp (-(z^2)/(2*U))) := add_le_add hp hq
    _ = _ := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring
end AzumaWeightedSums.IteratedLog.AWFresh
-- END MODULE AWProof.MaximalTail

-- BEGIN MODULE AWProof.NativeConclusion

namespace AzumaWeightedSums.IteratedLog.AWFresh
open MeasureTheory ProbabilityTheory Filter Topology

theorem native_theorem2_limsup_le_one {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (a : ℕ → ℝ)
    (ha_ratio : Tendsto (fun n => a n ^ 2 / sqWeightSum a n) atTop (𝓝 0))
    (ha_div : Tendsto (fun n => sqWeightSum a n) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      |weightedSum a x n ω|
        ≤ (1 + ε) * Real.sqrt (2 * sqWeightSum a n
            * Real.log (Real.log (sqWeightSum a n))) := by
  have _h_ratio := ha_ratio
  intro ε hε
  exact lil_of_finite_tail μ (weightedSum a x) (sqWeightSum a)
    (sqWeightSum_mono a) (sqWeightSum_zero a) ha_div
    (fun N U z hU hz hV => finite_tail_bound hx a N U z hU hz hV)
    (1 + ε) (by linarith)

end AzumaWeightedSums.IteratedLog.AWFresh
-- END MODULE AWProof.NativeConclusion

-- BEGIN MODULE Canonical
open MeasureTheory ProbabilityTheory Filter Topology

namespace AzumaWeightedSums.IteratedLog

/-- Azuma 1967, Theorem 2, display (4.2), p. 362: if `(x_n)` satisfies [G] with
`τ(x_n) ≤ 1` for all `n`, and the real weights `(a_n)` satisfy (4.1),
`a_n²/D_n² → 0` and `D_n² → ∞`, then
`limsup_{n→∞} |S_n| / √(2 D_n² log log D_n²) ≤ 1` almost surely.
The lim sup is stated in its equivalent eventual form: for every `ε > 0`, almost surely,
`|S_n| ≤ (1 + ε) √(2 D_n² log log D_n²)` for all sufficiently large `n`. -/
theorem theorem2_limsup_le_one {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (a : ℕ → ℝ)
    (ha_ratio : Tendsto (fun n => a n ^ 2 / sqWeightSum a n) atTop (𝓝 0))
    (ha_div : Tendsto (fun n => sqWeightSum a n) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      |weightedSum a x n ω|
        ≤ (1 + ε) * Real.sqrt (2 * sqWeightSum a n
            * Real.log (Real.log (sqWeightSum a n))) := by
  exact AWFresh.native_theorem2_limsup_le_one hx a ha_ratio ha_div

end AzumaWeightedSums.IteratedLog
-- END MODULE Canonical

open MeasureTheory ProbabilityTheory Filter Topology AzumaWeightedSums.IteratedLog

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (a : ℕ → ℝ)
    (ha_ratio : Tendsto (fun n => a n ^ 2 / sqWeightSum a n) atTop (𝓝 0))
    (ha_div : Tendsto (fun n => sqWeightSum a n) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      |weightedSum a x n ω|
        ≤ (1 + ε) * Real.sqrt (2 * sqWeightSum a n
            * Real.log (Real.log (sqWeightSum a n))) := by
  exact AzumaWeightedSums.IteratedLog.theorem2_limsup_le_one hx a ha_ratio ha_div
