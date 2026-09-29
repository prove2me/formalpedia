-- Prove2me | solution 1 for BanditAlgorithm.bandit_kl_ucb_finite_to_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T03:50:49.756726+00:00
-- url     : https://prove2.me/submissions/2f9da938-dcf2-4129-b77b-3ea65a3a547b

import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_banditRegret
import Theorems.Thm_BanditAlgorithm_bernoulli_relative_entropy_pinsker
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.CompareExp
import Mathlib.Tactic.Linarith

open Filter Topology MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-! The analytic bridge in Exercise 10.2 of Lattimore--Szepesvári:
specialize the finite KL-UCB bound at a slowly vanishing epsilon and divide by
`log n`. -/

lemma tendsto_log_nat_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma one_le_klucbExploration (n : ℕ) :
    1 ≤ klucbExploration n := by
  rw [klucbExploration]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (Real.log (n : ℝ))))

lemma log_klucbExploration_nonneg (n : ℕ) :
    0 ≤ Real.log (klucbExploration n) :=
  Real.log_nonneg (one_le_klucbExploration n)

lemma klucbExploration_factorization (n : ℕ) (hn : 0 < n) :
    klucbExploration n =
      (n : ℝ) * ((n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2) := by
  simp [klucbExploration, mul_add, Nat.ne_of_gt hn]

lemma log_klucbExploration_factorization (n : ℕ) (hn : 0 < n) :
    Real.log (klucbExploration n) =
      Real.log (n : ℝ) +
        Real.log ((n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2) := by
  rw [klucbExploration_factorization n hn,
    Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
  positivity

lemma tendsto_log_log_nat_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_log_nat_atTop).tendsto_div_nhds_zero

lemma tendsto_klucbExploration_atTop :
    Tendsto (fun n : ℕ ↦ klucbExploration n) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_nat_atTop
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ hnat
  filter_upwards [hlog.eventually_ge_atTop 1] with n hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsquare : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  rw [klucbExploration]
  nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hsquare)]

lemma tendsto_log_klucbExploration_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (klucbExploration n)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_klucbExploration_atTop

lemma eventually_pos_log_klucbExploration :
    ∀ᶠ n : ℕ in atTop, 0 < Real.log (klucbExploration n) :=
  tendsto_log_klucbExploration_atTop.eventually_gt_atTop 0

lemma tendsto_inv_log_klucbExploration_zero :
    Tendsto (fun n : ℕ ↦ (Real.log (klucbExploration n))⁻¹)
      atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_klucbExploration_atTop

lemma tendsto_sqrt_log_klucbExploration_atTop :
    Tendsto (fun n : ℕ ↦ Real.sqrt (Real.log (klucbExploration n)))
      atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_log_klucbExploration_atTop

lemma tendsto_inv_sqrt_log_klucbExploration_zero :
    Tendsto
      (fun n : ℕ ↦ (Real.sqrt (Real.log (klucbExploration n)))⁻¹)
      atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_sqrt_log_klucbExploration_atTop

lemma tendsto_sqrt_pi_mul_inv_sqrt_log_klucbExploration_zero :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt Real.pi *
        (Real.sqrt (Real.log (klucbExploration n)))⁻¹)
      atTop (𝓝 0) :=
  by
    simpa using
      (tendsto_const_nhds (x := Real.sqrt Real.pi)).mul
        tendsto_inv_sqrt_log_klucbExploration_zero

lemma tendsto_sqrt_pi_log_schedule_div_log_schedule_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.sqrt (Real.pi * Real.log (klucbExploration n)) /
          Real.log (klucbExploration n))
      atTop (𝓝 0) := by
  refine tendsto_sqrt_pi_mul_inv_sqrt_log_klucbExploration_zero.congr' ?_
  filter_upwards [eventually_pos_log_klucbExploration] with n hn
  rw [Real.sqrt_mul (le_of_lt Real.pi_pos), mul_div_assoc,
    Real.sqrt_div_self]

lemma tendsto_fourthRoot_log_klucbExploration_atTop :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt
        (Real.sqrt (Real.log (klucbExploration n))))
      atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_sqrt_log_klucbExploration_atTop

/-- The vanishing epsilon `log(f(n))^(-1/4)` used for Exercise 10.2. -/
lemma tendsto_inv_fourthRoot_log_klucbExploration_zero :
    Tendsto
      (fun n : ℕ ↦
        (Real.sqrt (Real.sqrt (Real.log (klucbExploration n))))⁻¹)
      atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    tendsto_fourthRoot_log_klucbExploration_atTop

lemma eventually_pos_inv_fourthRoot_log_klucbExploration :
    ∀ᶠ n : ℕ in atTop,
      0 < (Real.sqrt
        (Real.sqrt (Real.log (klucbExploration n))))⁻¹ := by
  filter_upwards
    [tendsto_fourthRoot_log_klucbExploration_atTop.eventually_gt_atTop 0]
      with n hn
  exact inv_pos.mpr hn

lemma eventually_inv_fourthRoot_log_klucbExploration_lt
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (Real.sqrt
        (Real.sqrt (Real.log (klucbExploration n))))⁻¹ < δ :=
  (tendsto_order.1
    tendsto_inv_fourthRoot_log_klucbExploration_zero).2 δ hδ

lemma eventually_inv_fourthRoot_log_klucbExploration_admissible
    {k : ℕ} (Δ : Fin k → ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ i, 0 < Δ i →
      0 < (Real.sqrt
        (Real.sqrt (Real.log (klucbExploration n))))⁻¹ ∧
      (Real.sqrt
        (Real.sqrt (Real.log (klucbExploration n))))⁻¹ < Δ i := by
  rw [eventually_all]
  intro i
  by_cases hi : 0 < Δ i
  · filter_upwards
      [eventually_pos_inv_fourthRoot_log_klucbExploration,
        eventually_inv_fourthRoot_log_klucbExploration_lt hi]
        with n hnpos hnlt
    exact fun _ ↦ ⟨hnpos, hnlt⟩
  · exact Filter.Eventually.of_forall (fun _ hpos ↦ (hi hpos).elim)

noncomputable def klucbAsymptoticEpsilon (n : ℕ) : ℝ :=
  (Real.sqrt (Real.sqrt (Real.log (klucbExploration n))))⁻¹

lemma tendsto_inv_log_nat_zero :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop

lemma tendsto_log_two_div_log_nat_zero :
    Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds (x := Real.log 2)).mul tendsto_inv_log_nat_zero

lemma tendsto_two_mul_log_log_nat_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        2 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  convert
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      tendsto_log_log_nat_div_log_nat_zero using 1 <;> ring

lemma tendsto_log_two_log_sq_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.log (2 * Real.log (n : ℝ) ^ 2) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          Real.log 2 / Real.log (n : ℝ) +
            2 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
        atTop (𝓝 0) := by
    simpa using tendsto_log_two_div_log_nat_zero.add
      tendsto_two_mul_log_log_nat_div_log_nat_zero
  refine hsum.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hn
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (pow_ne_zero 2 (ne_of_gt hn)), Real.log_pow]
  ring

lemma tendsto_log_schedule_correction_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.log ((n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2) /
          Real.log (n : ℝ))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_log_two_log_sq_div_log_nat_zero
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
    have hsq : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
    have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    have hsum : 1 ≤ (n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2 := by linarith
    exact div_nonneg (Real.log_nonneg hsum) (by linarith)
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
    have hn_ne : n ≠ 0 := by
      intro hn0
      subst n
      norm_num at hn
    have hn_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn_ne)
    have hn_cast_one : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn_ne
    have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn_cast_one
    have hsq : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
    have hsum_pos : 0 < (n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2 := by positivity
    have hsum_le :
        (n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2 ≤
          2 * Real.log (n : ℝ) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hsum_pos hsum_le) (by linarith)

lemma tendsto_log_klucbExploration_div_log_nat_one :
    Tendsto
      (fun n : ℕ ↦
        Real.log (klucbExploration n) / Real.log (n : ℝ))
      atTop (𝓝 1) := by
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          1 +
            Real.log ((n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2) /
              Real.log (n : ℝ))
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      tendsto_log_schedule_correction_div_log_nat_zero
  refine hsum.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hn
  have hn_ne : n ≠ 0 := by
    intro hn0
    subst n
    norm_num at hn
  rw [log_klucbExploration_factorization n (Nat.pos_of_ne_zero hn_ne)]
  field_simp

lemma tendsto_klucbAsymptoticEpsilon_zero :
    Tendsto klucbAsymptoticEpsilon atTop (𝓝 0) := by
  exact tendsto_inv_fourthRoot_log_klucbExploration_zero


lemma eventually_klucbAsymptoticEpsilon_admissible
    {k : ℕ} (Δ : Fin k → ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ i, 0 < Δ i →
      0 < klucbAsymptoticEpsilon n ∧
      0 < klucbAsymptoticEpsilon n ∧
      klucbAsymptoticEpsilon n + klucbAsymptoticEpsilon n < Δ i := by
  rw [eventually_all]
  intro i
  by_cases hi : 0 < Δ i
  · filter_upwards
      [eventually_pos_inv_fourthRoot_log_klucbExploration,
        eventually_inv_fourthRoot_log_klucbExploration_lt
          (half_pos hi)]
        with n hnpos hnlt
    intro _
    refine ⟨?_, ?_, ?_⟩
    · simpa [klucbAsymptoticEpsilon] using hnpos
    · simpa [klucbAsymptoticEpsilon] using hnpos
    · simpa [klucbAsymptoticEpsilon] using (show
        (Real.sqrt (Real.sqrt (Real.log (klucbExploration n))))⁻¹ +
            (Real.sqrt (Real.sqrt (Real.log (klucbExploration n))))⁻¹ <
          Δ i by linarith)
  · exact Filter.Eventually.of_forall (fun _ hpos ↦ (hi hpos).elim)

lemma tendsto_sqrt_log_klucbExploration_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.sqrt (Real.log (klucbExploration n)) /
          Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hprod := tendsto_log_klucbExploration_div_log_nat_one.mul
    tendsto_inv_sqrt_log_klucbExploration_zero
  have hprod' :
      Tendsto
        (fun n : ℕ ↦
          (Real.log (klucbExploration n) / Real.log (n : ℝ)) *
            (Real.sqrt (Real.log (klucbExploration n)))⁻¹)
        atTop (𝓝 0) := by simpa using hprod
  refine hprod'.congr' ?_
  filter_upwards [eventually_pos_log_klucbExploration,
    tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hL hn
  have hsqrt : 0 < Real.sqrt (Real.log (klucbExploration n)) :=
    Real.sqrt_pos.2 hL
  field_simp [ne_of_gt hsqrt, ne_of_gt hn]
  rw [Real.sq_sqrt hL.le]

lemma tendsto_klucb_penalty_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        (1 / (2 * klucbAsymptoticEpsilon n ^ 2) +
          2 / klucbAsymptoticEpsilon n ^ 2) /
            Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hscaled :=
    (tendsto_const_nhds (x := (5 / 2 : ℝ))).mul
      tendsto_sqrt_log_klucbExploration_div_log_nat_zero
  have hscaled' :
      Tendsto
        (fun n : ℕ ↦
          (5 / 2 : ℝ) *
            (Real.sqrt (Real.log (klucbExploration n)) /
              Real.log (n : ℝ)))
        atTop (𝓝 0) := by simpa using hscaled
  refine hscaled'.congr' ?_
  filter_upwards [eventually_pos_log_klucbExploration,
    tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hL hn
  have hsqrt : 0 < Real.sqrt (Real.log (klucbExploration n)) :=
    Real.sqrt_pos.2 hL
  have hfourth :
      0 < Real.sqrt (Real.sqrt (Real.log (klucbExploration n))) :=
    Real.sqrt_pos.2 hsqrt
  rw [klucbAsymptoticEpsilon]
  field_simp [ne_of_gt hfourth, ne_of_gt hn]
  rw [Real.sq_sqrt hsqrt.le]
  ring

lemma bernoulliRelativeEntropy_eq_expanded_asym
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) :
    bernoulliRelativeEntropy p q =
      p * Real.log p - p * Real.log q +
        (1 - p) * Real.log (1 - p) -
          (1 - p) * Real.log (1 - q) := by
  rw [bernoulliRelativeEntropy,
    Real.log_div (ne_of_gt hp) (ne_of_gt hq),
    Real.log_div (by linarith) (by linarith)]
  ring

lemma tendsto_bernoulliRelativeEntropy_asym
    {α : Type} {l : Filter α} {p q : ℝ}
    {P Q : α → ℝ}
    (hP : Tendsto P l (𝓝 p)) (hQ : Tendsto Q l (𝓝 q))
    (hP0 : ∀ᶠ x in l, 0 < P x) (hP1 : ∀ᶠ x in l, P x < 1)
    (hQ0 : ∀ᶠ x in l, 0 < Q x) (hQ1 : ∀ᶠ x in l, Q x < 1)
    (hp : 0 ≤ p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun x ↦ bernoulliRelativeEntropy (P x) (Q x))
      l (𝓝 (bernoulliRelativeEntropy p q)) := by
  let E : ℝ → ℝ → ℝ := fun x y ↦
    x * Real.log x - x * Real.log y +
      (1 - x) * Real.log (1 - x) -
        (1 - x) * Real.log (1 - y)
  have hE : Tendsto (fun x ↦ E (P x) (Q x)) l (𝓝 (E p q)) := by
    dsimp [E]
    have hOneP : Tendsto (fun x ↦ 1 - P x) l (𝓝 (1 - p)) :=
      tendsto_const_nhds.sub hP
    have hOneQ : Tendsto (fun x ↦ 1 - Q x) l (𝓝 (1 - q)) :=
      tendsto_const_nhds.sub hQ
    have hPlogP : Tendsto (fun x ↦ P x * Real.log (P x))
        l (𝓝 (p * Real.log p)) :=
      Real.continuous_mul_log.continuousAt.tendsto.comp hP
    have hOnePlog : Tendsto
        (fun x ↦ (1 - P x) * Real.log (1 - P x))
        l (𝓝 ((1 - p) * Real.log (1 - p))) :=
      Real.continuous_mul_log.continuousAt.tendsto.comp hOneP
    have hLogQ : Tendsto (fun x ↦ Real.log (Q x)) l (𝓝 (Real.log q)) :=
      (Real.continuousAt_log hq.ne').tendsto.comp hQ
    have hLogOneQ : Tendsto (fun x ↦ Real.log (1 - Q x))
        l (𝓝 (Real.log (1 - q))) :=
      (Real.continuousAt_log (by linarith : 1 - q ≠ 0)).tendsto.comp hOneQ
    exact ((hPlogP.sub (hP.mul hLogQ)).add hOnePlog).sub
      (hOneP.mul hLogOneQ)
  have hlim : bernoulliRelativeEntropy p q = E p q := by
    dsimp [E]
    by_cases hp0 : p = 0
    · subst p
      rw [bernoulliRelativeEntropy]
      simp [Real.log_inv]
    · rw [bernoulliRelativeEntropy_eq_expanded_asym
        (lt_of_le_of_ne hp (Ne.symm hp0)) hp1 hq hq1]
  rw [hlim]
  refine hE.congr' ?_
  filter_upwards [hP0, hP1, hQ0, hQ1] with x hpx0 hpx1 hqx0 hqx1
  rw [bernoulliRelativeEntropy_eq_expanded_asym
    hpx0 hpx1 hqx0 hqx1]

lemma banditArmMean_bernoulli_asym
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (i : Fin k) :
    banditArmMean ν i = μvec i := by
  rw [hν, banditArmMean, bernoulliBandit]
  change (∫ x : ℝ, x ∂(ENNReal.ofReal (μvec i) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - μvec i) • Measure.dirac (0 : ℝ))) = μvec i
  rw [integral_add_measure
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (1 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (0 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)]
  rcases hμ i with ⟨h0, h1⟩
  simp [ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (show 0 ≤ 1 - μvec i by linarith)]

lemma tendsto_klucb_arm_bound_div_log_nat
    {p q Δ : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hpq : p < q) (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto
      (fun n : ℕ ↦
        Δ *
          (Real.log (klucbExploration n) /
              bernoulliRelativeEntropy
                (p + klucbAsymptoticEpsilon n)
                (q - klucbAsymptoticEpsilon n) +
            1 / (2 * klucbAsymptoticEpsilon n ^ 2) +
            2 / klucbAsymptoticEpsilon n ^ 2) /
          Real.log (n : ℝ))
      atTop
      (𝓝 (Δ / bernoulliRelativeEntropy p q)) := by
  have hP : Tendsto (fun n : ℕ ↦ p + klucbAsymptoticEpsilon n)
      atTop (𝓝 p) := by
    simpa using tendsto_const_nhds.add tendsto_klucbAsymptoticEpsilon_zero
  have hQ : Tendsto (fun n : ℕ ↦ q - klucbAsymptoticEpsilon n)
      atTop (𝓝 q) := by
    simpa using tendsto_const_nhds.sub tendsto_klucbAsymptoticEpsilon_zero
  have hP0 : ∀ᶠ n : ℕ in atTop,
      0 < p + klucbAsymptoticEpsilon n := by
    filter_upwards
      [eventually_pos_inv_fourthRoot_log_klucbExploration] with n hn
    rw [klucbAsymptoticEpsilon]
    linarith [hp.1]
  have hP1 : ∀ᶠ n : ℕ in atTop,
      p + klucbAsymptoticEpsilon n < 1 :=
    (tendsto_order.1 hP).2 1 (lt_of_lt_of_le hpq hq1.le)
  have hQ0 : ∀ᶠ n : ℕ in atTop,
      0 < q - klucbAsymptoticEpsilon n :=
    (tendsto_order.1 hQ).1 0 hq0
  have hQ1 : ∀ᶠ n : ℕ in atTop,
      q - klucbAsymptoticEpsilon n < 1 := by
    filter_upwards
      [eventually_pos_inv_fourthRoot_log_klucbExploration] with n hn
    rw [klucbAsymptoticEpsilon]
    linarith
  have hD : Tendsto
      (fun n : ℕ ↦
        bernoulliRelativeEntropy
          (p + klucbAsymptoticEpsilon n)
          (q - klucbAsymptoticEpsilon n))
      atTop (𝓝 (bernoulliRelativeEntropy p q)) :=
    tendsto_bernoulliRelativeEntropy_asym hP hQ hP0 hP1 hQ0 hQ1
      hp.1 (lt_of_lt_of_le hpq hq1.le) hq0 hq1
  have hdpos : 0 < bernoulliRelativeEntropy p q := by
    have hpin := bernoulli_relative_entropy_pinsker p q hp ⟨hq0, hq1⟩
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hpq))]
  have hInv : Tendsto
      (fun n : ℕ ↦
        (bernoulliRelativeEntropy
          (p + klucbAsymptoticEpsilon n)
          (q - klucbAsymptoticEpsilon n))⁻¹)
      atTop (𝓝 (bernoulliRelativeEntropy p q)⁻¹) :=
    hD.inv₀ hdpos.ne'
  have hMain := tendsto_log_klucbExploration_div_log_nat_one.mul hInv
  have hInside :
      Tendsto
        (fun n : ℕ ↦
          (Real.log (klucbExploration n) /
                bernoulliRelativeEntropy
                  (p + klucbAsymptoticEpsilon n)
                  (q - klucbAsymptoticEpsilon n) +
              1 / (2 * klucbAsymptoticEpsilon n ^ 2) +
              2 / klucbAsymptoticEpsilon n ^ 2) /
            Real.log (n : ℝ))
        atTop (𝓝 ((bernoulliRelativeEntropy p q)⁻¹)) := by
    have hMain' :
        Tendsto
          (fun n : ℕ ↦
            (Real.log (klucbExploration n) / Real.log (n : ℝ)) *
              (bernoulliRelativeEntropy
                (p + klucbAsymptoticEpsilon n)
                (q - klucbAsymptoticEpsilon n))⁻¹)
          atTop (𝓝 ((bernoulliRelativeEntropy p q)⁻¹)) := by
      simpa using hMain
    have hsum := hMain'.add tendsto_klucb_penalty_div_log_nat_zero
    have hsum' :
        Tendsto
          (fun n : ℕ ↦
            (Real.log (klucbExploration n) / Real.log (n : ℝ)) *
                (bernoulliRelativeEntropy
                  (p + klucbAsymptoticEpsilon n)
                  (q - klucbAsymptoticEpsilon n))⁻¹ +
              (1 / (2 * klucbAsymptoticEpsilon n ^ 2) +
                2 / klucbAsymptoticEpsilon n ^ 2) /
                  Real.log (n : ℝ))
          atTop (𝓝 ((bernoulliRelativeEntropy p q)⁻¹)) := by
      simpa using hsum
    refine hsum'.congr' ?_
    filter_upwards
      [tendsto_log_nat_atTop.eventually_ne_atTop 0,
        (tendsto_order.1 hD).1 0 hdpos]
      with n hnlog hnD
    field_simp [hnlog, ne_of_gt hnD]
    ring
  have hScaled := (tendsto_const_nhds (x := Δ)).mul hInside
  simpa only [div_eq_mul_inv, mul_assoc] using hScaled

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (hπ : IsKLUCBPolicy π)
    (hfinite :
      ∀ n : ℕ, ∀ ε₁ ε₂ : Fin k → ℝ,
        (∀ i, 0 < banditGap ν i →
          0 < ε₁ i ∧ 0 < ε₂ i ∧
            ε₁ i + ε₂ i < banditGap ν i) →
        banditRegret ν π n ≤
          ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
            banditGap ν i *
              (Real.log (klucbExploration n) /
                  bernoulliRelativeEntropy
                    (banditArmMean ν i + ε₁ i)
                    (banditOptimalMean ν - ε₂ i) +
                1 / (2 * ε₁ i ^ 2) + 2 / ε₂ i ^ 2)) :
    atTop.limsup
        (fun n : ℕ ↦ ENNReal.ofReal (banditRegret ν π n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
        ENNReal.ofReal (banditGap ν i) /
          ENNReal.ofReal
            (bernoulliRelativeEntropy (banditArmMean ν i)
              (banditOptimalMean ν)) := by
  classical
  let S : Finset (Fin k) :=
    Finset.univ.filter (fun i ↦ 0 < banditGap ν i)
  by_cases hS : S = ∅
  · have hbound : ∀ n : ℕ, banditRegret ν π n ≤ 0 := by
      intro n
      have hε : ∀ i, 0 < banditGap ν i →
          0 < (1 : ℝ) ∧ 0 < (1 : ℝ) ∧
            (1 : ℝ) + 1 < banditGap ν i := by
        intro i hi
        have himem : i ∈ S := by
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
        rw [hS] at himem
        simp at himem
      simpa [S, hS] using
        hfinite n (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ)) hε
    have hpoint :
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal (banditRegret ν π n / Real.log n) ≤
            (0 : ENNReal) := by
      filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0]
        with n hn
      rw [ENNReal.ofReal_eq_zero.mpr
        (div_nonpos_of_nonpos_of_nonneg (hbound n) hn.le)]
    calc
      atTop.limsup
          (fun n : ℕ ↦
            ENNReal.ofReal (banditRegret ν π n / Real.log n)) ≤
          atTop.limsup (fun _n : ℕ ↦ (0 : ENNReal)) :=
        limsup_le_limsup hpoint
      _ = 0 := tendsto_const_nhds.limsup_eq
      _ = ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
          ENNReal.ofReal (banditGap ν i) /
            ENNReal.ofReal
              (bernoulliRelativeEntropy (banditArmMean ν i)
                (banditOptimalMean ν)) := by
        change (0 : ENNReal) = ∑ i ∈ S,
          ENNReal.ofReal (banditGap ν i) /
            ENNReal.ofReal
              (bernoulliRelativeEntropy (banditArmMean ν i)
                (banditOptimalMean ν))
        rw [hS]
        simp
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS
    letI : Nonempty (Fin k) := ⟨hSne.choose⟩
    obtain ⟨a, ha⟩ :
        ∃ a : Fin k, banditArmMean ν a =
          ⨆ j, banditArmMean ν j :=
      exists_eq_ciSup_of_finite
    have ha' : banditArmMean ν a = banditOptimalMean ν := by
      simpa [banditOptimalMean] using ha
    have hmean (j : Fin k) : banditArmMean ν j = μvec j :=
      banditArmMean_bernoulli_asym μvec hμ ν hν j
    have hqmem : banditOptimalMean ν ∈ Set.Icc (0 : ℝ) 1 := by
      rw [← ha', hmean]
      exact hμ a
    have hqpos : 0 < banditOptimalMean ν := by
      obtain ⟨i, hiS⟩ := hSne
      have higap : 0 < banditGap ν i := (Finset.mem_filter.1 hiS).2
      rw [banditGap] at higap
      have hip0 : 0 ≤ banditArmMean ν i := by
        rw [hmean]
        exact (hμ i).1
      linarith
    by_cases hqtop : banditOptimalMean ν = 1
    · have hRHS :
          (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
            ENNReal.ofReal (banditGap ν i) /
              ENNReal.ofReal
                (bernoulliRelativeEntropy (banditArmMean ν i)
                  (banditOptimalMean ν))) = (⊤ : ENNReal) := by
        rw [ENNReal.sum_eq_top]
        obtain ⟨i, hiS⟩ := hSne
        refine ⟨i, ?_, ?_⟩
        · simpa [S] using hiS
        · have higap : 0 < banditGap ν i :=
            (Finset.mem_filter.1 hiS).2
          have hip : banditArmMean ν i ∈ Set.Icc (0 : ℝ) 1 := by
            rw [hmean]
            exact hμ i
          have hdnonpos :
              bernoulliRelativeEntropy (banditArmMean ν i)
                  (banditOptimalMean ν) ≤ 0 := by
            rw [hqtop, bernoulliRelativeEntropy]
            simp
            exact Real.mul_log_nonpos hip.1 hip.2
          rw [ENNReal.ofReal_eq_zero.mpr hdnonpos]
          exact ENNReal.div_zero
            (ne_of_gt (ENNReal.ofReal_pos.mpr higap))
      rw [hRHS]
      exact le_top
    · have hq1 : banditOptimalMean ν < 1 :=
        lt_of_le_of_ne hqmem.2 hqtop
      let B : ℕ → ℝ := fun n ↦
        (∑ i ∈ S,
          banditGap ν i *
            (Real.log (klucbExploration n) /
                bernoulliRelativeEntropy
                  (banditArmMean ν i + klucbAsymptoticEpsilon n)
                  (banditOptimalMean ν - klucbAsymptoticEpsilon n) +
              1 / (2 * klucbAsymptoticEpsilon n ^ 2) +
              2 / klucbAsymptoticEpsilon n ^ 2)) /
          Real.log (n : ℝ)
      let C : ℝ := ∑ i ∈ S,
        banditGap ν i /
          bernoulliRelativeEntropy
            (banditArmMean ν i) (banditOptimalMean ν)
      have hBreal : Tendsto B atTop (𝓝 C) := by
        dsimp [B, C]
        simpa only [Finset.sum_div] using
          tendsto_finset_sum S (fun i hi ↦ by
            have higap : 0 < banditGap ν i :=
              (Finset.mem_filter.1 hi).2
            have hip : banditArmMean ν i ∈ Set.Icc (0 : ℝ) 1 := by
              rw [hmean]
              exact hμ i
            have hipq : banditArmMean ν i < banditOptimalMean ν := by
              rw [banditGap] at higap
              linarith
            exact tendsto_klucb_arm_bound_div_log_nat
              (Δ := banditGap ν i) hip hipq hqpos hq1)
      have hBenn : Tendsto (fun n ↦ ENNReal.ofReal (B n))
          atTop (𝓝 (ENNReal.ofReal C)) :=
        ENNReal.tendsto_ofReal hBreal
      have hpoint :
          ∀ᶠ n : ℕ in atTop,
            ENNReal.ofReal (banditRegret ν π n / Real.log n) ≤
              ENNReal.ofReal (B n) := by
        filter_upwards
          [eventually_klucbAsymptoticEpsilon_admissible
              (fun i ↦ banditGap ν i),
            tendsto_log_nat_atTop.eventually_gt_atTop 0]
          with n hnε hnlog
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ hnlog.le
        simpa [B, S] using
          hfinite n
            (fun _ ↦ klucbAsymptoticEpsilon n)
            (fun _ ↦ klucbAsymptoticEpsilon n) hnε
      have hC :
          ENNReal.ofReal C =
            ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
              ENNReal.ofReal (banditGap ν i) /
                ENNReal.ofReal
                  (bernoulliRelativeEntropy (banditArmMean ν i)
                    (banditOptimalMean ν)) := by
        rw [show Finset.univ.filter
            (fun i ↦ 0 < banditGap ν i) = S by rfl]
        dsimp [C]
        rw [ENNReal.ofReal_sum_of_nonneg]
        · apply Finset.sum_congr rfl
          intro i hi
          have higap : 0 < banditGap ν i :=
            (Finset.mem_filter.1 hi).2
          have hip : banditArmMean ν i ∈ Set.Icc (0 : ℝ) 1 := by
            rw [hmean]
            exact hμ i
          have hipq : banditArmMean ν i < banditOptimalMean ν := by
            rw [banditGap] at higap
            linarith
          have hdpos :
              0 < bernoulliRelativeEntropy
                (banditArmMean ν i) (banditOptimalMean ν) := by
            have hpinsker := bernoulli_relative_entropy_pinsker
              (banditArmMean ν i) (banditOptimalMean ν)
              hip ⟨hqpos, hq1⟩
            nlinarith [sq_pos_of_ne_zero
              (sub_ne_zero.mpr (ne_of_lt hipq))]
          exact ENNReal.ofReal_div_of_pos hdpos
        · intro i hi
          have higap : 0 < banditGap ν i :=
            (Finset.mem_filter.1 hi).2
          have hip : banditArmMean ν i ∈ Set.Icc (0 : ℝ) 1 := by
            rw [hmean]
            exact hμ i
          have hipq : banditArmMean ν i < banditOptimalMean ν := by
            rw [banditGap] at higap
            linarith
          have hdpos :
              0 < bernoulliRelativeEntropy
                (banditArmMean ν i) (banditOptimalMean ν) := by
            have hpinsker := bernoulli_relative_entropy_pinsker
              (banditArmMean ν i) (banditOptimalMean ν)
              hip ⟨hqpos, hq1⟩
            nlinarith [sq_pos_of_ne_zero
              (sub_ne_zero.mpr (ne_of_lt hipq))]
          exact div_nonneg higap.le hdpos.le
      calc
        atTop.limsup
            (fun n : ℕ ↦
              ENNReal.ofReal (banditRegret ν π n / Real.log n)) ≤
            atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal (B n)) :=
          limsup_le_limsup hpoint
        _ = ENNReal.ofReal C := hBenn.limsup_eq
        _ = ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
            ENNReal.ofReal (banditGap ν i) /
              ENNReal.ofReal
                (bernoulliRelativeEntropy (banditArmMean ν i)
                  (banditOptimalMean ν)) := hC
