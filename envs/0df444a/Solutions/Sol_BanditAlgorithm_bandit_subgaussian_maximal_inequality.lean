-- Prove2me | solution 1 for BanditAlgorithm.bandit_subgaussian_maximal_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-07-20T19:00:08.368894+00:00
-- url     : https://prove2.me/submissions/b8e66b30-9aa5-4bbe-a998-c84f4b44713e

import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.BorelCantelli
import Mathlib.Analysis.Convex.Integral

/-!
Direct-proof development for Lattimore--Szepesvari, *Bandit Algorithms*,
Theorem 9.2, printed p. 124 / PDF p. 133, Eq. (9.1).  The source applies
Doob's maximal inequality to `exp (lambda * S_t)` and optimizes at
`lambda = epsilon / (n * sigma^2)`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MaximalSubgaussianDirectScratch

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {P : Measure Omega}
    [IsProbabilityMeasure P]

lemma hasSubgaussianMGF_integral_eq_zero {Z : Omega -> Real} {c : NNReal}
    (hZ : HasSubgaussianMGF Z c P) : P[Z] = 0 := by
  have hzero_mem : (0 : Real) ∈ interior (integrableExpSet Z P) := by
    rw [hZ.integrableExpSet_eq_univ]
    simp
  let g : Real -> Real := fun t => exp ((c : Real) * t ^ 2 / 2) - mgf Z P t
  have hg_min : IsLocalMin g 0 := by
    filter_upwards [] with t
    change g 0 <= g t
    simp only [g, zero_pow, mul_zero, zero_div, exp_zero, mgf_zero]
    simpa using hZ.mgf_le t
  have hg_deriv : deriv g 0 = 0 := hg_min.deriv_eq_zero
  have hbound_deriv : HasDerivAt (fun t : Real => exp ((c : Real) * t ^ 2 / 2)) 0 0 := by
    convert (((hasDerivAt_id (x := (0 : Real))).pow 2).const_mul (c : Real) |>.div_const 2 |>.exp)
      using 1 <;> norm_num
  have hmgf_deriv := hasDerivAt_mgf hzero_mem
  have hg_hasDeriv : HasDerivAt g (-P[Z]) 0 := by
    have h := hbound_deriv.sub hmgf_deriv
    simp only [zero_mul, exp_zero, mul_one, zero_sub] at h
    exact h
  rw [hg_hasDeriv.deriv] at hg_deriv
  linarith

lemma one_le_mgf_of_hasSubgaussianMGF {Z : Omega -> Real} {c : NNReal}
    (hZ : HasSubgaussianMGF Z c P) (lambda : Real) : 1 <= mgf Z P lambda := by
  have hmean : P[Z] = 0 := hasSubgaussianMGF_integral_eq_zero hZ
  have hjensen := convexOn_exp.map_integral_le (μ := P) (f := fun omega => lambda * Z omega)
    continuousOn_exp isClosed_univ (by simp) (hZ.integrable.const_mul lambda)
    (hZ.integrable_exp_mul lambda)
  simpa [mgf, integral_const_mul, hmean] using hjensen

variable {X : Nat -> Omega -> Real} {sigma : NNReal}

lemma terminal_sum_subgaussian (h_indep : iIndepFun X P)
    (h_subG : forall i, HasSubgaussianMGF (X i) (sigma ^ 2) P) (n : Nat) :
    HasSubgaussianMGF (fun omega => ∑ i ∈ Finset.range n, X i omega)
      (∑ i ∈ Finset.range n, sigma ^ 2) P :=
  HasSubgaussianMGF.sum_of_iIndepFun h_indep (fun i hi => h_subG i)

lemma optimized_exponent {n : Nat} (hn : 0 < n) {sigma : NNReal} (hsigma : 0 < sigma)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    (n : Real) * (sigma : Real) ^ 2 *
          (epsilon / ((n : Real) * (sigma : Real) ^ 2)) ^ 2 / 2 -
        (epsilon / ((n : Real) * (sigma : Real) ^ 2)) * epsilon =
      -epsilon ^ 2 / (2 * n * (sigma : Real) ^ 2) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hsigmaR : (0 : Real) < (sigma : Real) := by exact_mod_cast hsigma
  field_simp
  ring

lemma exp_partial_sum_submartingale (hX : forall i, StronglyMeasurable (X i))
    (h_indep : iIndepFun X P)
    (h_subG : forall i, HasSubgaussianMGF (X i) (sigma ^ 2) P) (lambda : Real) :
    Submartingale
      (fun i omega => exp (lambda * (∑ s ∈ Finset.range (i + 1), X s omega)))
      (Filtration.natural X hX) P := by
  let F := Filtration.natural X hX
  let S : Nat -> Omega -> Real :=
    fun i omega => ∑ s ∈ Finset.range (i + 1), X s omega
  let M : Nat -> Omega -> Real := fun i omega => exp (lambda * S i omega)
  change Submartingale M F P
  have hX_adapted : StronglyAdapted F X := Filtration.stronglyAdapted_natural hX
  have hS_adapted : StronglyAdapted F S := by
    intro i
    dsimp only [S]
    have heq : (fun omega => ∑ s ∈ Finset.range (i + 1), X s omega) =
        (∑ s ∈ Finset.range (i + 1), X s) := by
      funext omega
      simp
    rw [heq]
    exact Finset.stronglyMeasurable_sum (Finset.range (i + 1)) (fun s hs =>
      hX_adapted.stronglyMeasurable_le (Nat.le_of_lt_succ (Finset.mem_range.mp hs)))
  have hM_adapted : StronglyAdapted F M := by
    intro i
    exact continuous_exp.comp_stronglyMeasurable ((hS_adapted i).const_mul lambda)
  have hM_int : forall i, Integrable (M i) P := by
    intro i
    simpa only [M, S] using
      (terminal_sum_subgaussian h_indep h_subG (i + 1)).integrable_exp_mul lambda
  refine submartingale_nat hM_adapted hM_int ?_
  intro i
  have hXi_int : Integrable (fun omega => exp (lambda * X (i + 1) omega)) P :=
    (h_subG (i + 1)).integrable_exp_mul lambda
  have hM_succ_eq : M (i + 1) =
      M i * (fun omega => exp (lambda * X (i + 1) omega)) := by
    funext omega
    simp only [M, S, Pi.mul_apply, Finset.sum_range_succ]
    rw [mul_add, exp_add]
  have hprod_int : Integrable
      (M i * (fun omega => exp (lambda * X (i + 1) omega))) P := by
    rw [← hM_succ_eq]
    exact hM_int (i + 1)
  have hnext_indep :
      Indep (MeasurableSpace.comap (X (i + 1)) inferInstance) (F i) P := by
    exact h_indep.indep_comap_natural_of_lt hX (Nat.lt_succ_self i)
  have hcond_next :
      P[fun omega => exp (lambda * X (i + 1) omega) | F i] =ᵐ[P]
        fun _ => mgf (X (i + 1)) P lambda := by
    apply condExp_indep_eq (m₁ := MeasurableSpace.comap (X (i + 1)) inferInstance)
      (m₂ := F i) (m := mOmega)
    · exact (hX (i + 1)).measurable.comap_le
    · exact (Measurable.stronglyMeasurable
        (measurable_exp.comp (measurable_const.mul (Measurable.of_comap_le le_rfl))) :
        StronglyMeasurable[MeasurableSpace.comap (X (i + 1)) inferInstance]
          (fun omega => exp (lambda * X (i + 1) omega)))
    · exact hnext_indep
  rw [hM_succ_eq]
  filter_upwards [condExp_mul_of_stronglyMeasurable_left (hM_adapted i)
      hprod_int hXi_int, hcond_next] with omega hpull hcond
  rw [hpull, Pi.mul_apply, hcond]
  exact le_mul_of_one_le_right (exp_nonneg _) (one_le_mgf_of_hasSubgaussianMGF (h_subG (i + 1)) lambda)

lemma maximal_bound_of_stronglyMeasurable (hX : forall i, StronglyMeasurable (X i))
    (h_indep : iIndepFun X P)
    (h_subG : forall i, HasSubgaussianMGF (X i) (sigma ^ 2) P)
    {n : Nat} (hn : 0 < n) {epsilon lambda : Real} (hlambda : 0 < lambda) :
    P.real {omega | exists t, 0 < t ∧ t <= n ∧
      epsilon <= ∑ s ∈ Finset.range t, X s omega} <=
      exp ((n : Real) * (sigma : Real) ^ 2 * lambda ^ 2 / 2 - lambda * epsilon) := by
  let F := Filtration.natural X hX
  let M : Nat -> Omega -> Real := fun i omega =>
    exp (lambda * (∑ s ∈ Finset.range (i + 1), X s omega))
  have hn_range : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.2 hn⟩
  let crossing : Set Omega := {omega | exists t, 0 < t ∧ t <= n ∧
    epsilon <= ∑ s ∈ Finset.range t, X s omega}
  let maximal : Set Omega := {omega |
    exp (lambda * epsilon) <=
      (Finset.range n).sup' hn_range (fun i => M i omega)}
  have hsub : Submartingale M F P := by
    exact exp_partial_sum_submartingale hX h_indep h_subG lambda
  have hnonneg : 0 <= M := fun i omega => exp_nonneg _
  have hn_pred : (n - 1) + 1 = n := by omega
  have hsets : crossing = maximal := by
    ext omega
    simp only [crossing, maximal, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, ht0, htn, hsum⟩
      have hit : t - 1 < n := by omega
      apply (Finset.le_sup'_iff hn_range).2
      refine ⟨t - 1, Finset.mem_range.2 hit, ?_⟩
      have ht_pred : (t - 1) + 1 = t := by omega
      simp only [M, ht_pred]
      exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum hlambda.le)
    · intro hmax
      obtain ⟨i, hi, hcross⟩ := (Finset.le_sup'_iff hn_range).1 hmax
      refine ⟨i + 1, Nat.zero_lt_succ i, Nat.succ_le_iff.2 (Finset.mem_range.1 hi), ?_⟩
      simp only [M] at hcross
      exact le_of_mul_le_mul_left (exp_le_exp.mp hcross) hlambda
  let a : NNReal := ⟨exp (lambda * epsilon), exp_nonneg _⟩
  have ha : (a : Real) = exp (lambda * epsilon) := rfl
  have hdoob_raw := maximal_ineq hsub hnonneg (ε := a) (n - 1)
  have hdoob : (a : ENNReal) * P maximal <=
      ENNReal.ofReal (∫ omega in maximal, M (n - 1) omega ∂P) := by
    simp only [ha, hn_pred] at hdoob_raw
    exact hdoob_raw
  have hdoob_real := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdoob
  have hset_nonneg : 0 <= ∫ omega in maximal, M (n - 1) omega ∂P := by
    exact integral_nonneg (fun _ => exp_nonneg _)
  have hdoob_real' : exp (lambda * epsilon) * P.real maximal <=
      ∫ omega in maximal, M (n - 1) omega ∂P := by
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ha, measureReal_def,
      ENNReal.toReal_ofReal hset_nonneg] using hdoob_real
  have hM_end_int : Integrable (M (n - 1)) P := hsub.integrable (n - 1)
  have hset_le_full : (∫ omega in maximal, M (n - 1) omega ∂P) <=
      ∫ omega, M (n - 1) omega ∂P :=
    setIntegral_le_integral hM_end_int (ae_of_all _ fun _ => exp_nonneg _)
  have hfull_eq : (∫ omega, M (n - 1) omega ∂P) =
      mgf (fun omega => ∑ s ∈ Finset.range n, X s omega) P lambda := by
    simp only [M, mgf, hn_pred]
  have hmgf : mgf (fun omega => ∑ s ∈ Finset.range n, X s omega) P lambda <=
      exp ((n : Real) * (sigma : Real) ^ 2 * lambda ^ 2 / 2) := by
    have h := (terminal_sum_subgaussian h_indep h_subG n).mgf_le lambda
    simpa [Finset.sum_const, NNReal.coe_pow] using h
  have hmul : exp (lambda * epsilon) * P.real crossing <=
      exp ((n : Real) * (sigma : Real) ^ 2 * lambda ^ 2 / 2) := by
    rw [hsets]
    exact hdoob_real'.trans (hset_le_full.trans (hfull_eq.trans_le hmgf))
  have hdiv : P.real crossing <=
      exp ((n : Real) * (sigma : Real) ^ 2 * lambda ^ 2 / 2) /
        exp (lambda * epsilon) := (le_div_iff₀ (exp_pos (lambda * epsilon))).2 (by
    simpa only [mul_comm] using hmul)
  simpa only [← exp_sub] using hdiv

lemma optimized_maximal_bound_of_stronglyMeasurable
    (hX : forall i, StronglyMeasurable (X i))
    (h_indep : iIndepFun X P)
    (h_subG : forall i, HasSubgaussianMGF (X i) (sigma ^ 2) P)
    (hsigma : 0 < sigma) {n : Nat} (hn : 0 < n) {epsilon : Real} (hepsilon : 0 < epsilon) :
    P.real {omega | exists t, 0 < t ∧ t <= n ∧
      epsilon <= ∑ s ∈ Finset.range t, X s omega} <=
      exp (-epsilon ^ 2 / (2 * n * (sigma : Real) ^ 2)) := by
  let lambda : Real := epsilon / ((n : Real) * (sigma : Real) ^ 2)
  have hlambda : 0 < lambda := by
    dsimp only [lambda]
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hsigmaR : (0 : Real) < (sigma : Real) := by exact_mod_cast hsigma
    positivity
  have h := maximal_bound_of_stronglyMeasurable hX h_indep h_subG hn
    (epsilon := epsilon) (lambda := lambda) hlambda
  rw [optimized_exponent hn hsigma hepsilon] at h
  exact h

lemma optimized_maximal_bound
    (h_indep : iIndepFun X P)
    (h_subG : forall i, HasSubgaussianMGF (X i) (sigma ^ 2) P)
    (hsigma : 0 < sigma) {n : Nat} (hn : 0 < n) {epsilon : Real} (hepsilon : 0 < epsilon) :
    P.real {omega | exists t, 0 < t ∧ t <= n ∧
      epsilon <= ∑ s ∈ Finset.range t, X s omega} <=
      exp (-epsilon ^ 2 / (2 * n * (sigma : Real) ^ 2)) := by
  let Y : Nat -> Omega -> Real :=
    fun i => (h_subG i).aestronglyMeasurable.mk (X i)
  have hXY : forall i, X i =ᵐ[P] Y i := fun i => (h_subG i).aestronglyMeasurable.ae_eq_mk
  have hY_meas : forall i, StronglyMeasurable (Y i) :=
    fun i => (h_subG i).aestronglyMeasurable.stronglyMeasurable_mk
  have hY_indep : iIndepFun Y P := h_indep.congr hXY
  have hY_subG : forall i, HasSubgaussianMGF (Y i) (sigma ^ 2) P :=
    fun i => (h_subG i).congr (hXY i)
  have hY_bound := optimized_maximal_bound_of_stronglyMeasurable
    hY_meas hY_indep hY_subG hsigma hn hepsilon
  have hevents :
      {omega | exists t, 0 < t ∧ t <= n ∧
        epsilon <= ∑ s ∈ Finset.range t, X s omega} =ᵐ[P]
      {omega | exists t, 0 < t ∧ t <= n ∧
        epsilon <= ∑ s ∈ Finset.range t, Y s omega} := by
    filter_upwards [ae_all_iff.2 hXY] with omega homega
    apply propext
    constructor
    · rintro ⟨t, ht0, htn, hsum⟩
      refine ⟨t, ht0, htn, ?_⟩
      calc
        epsilon <= ∑ s ∈ Finset.range t, X s omega := hsum
        _ = ∑ s ∈ Finset.range t, Y s omega := by
          apply Finset.sum_congr rfl
          intro s hs
          exact homega s
    · rintro ⟨t, ht0, htn, hsum⟩
      refine ⟨t, ht0, htn, ?_⟩
      calc
        epsilon <= ∑ s ∈ Finset.range t, Y s omega := hsum
        _ = ∑ s ∈ Finset.range t, X s omega := by
          apply Finset.sum_congr rfl
          intro s hs
          exact (homega s).symm
  rw [measureReal_congr hevents]
  exact hY_bound

  
  

end MaximalSubgaussianDirectScratch

theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {σ : ℝ≥0} (hσ : 0 < σ)
    (h_indep : iIndepFun X P)
    (h_subG : ∀ i, HasSubgaussianMGF (X i) (σ ^ 2) P)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ∃ t, 0 < t ∧ t ≤ n ∧ ε ≤ ∑ s ∈ Finset.range t, X s ω} ≤
      exp (-ε ^ 2 / (2 * n * (σ : ℝ) ^ 2)) := by
  exact MaximalSubgaussianDirectScratch.optimized_maximal_bound
    h_indep h_subG hσ hn hε
