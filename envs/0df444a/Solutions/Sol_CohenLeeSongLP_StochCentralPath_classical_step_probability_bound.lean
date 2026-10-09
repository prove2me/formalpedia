-- Prove2me | solution 1 for CohenLeeSongLP.StochCentralPath.classical_step_probability_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T09:57:19.051656+00:00
-- url     : https://prove2.me/submissions/b1dcc513-1ec2-4ea0-b057-9f5c08cee3f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_Main
import Theorems.Thm_CohenLeeSongLP_StochCentralPath_potential_expected_decrease
import Theorems.Thm_CohenLeeSongLP_StochCentralPath_success_probability

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder

namespace CohenLeeSongLP.StochCentralPath.L414

/-! Reduction of Lemma 4.14 to Lemma 4.13 (`potential_expected_decrease`) and
Claim 4.7 (`success_probability`). -/

lemma one_lt_log {n : ℕ} (hn : 10 ≤ n) : 1 < Real.log n := by
  have h10 : (10:ℝ) ≤ n := by exact_mod_cast hn
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log n := Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

lemma eps_pos {n : ℕ} (hn : 10 ≤ n) : 0 < eps n := by
  have := one_lt_log hn; unfold eps; positivity

lemma eps_le {n : ℕ} (hn : 10 ≤ n) : eps n ≤ 1 / 40000 := by
  have := one_lt_log hn; unfold eps
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith

lemma lam_pos {n : ℕ} (hn : 10 ≤ n) : 0 < lam n := by
  have := one_lt_log hn; unfold lam; positivity

lemma lam_mul_eps {n : ℕ} (hn : 10 ≤ n) : lam n * eps n = 1 / 1000 := by
  have := one_lt_log hn
  have hl : Real.log n ≠ 0 := by linarith
  unfold lam eps; field_simp; ring

lemma sqrt_n_ge_one {n : ℕ} (hn : 10 ≤ n) : 1 ≤ Real.sqrt n := by
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ n by omega))

lemma q_bounds {n : ℕ} (hn : 10 ≤ n) :
    0 < 1 - eps n / (3 * Real.sqrt n) ∧ 1 - eps n / (3 * Real.sqrt n) ≤ 1 := by
  have he := eps_pos hn; have he2 := eps_le hn
  have hs := sqrt_n_ge_one hn
  constructor
  · have : eps n / (3 * Real.sqrt n) ≤ eps n / 3 :=
      div_le_div_of_nonneg_left he.le (by norm_num) (by linarith)
    linarith
  · have : 0 ≤ eps n / (3 * Real.sqrt n) := by positivity
    linarith

lemma tSeq_succ' (n j : ℕ) : tSeq n (j + 1) = (1 - eps n / (3 * Real.sqrt n)) * tSeq n j := by
  unfold tSeq; rw [pow_succ, mul_comm]

lemma tSeq_pos' {n : ℕ} (hn : 10 ≤ n) (j : ℕ) : 0 < tSeq n j :=
  pow_pos (q_bounds hn).1 j

lemma potential_nonneg' {n : ℕ} (L : ℝ) (r : Fin n → ℝ) : 0 ≤ potential L r :=
  Finset.sum_nonneg (fun i _ => (Real.cosh_pos _).le)

/-- The potential of a state at path parameter `T`. -/
noncomputable def PhiT (n : ℕ) (T : ℝ) (y : State n) : ℝ :=
  potential (lam n) (fun i => y.1 i * y.2.1 i / T - 1)

/-- The invariant of Main: positive iterates and potential at most `n³`. -/
def InvT (n : ℕ) (T : ℝ) (y : State n) : Prop :=
  (∀ i, 0 < y.1 i) ∧ (∀ i, 0 < y.2.1 i) ∧ PhiT n T y ≤ (n : ℝ) ^ 3

lemma measurable_PhiT (n : ℕ) (T : ℝ) : Measurable (PhiT n T) := by
  unfold PhiT potential; fun_prop

lemma measurableSet_InvT (n : ℕ) (T : ℝ) : MeasurableSet {y : State n | InvT n T y} := by
  have h1 : MeasurableSet {y : State n | ∀ i, 0 < y.1 i} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (by fun_prop)
  have h2 : MeasurableSet {y : State n | ∀ i, 0 < y.2.1 i} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (by fun_prop)
  have h3 : MeasurableSet {y : State n | PhiT n T y ≤ (n : ℝ) ^ 3} :=
    measurableSet_le (measurable_PhiT n T) measurable_const
  have e : {y : State n | InvT n T y} =
      {y : State n | ∀ i, 0 < y.1 i} ∩ ({y : State n | ∀ i, 0 < y.2.1 i} ∩
        {y : State n | PhiT n T y ≤ (n : ℝ) ^ 3}) := by
    ext y; exact Iff.rfl
  rw [e]; exact h1.inter (h2.inter h3)

lemma exp_abs_le_two_cosh (y : ℝ) : Real.exp |y| ≤ 2 * Real.cosh y := by
  rw [← Real.cosh_abs, Real.cosh_eq]; have := Real.exp_pos (-|y|); linarith

/-- `Φ ≤ n³` forces `xs ≈_{0.1} t`. -/
lemma approx_of_phi {n : ℕ} (hn : 10 ≤ n) {T : ℝ} (hT : 0 < T) (x s : Fin n → ℝ)
    (hΦ : potential (lam n) (fun i => x i * s i / T - 1) ≤ (n : ℝ) ^ 3) :
    ApproxScalar 0.1 (fun i => x i * s i) T := by
  intro i
  have hl := one_lt_log hn
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hi : Real.cosh (lam n * (x i * s i / T - 1)) ≤ (n : ℝ) ^ 3 :=
    le_trans (Finset.single_le_sum (f := fun i => Real.cosh (lam n * (x i * s i / T - 1)))
      (fun j _ => (Real.cosh_pos _).le) (Finset.mem_univ i)) hΦ
  have hr : |x i * s i / T - 1| ≤ 0.1 := by
    by_contra hcon
    push Not at hcon
    have h4 : 4 * Real.log n < |lam n * (x i * s i / T - 1)| := by
      rw [abs_mul, abs_of_pos (lam_pos hn)]; unfold lam; nlinarith
    have h5 : Real.exp (4 * Real.log n) = (n : ℝ) ^ 4 := by
      rw [show (4:ℝ) * Real.log n = ((4:ℕ):ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
        Real.exp_log (by linarith)]
    have h6 := Real.exp_lt_exp.2 h4
    have h7 := exp_abs_le_two_cosh (lam n * (x i * s i / T - 1))
    rw [h5] at h6
    have h8 : (n : ℝ) ^ 4 = n * n ^ 3 := by ring
    have h9 : (0:ℝ) < (n : ℝ) ^ 3 := by positivity
    nlinarith
  rw [abs_le] at hr
  obtain ⟨h1, h2⟩ := hr
  constructor
  · have : 0.9 ≤ x i * s i / T := by linarith
    rw [le_div_iff₀ hT] at this; linarith
  · have : x i * s i / T ≤ 1.1 := by linarith
    rw [div_le_iff₀ hT] at this; linarith

/-- `‖δ_μ‖₂ ≤ ε t` for Main's direction. -/
lemma direction_norm {n : ℕ} (hn : 10 ≤ n) {T : ℝ} (hT : 0 < T) (x s : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i)
    (hap : ApproxScalar 0.1 (fun i => x i * s i) T) :
    norm2 (direction (lam n) (eps n) T ((1 - eps n / (3 * Real.sqrt n)) * T) x s) ≤ eps n * T := by
  have he := eps_pos hn
  have hq := q_bounds hn
  have hn0 : (0:ℝ) < n := by have : (10:ℝ) ≤ n := by exact_mod_cast hn
                             linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hsq2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  set G := potentialGrad (lam n) (fun l => x l * s l / T - 1) with hG
  set q := 1 - eps n / (3 * Real.sqrt n) with hqdef
  have hqT : q * T / T - 1 = -(eps n / (3 * Real.sqrt n)) := by
    rw [mul_div_assoc, div_self hT.ne', mul_one, hqdef]; ring
  have hgs : ∑ i, (G i / norm2 G) ^ 2 ≤ 1 := by
    by_cases h0 : ∑ i, G i ^ 2 = 0
    · have : norm2 G = 0 := by unfold norm2; rw [h0, Real.sqrt_zero]
      simp [this]
    · have hpos : 0 < ∑ i, G i ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm h0)
      have h2 : norm2 G ^ 2 = ∑ i, G i ^ 2 := by unfold norm2; exact Real.sq_sqrt hpos.le
      simp_rw [div_pow]; rw [← Finset.sum_div, h2, div_self h0]
  have hmu : ∑ i, (x i * s i) ^ 2 ≤ n * (1.1 * T) ^ 2 := by
    have hb : ∀ i ∈ Finset.univ, (x i * s i) ^ 2 ≤ (1.1 * T) ^ 2 := by
      intro i _
      have h := hap i
      dsimp only at h
      have := mul_pos (hx i) (hs i)
      nlinarith [h.2]
    calc ∑ i, (x i * s i) ^ 2 ≤ ∑ _i : Fin n, (1.1 * T) ^ 2 := Finset.sum_le_sum hb
      _ = n * (1.1 * T) ^ 2 := by simp
  have hd : ∀ i, direction (lam n) (eps n) T (q * T) x s i =
      (-(eps n / (3 * Real.sqrt n))) * (x i * s i) - eps n / 2 * (q * T) * (G i / norm2 G) := by
    intro i; simp only [direction, hqT]; rfl
  have hc : (eps n / (3 * Real.sqrt n)) ^ 2 * n = eps n ^ 2 / 9 := by
    rw [div_pow, mul_pow, hsq2]; field_simp; ring
  unfold norm2
  rw [show eps n * T = Real.sqrt ((eps n * T) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  calc ∑ i, direction (lam n) (eps n) T (q * T) x s i ^ 2
      = ∑ i, ((-(eps n / (3 * Real.sqrt n))) * (x i * s i)
          - eps n / 2 * (q * T) * (G i / norm2 G)) ^ 2 := by simp only [hd]
    _ ≤ ∑ i, (2 * ((eps n / (3 * Real.sqrt n)) ^ 2 * (x i * s i) ^ 2)
          + 2 * ((eps n / 2 * (q * T)) ^ 2 * (G i / norm2 G) ^ 2)) := by
        apply Finset.sum_le_sum; intro i _
        nlinarith [sq_nonneg ((-(eps n / (3 * Real.sqrt n))) * (x i * s i)
          + eps n / 2 * (q * T) * (G i / norm2 G))]
    _ = 2 * (eps n / (3 * Real.sqrt n)) ^ 2 * ∑ i, (x i * s i) ^ 2
          + 2 * (eps n / 2 * (q * T)) ^ 2 * ∑ i, (G i / norm2 G) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
    _ ≤ 2 * (eps n / (3 * Real.sqrt n)) ^ 2 * (n * (1.1 * T) ^ 2)
          + 2 * (eps n / 2 * (q * T)) ^ 2 * 1 := by
        gcongr
    _ = (2.42 / 9) * (eps n * T) ^ 2 + (q ^ 2 / 2) * (eps n * T) ^ 2 := by
        rw [show 2 * (eps n / (3 * Real.sqrt n)) ^ 2 * (n * (1.1 * T) ^ 2)
          = 2 * ((eps n / (3 * Real.sqrt n)) ^ 2 * n) * (1.1 * T) ^ 2 by ring, hc]
        ring
    _ ≤ (eps n * T) ^ 2 := by
        have hX : 0 ≤ (eps n * T) ^ 2 := sq_nonneg _
        have hq2 : q ^ 2 ≤ 1 := by nlinarith [hq.1, hq.2]
        nlinarith

/-- Child-free step (i)–(ii): the invariant gives Assumption 4.1. -/
lemma asm41 {n : ℕ} (hn : 10 ≤ n) {T : ℝ} (hT : 0 < T) (x s v : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i)
    (hΦ : potential (lam n) (fun i => x i * s i / T - 1) ≤ (n : ℝ) ^ 3)
    (hv : ApproxVec epsMp (fun i => x i / s i) v) :
    Assumption41 x s T v (direction (lam n) (eps n) T ((1 - eps n / (3 * Real.sqrt n)) * T) x s)
      (kSampMain n) (eps n) epsMp := by
  have hap := approx_of_phi hn hT x s hΦ
  have hl := one_lt_log hn
  have hn0 : (0:ℝ) < n := by have : (10:ℝ) ≤ n := by exact_mod_cast hn
                             linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have he := eps_pos hn
  exact {
    x_pos := hx
    s_pos := hs
    t_pos := hT
    xs_approx := hap
    εmp_pos := by unfold epsMp; norm_num
    εmp_le := le_rfl
    w_approx := hv
    ε_pos := he
    ε_le := le_rfl
    δμ_norm := direction_norm hn hT x s hx hs hap
    kSamp_pos := by unfold kSampMain epsMp; positivity
    kSamp_ge := le_rfl }

/-- (iv) from Claim 4.7: the success event has positive probability. -/
lemma success_pos_of {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (x s v δμ : Fin n → ℝ)
    (h : ENNReal.ofReal (1 - 2 * n * Real.exp (-(0.003 * kSampMain n /
        (eps n * Real.sqrt n * Real.log n))))
      ≤ sampleLaw (kSampMain n) δμ {δ | ∀ i,
          |stepS A x s v δ i / sbar x s v i| ≤ 0.01 / Real.log n ∧
          |stepS A x s v δ i / s i| ≤ 0.02 / Real.log n ∧
          |stepX A x s v δ i / xbar x s v i| ≤ 0.01 / Real.log n ∧
          |stepX A x s v δ i / x i| ≤ 0.02 / Real.log n ∧
          |δ i / (x i * s i)| ≤ 0.02 / Real.log n}) :
    0 < sampleLaw (kSampMain n) δμ (successEvent A x s v) := by
  have hl := one_lt_log hn
  have he := eps_pos hn
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hX : 0.003 * kSampMain n / (eps n * Real.sqrt n * Real.log n) = 120000 * Real.log n := by
    unfold kSampMain epsMp
    rw [show (0.003:ℝ) = 3 / 1000 by norm_num]
    field_simp; ring
  rw [hX] at h
  have hexp : Real.exp (-(120000 * Real.log n)) ≤ ((n:ℝ) * n)⁻¹ := by
    rw [Real.exp_neg]
    apply inv_anti₀ (by positivity)
    have e2 : Real.exp (2 * Real.log n) = n * n := by
      rw [two_mul, Real.exp_add, Real.exp_log (by linarith)]
    rw [← e2]; exact Real.exp_le_exp.2 (by nlinarith)
  have hpos : 0 < 1 - 2 * n * Real.exp (-(120000 * Real.log n)) := by
    have h1 : 2 * (n:ℝ) * Real.exp (-(120000 * Real.log n)) ≤ 2 * n * ((n:ℝ) * n)⁻¹ :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have h2 : 2 * (n:ℝ) * ((n:ℝ) * n)⁻¹ = 2 / n := by field_simp
    rw [h2] at h1
    have h3 : (2:ℝ) / n ≤ 1 / 5 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have e : (0.01:ℝ) / Real.log n = 1 / (100 * Real.log n) := by
    rw [show (0.01:ℝ) = 1 / 100 by norm_num, div_div]
  calc (0:ENNReal) < ENNReal.ofReal (1 - 2 * n * Real.exp (-(120000 * Real.log n))) :=
        ENNReal.ofReal_pos.2 hpos
    _ ≤ _ := h
    _ ≤ _ := measure_mono (show _ ⊆ successEvent A x s v from fun δ hδ i => by
        obtain ⟨h1, -, h3, -, -⟩ := hδ i
        rw [e] at h1 h3
        exact ⟨h1, h3⟩)

lemma sqrt_le_two' {a : ℝ} (h : a ≤ 2) : Real.sqrt a ≤ 2 := by
  have h0 := Real.sqrt_nonneg a
  by_cases ha : 0 ≤ a
  · have := Real.sq_sqrt ha; nlinarith
  · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]; norm_num

lemma step_bound {a b c L : ℝ} (hb : 0 < b) (hbc : b ≤ 2 * c) (hL : 1 < L)
    (h : |a / b| ≤ 1 / (100 * L)) : |a| ≤ c / 50 := by
  have e : |a| = |a / b| * b := by rw [abs_div, abs_of_pos hb, div_mul_cancel₀ _ hb.ne']
  rw [e]
  have h1 : 1 / (100 * L) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  calc |a / b| * b ≤ (1 / 100) * (2 * c) := mul_le_mul (h.trans h1) hbc hb.le (by norm_num)
    _ = c / 50 := by ring

lemma cont_stepX {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n) :
    Continuous (fun δ => stepX A x s v δ i) := by
  unfold stepX pMu; fun_prop

lemma cont_stepS {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n) :
    Continuous (fun δ => stepS A x s v δ i) := by
  unfold stepS pMu; fun_prop

lemma cont_phiRaw {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (T' : ℝ) :
    Continuous (fun δ => potential (lam n) (fun i => muNew A x s v δ i / T' - 1)) := by
  unfold potential muNew stepX stepS pMu; fun_prop

lemma measurableSet_successEvent {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) :
    MeasurableSet (successEvent A x s v) := by
  have e : successEvent A x s v = ⋂ i, ({δ | |stepS A x s v δ i / sbar x s v i| ≤
      1 / (100 * Real.log n)} ∩ {δ | |stepX A x s v δ i / xbar x s v i| ≤ 1 / (100 * Real.log n)}) := by
    ext δ; simp only [successEvent, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  refine MeasurableSet.iInter fun i => (measurableSet_le ?_ measurable_const).inter
    (measurableSet_le ?_ measurable_const)
  · exact ((cont_stepS A x s v i).div_const _).abs.measurable
  · exact ((cont_stepX A x s v i).div_const _).abs.measurable

/-- One step of Main from a state satisfying the invariant (paper p. 3:20). -/
lemma step_core {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ) {T' : ℝ} (hT' : 0 < T')
    (x s v δμ : Fin n → ℝ) (k B0 : ℝ)
    (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i)
    (hv : ApproxVec epsMp (fun i => x i / s i) v)
    (Cx Cs : Fin n → ℝ) (hC : InvT n T' (Cx, Cs, true))
    (hprob : IsProbabilityMeasure (stepLaw A x s v k δμ))
    (hdec : ∫ δ, potential (lam n) (fun i => muNew A x s v δ i / T' - 1)
      ∂(stepLaw A x s v k δμ) ≤ B0)
    (F : (Fin n → ℝ) → State n) (hFm : Measurable F)
    (hF1 : ∀ δ, (n : ℝ) ^ 3 < potential (lam n) (fun i => muNew A x s v δ i / T' - 1) →
      F δ = (Cx, Cs, true))
    (hF2 : ∀ δ, ¬ (n : ℝ) ^ 3 < potential (lam n) (fun i => muNew A x s v δ i / T' - 1) →
      F δ = ((fun i => x i + stepX A x s v δ i), (fun i => s i + stepS A x s v δ i), false)) :
    ((stepLaw A x s v k δμ).map F) {y | ¬ InvT n T' y} = 0 ∧
    ∫⁻ y, ENNReal.ofReal (PhiT n T' y) ∂((stepLaw A x s v k δμ).map F) ≤ ENNReal.ofReal B0 ∧
    ((stepLaw A x s v k δμ).map F) {y | y.2.2 = true} ≤
      ENNReal.ofReal B0 / ENNReal.ofReal ((n : ℝ) ^ 3) := by
  have hl := one_lt_log hn
  have hn0 : (0:ℝ) < n := by have : (10:ℝ) ≤ n := by exact_mod_cast hn
                             linarith
  have hSm := measurableSet_successEvent A x s v
  have hSc : stepLaw A x s v k δμ (successEvent A x s v)ᶜ = 0 := by
    rw [stepLaw, cond_apply hSm, Set.inter_compl_self, measure_empty, mul_zero]
  have hΦrm : Measurable (fun δ => potential (lam n) (fun i => muNew A x s v δ i / T' - 1)) :=
    (cont_phiRaw A x s v T').measurable
  have hbar : ∀ i, 0 < xbar x s v i ∧ xbar x s v i ≤ 2 * x i ∧
      0 < sbar x s v i ∧ sbar x s v i ≤ 2 * s i := by
    intro i
    have hw : 0 < x i / s i := div_pos (hx i) (hs i)
    obtain ⟨h1, h2⟩ := hv i
    dsimp only at h1 h2
    unfold epsMp at h1 h2
    have hvp : 0 < v i := by nlinarith
    have hr1 : v i / (x i / s i) ≤ 2 := by rw [div_le_iff₀ hw]; nlinarith
    have hr2 : (x i / s i) / v i ≤ 2 := by rw [div_le_iff₀ hvp]; nlinarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold xbar; exact mul_pos (hx i) (Real.sqrt_pos.2 (div_pos hvp hw))
    · unfold xbar; have := sqrt_le_two' hr1; have := hx i; nlinarith
    · unfold sbar; exact mul_pos (hs i) (Real.sqrt_pos.2 (div_pos hw hvp))
    · unfold sbar; have := sqrt_le_two' hr2; have := hs i; nlinarith
  have hgood : ∀ δ ∈ successEvent A x s v, ∀ i,
      (0 < x i + stepX A x s v δ i ∧ x i + stepX A x s v δ i ≤ 2 * x i) ∧
      (0 < s i + stepS A x s v δ i ∧ s i + stepS A x s v δ i ≤ 2 * s i) := by
    intro δ hδ i
    obtain ⟨hS, hX⟩ := hδ i
    obtain ⟨b1, b2, b3, b4⟩ := hbar i
    have e1 := step_bound b1 b2 hl hX
    have e2 := step_bound b3 b4 hl hS
    have := hx i; have := hs i
    rw [abs_le] at e1 e2
    exact ⟨⟨by linarith [e1.1], by linarith [e1.2]⟩, ⟨by linarith [e2.1], by linarith [e2.2]⟩⟩
  have hInvF : ∀ δ ∈ successEvent A x s v, InvT n T' (F δ) := by
    intro δ hδ
    by_cases hc : (n : ℝ) ^ 3 < potential (lam n) (fun i => muNew A x s v δ i / T' - 1)
    · rw [hF1 δ hc]; exact hC
    · rw [hF2 δ hc]
      exact ⟨fun i => (hgood δ hδ i).1.1, fun i => (hgood δ hδ i).2.1, not_lt.1 hc⟩
  have hle : ∀ δ, PhiT n T' (F δ) ≤
      potential (lam n) (fun i => muNew A x s v δ i / T' - 1) := by
    intro δ
    by_cases hc : (n : ℝ) ^ 3 < potential (lam n) (fun i => muNew A x s v δ i / T' - 1)
    · rw [hF1 δ hc]; exact hC.2.2.trans hc.le
    · rw [hF2 δ hc]; exact le_rfl
  have hbound : ∀ δ ∈ successEvent A x s v,
      potential (lam n) (fun i => muNew A x s v δ i / T' - 1) ≤
        ∑ i, Real.cosh (lam n * (4 * (x i * s i) / T' + 1)) := by
    intro δ hδ
    unfold potential
    apply Finset.sum_le_sum; intro i _
    rw [Real.cosh_le_cosh]
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hgood δ hδ i
    have hxs := mul_pos (hx i) (hs i)
    have hm0 : 0 < muNew A x s v δ i := mul_pos a1 b1
    have hm1 : muNew A x s v δ i ≤ 4 * (x i * s i) := by unfold muNew; nlinarith
    have hL := lam_pos hn
    have h3 : 0 ≤ 4 * (x i * s i) / T' := div_nonneg (by linarith) hT'.le
    have hB : 0 < 4 * (x i * s i) / T' + 1 := by linarith
    rw [abs_mul, abs_mul, abs_of_pos hL, abs_of_pos hB]
    apply mul_le_mul_of_nonneg_left _ hL.le
    rw [abs_le]
    have h1 : muNew A x s v δ i / T' ≤ 4 * (x i * s i) / T' :=
      div_le_div_of_nonneg_right hm1 hT'.le
    have h2 : 0 ≤ muNew A x s v δ i / T' := div_nonneg hm0.le hT'.le
    constructor <;> linarith
  have hint : Integrable (fun δ => potential (lam n) (fun i => muNew A x s v δ i / T' - 1))
      (stepLaw A x s v k δμ) := by
    refine Integrable.of_bound hΦrm.aestronglyMeasurable
      (∑ i, Real.cosh (lam n * (4 * (x i * s i) / T' + 1))) ?_
    have hae : ∀ᵐ δ ∂(stepLaw A x s v k δμ), δ ∈ successEvent A x s v := ae_cond_mem hSm
    filter_upwards [hae] with δ hδ
    rw [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg' _ _)]
    exact hbound δ hδ
  have hE : ∫⁻ δ, ENNReal.ofReal (potential (lam n) (fun i => muNew A x s v δ i / T' - 1))
      ∂(stepLaw A x s v k δμ) ≤ ENNReal.ofReal B0 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun δ => potential_nonneg' _ _)]
    exact ENNReal.ofReal_le_ofReal hdec
  refine ⟨?_, ?_, ?_⟩
  · have hbad : MeasurableSet {y : State n | ¬ InvT n T' y} := (measurableSet_InvT n T').compl
    rw [Measure.map_apply hFm hbad]
    apply measure_mono_null _ hSc
    intro δ hδ hS
    exact hδ (hInvF δ hS)
  · rw [lintegral_map (measurable_PhiT n T').ennreal_ofReal hFm]
    exact (lintegral_mono fun δ => ENNReal.ofReal_le_ofReal (hle δ)).trans hE
  · have hflag : MeasurableSet {y : State n | y.2.2 = true} :=
      measurable_snd.snd (measurableSet_singleton true)
    rw [Measure.map_apply hFm hflag]
    have hsub : F ⁻¹' {y : State n | y.2.2 = true} ⊆
        {δ | ENNReal.ofReal ((n : ℝ) ^ 3) ≤
          ENNReal.ofReal (potential (lam n) (fun i => muNew A x s v δ i / T' - 1))} := by
      intro δ hδ
      by_cases hc : (n : ℝ) ^ 3 < potential (lam n) (fun i => muNew A x s v δ i / T' - 1)
      · exact ENNReal.ofReal_le_ofReal hc.le
      · exfalso
        have := hF2 δ hc
        simp [this] at hδ
    refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
      (ENNReal.measurable_ofReal.comp hΦrm).aemeasurable ?_ ENNReal.ofReal_ne_top).trans ?_)
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    · exact ENNReal.div_le_div_right hE _

/-- One step of Main as a kernel, from a history whose last state satisfies the invariant. -/
lemma kstep {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (U : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ))
    (hU : ∀ j (h : (i : Finset.Iic j) → State n),
      (∀ i, 0 < (current h).1 i) → (∀ i, 0 < (current h).2.1 i) →
      ApproxVec epsMp (fun i => (current h).1 i / (current h).2.1 i) (U j h))
    (C : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ) × (Fin n → ℝ))
    (hC : ∀ j (h : (i : Finset.Iic j) → State n),
      (∀ i, 0 < (current h).1 i) → (∀ i, 0 < (current h).2.1 i) →
      ApproxScalar 0.1 (fun i => (current h).1 i * (current h).2.1 i) (tSeq n j) →
      (∀ i, 0 < (C j h).1 i) ∧ (∀ i, 0 < (C j h).2 i) ∧
      potential (lam n) (fun i => (C j h).1 i * (C j h).2 i / tSeq n (j + 1) - 1) ≤ (n : ℝ) ^ 3)
    (j : ℕ) (h : (i : Finset.Iic j) → State n) (hI : InvT n (tSeq n j) (current h)) :
    mainStepLaw A U C j h {y | ¬ InvT n (tSeq n (j + 1)) y} = 0 ∧
    ∫⁻ y, ENNReal.ofReal (PhiT n (tSeq n (j + 1)) y) ∂(mainStepLaw A U C j h) ≤
      ENNReal.ofReal (PhiT n (tSeq n j) (current h) - lam n * eps n / (15 * Real.sqrt n) *
        (PhiT n (tSeq n j) (current h) - 10 * n)) ∧
    mainStepLaw A U C j h {y | y.2.2 = true} ≤
      ENNReal.ofReal (PhiT n (tSeq n j) (current h) - lam n * eps n / (15 * Real.sqrt n) *
        (PhiT n (tSeq n j) (current h) - 10 * n)) / ENNReal.ofReal ((n : ℝ) ^ 3) := by
  obtain ⟨hx, hs, hΦ⟩ := hI
  have hT := tSeq_pos' hn j
  have hq := q_bounds hn
  have hT' : 0 < (1 - eps n / (3 * Real.sqrt n)) * tSeq n j := mul_pos hq.1 hT
  have hv := hU j h hx hs
  have hA41 := asm41 hn hT (current h).1 (current h).2.1 (U j h) hx hs hΦ hv
  have hsucc := success_pos_of hn A (current h).1 (current h).2.1 (U j h) _
    (success_probability hn A hA (current h).1 (current h).2.1 (U j h) _ (tSeq n j)
      (kSampMain n) (eps n) epsMp hA41).2
  obtain ⟨hprob, hdec⟩ := potential_expected_decrease hn A hA (current h).1 (current h).2.1
    (U j h) (tSeq n j) (kSampMain n) (eps n) epsMp hA41
  have hCj := hC j h hx hs (approx_of_phi hn hT _ _ hΦ)
  have hC' : InvT n ((1 - eps n / (3 * Real.sqrt n)) * tSeq n j) ((C j h).1, (C j h).2, true) := by
    refine ⟨hCj.1, hCj.2.1, ?_⟩
    rw [← tSeq_succ']; exact hCj.2.2
  unfold mainStepLaw
  dsimp only
  rw [tSeq_succ', if_neg hsucc.ne']
  refine step_core hn A hT' _ _ _ _ _ _ hx hs hv _ _ hC' hprob hdec _ ?_ ?_ ?_
  · refine Measurable.ite (measurableSet_lt measurable_const (cont_phiRaw A _ _ _ _).measurable)
      measurable_const ?_
    exact (measurable_pi_lambda _ fun i => measurable_const.add (cont_stepX A _ _ _ i).measurable).prodMk
      ((measurable_pi_lambda _ fun i =>
        measurable_const.add (cont_stepS A _ _ _ i).measurable).prodMk measurable_const)
  · intro δ hc; exact if_pos hc
  · intro δ hc; exact if_neg hc

lemma traj_succ_lint {n : ℕ}
    (κ : (j : ℕ) → Kernel ((i : Finset.Iic j) → State n) (State n)) [∀ j, IsMarkovKernel (κ j)]
    (μ0 : Measure (State n)) [IsProbabilityMeasure μ0] (j : ℕ)
    (f : State n → ENNReal) (hf : Measurable f) :
    ∫⁻ ω : (k : ℕ) → State n, f (ω (j + 1)) ∂(Kernel.trajMeasure (X := fun _ => State n) μ0 κ) =
      ∫⁻ ω : (k : ℕ) → State n, ∫⁻ y, f y ∂(κ j (frestrictLe j ω)) ∂(Kernel.trajMeasure (X := fun _ => State n) μ0 κ) := by
  have hm : Measurable (fun ω : (k : ℕ) → State n => (frestrictLe j ω, ω (j + 1))) :=
    (measurable_frestrictLe j).prodMk (measurable_pi_apply _)
  calc ∫⁻ ω : (k : ℕ) → State n, f (ω (j + 1)) ∂(Kernel.trajMeasure (X := fun _ => State n) μ0 κ)
      = ∫⁻ p, f p.2 ∂((Kernel.trajMeasure (X := fun _ => State n) μ0 κ).map
          (fun ω : (k : ℕ) → State n => (frestrictLe j ω, ω (j + 1)))) :=
        (lintegral_map (hf.comp measurable_snd) hm).symm
    _ = ∫⁻ p, f p.2 ∂(((Kernel.trajMeasure (X := fun _ => State n) μ0 κ).map (frestrictLe j)) ⊗ₘ κ j) := by
        rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]
    _ = ∫⁻ a, ∫⁻ y, f y ∂(κ j a) ∂((Kernel.trajMeasure (X := fun _ => State n) μ0 κ).map (frestrictLe j)) :=
        Measure.lintegral_compProd (hf.comp measurable_snd)
    _ = _ := lintegral_map (hf.lintegral_kernel) (measurable_frestrictLe j)

lemma traj_succ_set {n : ℕ}
    (κ : (j : ℕ) → Kernel ((i : Finset.Iic j) → State n) (State n)) [∀ j, IsMarkovKernel (κ j)]
    (μ0 : Measure (State n)) [IsProbabilityMeasure μ0] (j : ℕ)
    (B : Set (State n)) (hB : MeasurableSet B) :
    Kernel.trajMeasure (X := fun _ => State n) μ0 κ {ω : (k : ℕ) → State n | ω (j + 1) ∈ B} =
      ∫⁻ ω : (k : ℕ) → State n, κ j (frestrictLe j ω) B ∂(Kernel.trajMeasure (X := fun _ => State n) μ0 κ) := by
  have h1 := traj_succ_lint κ μ0 j (B.indicator 1) (measurable_one.indicator hB)
  simp only [lintegral_indicator_one hB] at h1
  rw [← h1, show {ω : (k : ℕ) → State n | ω (j + 1) ∈ B} = (fun f : (k : ℕ) → State n => f (j + 1)) ⁻¹' B
    from rfl, ← lintegral_indicator_one (measurable_pi_apply (j + 1) hB)]
  rfl

lemma traj_zero {n : ℕ}
    (κ : (j : ℕ) → Kernel ((i : Finset.Iic j) → State n) (State n)) [∀ j, IsMarkovKernel (κ j)]
    (p : State n) : ∀ᵐ ω : (k : ℕ) → State n ∂(Kernel.trajMeasure (X := fun _ => State n) (Measure.dirac p) κ), ω 0 = p := by
  have hmap : (Kernel.trajMeasure (X := fun _ => State n) (Measure.dirac p) κ).map (frestrictLe 0) =
      Measure.dirac ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => State n)).symm p) := by
    rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
      Measure.map_dirac' (MeasurableEquiv.measurable _)]
  have h : ∀ᵐ y ∂((Kernel.trajMeasure (X := fun _ => State n) (Measure.dirac p) κ).map (frestrictLe 0)),
      y ⟨0, by simp⟩ = p := by
    rw [hmap, ae_dirac_eq, Filter.eventually_pure]
    rfl
  exact ae_of_ae_map (measurable_frestrictLe 0).aemeasurable h

lemma lint_affine {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hfm : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : 0 ≤ M) (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal M) :
    ∫⁻ ω, ENNReal.ofReal (a * f ω + b) ∂P ≤ ENNReal.ofReal (a * M + b) := by
  have e : ∀ ω, ENNReal.ofReal (a * f ω + b) =
      ENNReal.ofReal a * ENNReal.ofReal (f ω) + ENNReal.ofReal b := by
    intro ω; rw [ENNReal.ofReal_add (mul_nonneg ha (hf0 ω)) hb, ENNReal.ofReal_mul ha]
  simp_rw [e]
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul _
    hfm.ennreal_ofReal, lintegral_const, measure_univ, mul_one,
    ENNReal.ofReal_add (mul_nonneg ha hM) hb, ENNReal.ofReal_mul ha]
  gcongr

lemma c_bounds {n : ℕ} (hn : 10 ≤ n) :
    0 ≤ lam n * eps n / (15 * Real.sqrt n) ∧ lam n * eps n / (15 * Real.sqrt n) ≤ 1 := by
  have hs := sqrt_n_ge_one hn
  rw [lam_mul_eps hn]
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith

lemma base_bound {n : ℕ} (hn : 10 ≤ n) (x0 s0 : Fin n → ℝ)
    (hinit : ApproxScalar (1 / lam n) (fun i => x0 i * s0 i) 1) :
    PhiT n (tSeq n 0) (x0, s0, false) ≤ 10 * n := by
  have hL := lam_pos hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  show ∑ i, Real.cosh (lam n * (x0 i * s0 i / tSeq n 0 - 1)) ≤ 10 * n
  rw [show tSeq n 0 = 1 from pow_zero _]
  simp only [div_one]
  have hc1 : Real.cosh 1 ≤ 2 := by
    rw [Real.cosh_eq]
    have := Real.exp_one_lt_d9
    have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    linarith
  calc ∑ i, Real.cosh (lam n * (x0 i * s0 i - 1)) ≤ ∑ _i : Fin n, (2:ℝ) := by
        apply Finset.sum_le_sum; intro i _
        have h := hinit i
        dsimp only at h
        obtain ⟨h1, h2⟩ := h
        have hu : lam n * (1 / lam n) = 1 := by field_simp
        have h3 : |lam n * (x0 i * s0 i - 1)| ≤ 1 := by
          rw [abs_le]
          constructor
          · nlinarith [mul_le_mul_of_nonneg_left h1 hL.le]
          · nlinarith [mul_le_mul_of_nonneg_left h2 hL.le]
        calc Real.cosh (lam n * (x0 i * s0 i - 1)) ≤ Real.cosh 1 :=
              Real.cosh_le_cosh.2 (by rwa [abs_one])
          _ ≤ 2 := hc1
    _ = 2 * n := by simp [mul_comm]
    _ ≤ 10 * n := by nlinarith

/-- The induction over iterations: the invariant holds a.s. and `E[Φ_j] ≤ 10 n`. -/
lemma induct {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (x0 s0 : Fin n → ℝ) (hx0 : ∀ i, 0 < x0 i) (hs0 : ∀ i, 0 < s0 i)
    (hinit : ApproxScalar (1 / lam n) (fun i => x0 i * s0 i) 1)
    (U : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ))
    (hU : ∀ j (h : (i : Finset.Iic j) → State n),
      (∀ i, 0 < (current h).1 i) → (∀ i, 0 < (current h).2.1 i) →
      ApproxVec epsMp (fun i => (current h).1 i / (current h).2.1 i) (U j h))
    (C : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ) × (Fin n → ℝ))
    (hC : ∀ j (h : (i : Finset.Iic j) → State n),
      (∀ i, 0 < (current h).1 i) → (∀ i, 0 < (current h).2.1 i) →
      ApproxScalar 0.1 (fun i => (current h).1 i * (current h).2.1 i) (tSeq n j) →
      (∀ i, 0 < (C j h).1 i) ∧ (∀ i, 0 < (C j h).2 i) ∧
      potential (lam n) (fun i => (C j h).1 i * (C j h).2 i / tSeq n (j + 1) - 1) ≤ (n : ℝ) ^ 3)
    (κ : (j : ℕ) → ProbabilityTheory.Kernel ((i : Finset.Iic j) → State n) (State n))
    [∀ j, IsMarkovKernel (κ j)]
    (hκ : ∀ j h, κ j h = mainStepLaw A U C j h) (j : ℕ) :
    (∀ᵐ ω : (k : ℕ) → State n ∂(Kernel.trajMeasure (X := fun _ => State n) (Measure.dirac (x0, s0, false)) κ),
      InvT n (tSeq n j) (ω j)) ∧
    ∫⁻ ω : (k : ℕ) → State n, ENNReal.ofReal (PhiT n (tSeq n j) (ω j))
      ∂(Kernel.trajMeasure (X := fun _ => State n) (Measure.dirac (x0, s0, false)) κ) ≤ ENNReal.ofReal (10 * n) := by
  set P := Kernel.trajMeasure (X := fun _ => State n) (Measure.dirac (x0, s0, false)) κ with hP
  have hn3 : (10:ℝ) * n ≤ (n:ℝ) ^ 3 := by
    have h10 : (10:ℝ) ≤ n := by exact_mod_cast hn
    have h2 : (10:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
    calc (10:ℝ) * n ≤ (n:ℝ) ^ 2 * n := mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = (n:ℝ) ^ 3 := by ring
  induction j with
  | zero =>
    have hb := base_bound hn x0 s0 hinit
    have h0 := traj_zero κ (x0, s0, false)
    refine ⟨?_, ?_⟩
    · filter_upwards [h0] with ω hω
      rw [hω]; exact ⟨hx0, hs0, hb.trans hn3⟩
    · rw [lintegral_congr_ae (h0.mono fun ω hω => by
          show ENNReal.ofReal (PhiT n (tSeq n 0) (ω 0)) = ENNReal.ofReal (PhiT n (tSeq n 0) (x0, s0, false))
          rw [hω]), lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_le_ofReal hb
  | succ j ih =>
    obtain ⟨hI, hE⟩ := ih
    have hc := c_bounds hn
    refine ⟨?_, ?_⟩
    · rw [ae_iff]
      have hbad : MeasurableSet {y : State n | ¬ InvT n (tSeq n (j + 1)) y} :=
        (measurableSet_InvT n _).compl
      have e := traj_succ_set κ (Measure.dirac (x0, s0, false)) j _ hbad
      refine le_antisymm ?_ (by simp)
      calc P {ω : (k : ℕ) → State n | ¬ InvT n (tSeq n (j + 1)) (ω (j + 1))}
          = ∫⁻ ω : (k : ℕ) → State n, κ j (frestrictLe j ω) {y | ¬ InvT n (tSeq n (j + 1)) y} ∂P := e
        _ ≤ ∫⁻ _ω, 0 ∂P := lintegral_mono_ae (hI.mono fun ω hω => by
            rw [hκ]; exact (kstep hn A hA U hU C hC j (frestrictLe j ω) hω).1.le)
        _ = 0 := lintegral_zero
    · calc ∫⁻ ω : (k : ℕ) → State n, ENNReal.ofReal (PhiT n (tSeq n (j + 1)) (ω (j + 1))) ∂P
          = ∫⁻ ω : (k : ℕ) → State n, ∫⁻ y, ENNReal.ofReal (PhiT n (tSeq n (j + 1)) y) ∂(κ j (frestrictLe j ω)) ∂P :=
            traj_succ_lint κ _ j _ (measurable_PhiT n _).ennreal_ofReal
        _ ≤ ∫⁻ ω : (k : ℕ) → State n, ENNReal.ofReal ((1 - lam n * eps n / (15 * Real.sqrt n)) *
              PhiT n (tSeq n j) (ω j) + lam n * eps n / (15 * Real.sqrt n) * (10 * n)) ∂P := by
            refine lintegral_mono_ae (hI.mono fun ω hω => ?_)
            rw [hκ]
            refine (kstep hn A hA U hU C hC j (frestrictLe j ω) hω).2.1.trans (le_of_eq ?_)
            rw [show current (frestrictLe j ω) = ω j from rfl]
            congr 1; ring
        _ ≤ ENNReal.ofReal ((1 - lam n * eps n / (15 * Real.sqrt n)) * (10 * n) +
              lam n * eps n / (15 * Real.sqrt n) * (10 * n)) :=
            lint_affine P _ ((measurable_PhiT n _).comp (measurable_pi_apply j))
              (fun ω => potential_nonneg' _ _) (by linarith [hc.2])
              (mul_nonneg hc.1 (by positivity)) (by positivity) hE
        _ = ENNReal.ofReal (10 * n) := by congr 1; ring

end CohenLeeSongLP.StochCentralPath.L414

open CohenLeeSongLP.StochCentralPath in
theorem solution {n d : ℕ} (hn : 10 ≤ n)
    (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (x0 s0 : Fin n → ℝ) (hx0 : ∀ i, 0 < x0 i) (hs0 : ∀ i, 0 < s0 i)
    (hinit : ApproxScalar (1 / lam n) (fun i => x0 i * s0 i) 1)
    (U : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ))
    (hUmeas : ∀ j, Measurable (U j))
    (hU : ∀ j (h : (i : Finset.Iic j) → State n),
      (∀ i, 0 < (current h).1 i) → (∀ i, 0 < (current h).2.1 i) →
      ApproxVec epsMp (fun i => (current h).1 i / (current h).2.1 i) (U j h))
    (C : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ) × (Fin n → ℝ))
    (hCmeas : ∀ j, Measurable (C j))
    (hC : ∀ j (h : (i : Finset.Iic j) → State n),
      (∀ i, 0 < (current h).1 i) → (∀ i, 0 < (current h).2.1 i) →
      ApproxScalar 0.1 (fun i => (current h).1 i * (current h).2.1 i) (tSeq n j) →
      (∀ i, 0 < (C j h).1 i) ∧ (∀ i, 0 < (C j h).2 i) ∧
      potential (lam n) (fun i => (C j h).1 i * (C j h).2 i / tSeq n (j + 1) - 1) ≤ (n : ℝ) ^ 3)
    (κ : (j : ℕ) → ProbabilityTheory.Kernel ((i : Finset.Iic j) → State n) (State n))
    [∀ j, IsMarkovKernel (κ j)]
    (hκ : ∀ j h, κ j h = mainStepLaw A U C j h) (j : ℕ) :
    (∀ᵐ (ω : (k : ℕ) → State n) ∂(ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (x0, s0, false)) κ),
      Assumption41 (ω j).1 (ω j).2.1 (tSeq n j) (U j (fun i => ω i))
        (direction (lam n) (eps n) (tSeq n j) (tSeq n (j + 1)) (ω j).1 (ω j).2.1)
        (kSampMain n) (eps n) epsMp) ∧
    (∀ᵐ (ω : (k : ℕ) → State n) ∂(ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (x0, s0, false)) κ),
      0 < sampleLaw (kSampMain n)
        (direction (lam n) (eps n) (tSeq n j) (tSeq n (j + 1)) (ω j).1 (ω j).2.1)
        (successEvent A (ω j).1 (ω j).2.1 (U j (fun i => ω i)))) ∧
    ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (x0, s0, false)) κ
        {ω : (k : ℕ) → State n | (ω (j + 1)).2.2 = true} ≤ ENNReal.ofReal (10 / (n : ℝ) ^ 2) := by
  obtain ⟨hI, hE⟩ := L414.induct hn A hA x0 s0 hx0 hs0 hinit U hU C hC κ hκ j
  have hT := L414.tSeq_pos' hn j
  have h41 : ∀ᵐ (ω : (k : ℕ) → State n) ∂(ProbabilityTheory.Kernel.trajMeasure
      (Measure.dirac (x0, s0, false)) κ),
      Assumption41 (ω j).1 (ω j).2.1 (tSeq n j) (U j (fun i => ω i))
        (direction (lam n) (eps n) (tSeq n j) (tSeq n (j + 1)) (ω j).1 (ω j).2.1)
        (kSampMain n) (eps n) epsMp := by
    filter_upwards [hI] with ω hω
    rw [L414.tSeq_succ']
    exact L414.asm41 hn hT (ω j).1 (ω j).2.1 (U j (fun i => ω i)) hω.1 hω.2.1 hω.2.2
      (hU j (fun i => ω i) hω.1 hω.2.1)
  refine ⟨h41, ?_, ?_⟩
  · filter_upwards [h41] with ω hω
    exact L414.success_pos_of hn A _ _ _ _
      (success_probability hn A hA _ _ _ _ (tSeq n j) _ _ _ hω).2
  · have hc := L414.c_bounds hn
    have hn0 : (0:ℝ) < n := by
      have : (10:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hn3 : (0:ℝ) < (n:ℝ) ^ 3 := by positivity
    have hflag : MeasurableSet {y : State n | y.2.2 = true} :=
      measurable_snd.snd (measurableSet_singleton true)
    have e := L414.traj_succ_set κ (Measure.dirac (x0, s0, false)) j {y : State n | y.2.2 = true} hflag
    calc ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (x0, s0, false)) κ
          {ω : (k : ℕ) → State n | (ω (j + 1)).2.2 = true}
        = ∫⁻ ω : (k : ℕ) → State n, κ j (Preorder.frestrictLe j ω) {y : State n | y.2.2 = true}
            ∂(ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (x0, s0, false)) κ) := e
      _ ≤ ∫⁻ ω : (k : ℕ) → State n, ENNReal.ofReal ((1 - lam n * eps n / (15 * Real.sqrt n)) / (n:ℝ) ^ 3 *
              L414.PhiT n (tSeq n j) (ω j) +
              lam n * eps n / (15 * Real.sqrt n) * (10 * n) / (n:ℝ) ^ 3)
            ∂(ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (x0, s0, false)) κ) := by
          refine lintegral_mono_ae (hI.mono fun ω hω => ?_)
          rw [hκ]
          refine (L414.kstep hn A hA U hU C hC j (Preorder.frestrictLe j ω) hω).2.2.trans
            (le_of_eq ?_)
          rw [← ENNReal.ofReal_div_of_pos hn3, show current (Preorder.frestrictLe j ω) = ω j from rfl]
          congr 1; ring
      _ ≤ ENNReal.ofReal ((1 - lam n * eps n / (15 * Real.sqrt n)) / (n:ℝ) ^ 3 * (10 * n) +
              lam n * eps n / (15 * Real.sqrt n) * (10 * n) / (n:ℝ) ^ 3) :=
          L414.lint_affine _ _ ((L414.measurable_PhiT n _).comp (measurable_pi_apply j))
            (fun ω => L414.potential_nonneg' _ _)
            (div_nonneg (by linarith [hc.2]) hn3.le)
            (div_nonneg (mul_nonneg hc.1 (by positivity)) hn3.le) (by positivity) hE
      _ = ENNReal.ofReal (10 / (n : ℝ) ^ 2) := by
          congr 1; field_simp; ring
