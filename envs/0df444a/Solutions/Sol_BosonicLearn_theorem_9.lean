-- Prove2me | solution 1 for BosonicLearn.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:21:39.414075+00:00
-- url     : https://prove2.me/submissions/fef62c2f-2b99-475c-8f4a-8cb868806289

import Mathlib
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_promiseClass
import Definitions.Def_BosonicLearn_IsPassive
import Theorems.Thm_BosonicLearn_hermitian_packing
import Theorems.Thm_BosonicLearn_occupation_family
import Theorems.Thm_BosonicLearn_occupation_count_separation
import Theorems.Thm_BosonicLearn_povm_renyi2_converse
import Theorems.Thm_BosonicLearn_fugacity_renyi2_tensorPow
import Theorems.Thm_BosonicLearn_traceDist_triangle

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize NuclearExpansion IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.RealRegisters (Hilbert)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-! ### Symmetry of the trace norm (copied from the assembly of Theorem 5) -/

/-- `NucRep X w`: the matrix `X` is a sum `∑ₐ |Lₐ⟩⟨Rₐ|` over a countable index set, with total weight
`∑ₐ ‖Lₐ‖‖Rₐ‖ = w`. -/
private def NucRep {I : Type} (X : Matrix I I ℂ) (w : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (L R : ι → Hilbert I),
    HasSum (fun a => ‖L a‖ * ‖R a‖) w ∧ ∀ i j, HasSum (fun a => L a i * star (R a j)) (X i j)

/-- A representation of weight `w` bounds the trace size by `w`: re-index it by `ℕ`. -/
private lemma rep_traceSize {I : Type} {X : Matrix I I ℂ} {w : ℝ} (h : NucRep X w) :
    traceSize X ≤ ENNReal.ofReal w := by
  obtain ⟨ι, hι, L, R, hw, hX⟩ := h
  obtain ⟨g, hg⟩ := exists_injective_nat ι
  have key1 : (fun n => ‖Function.extend g L 0 n‖ * ‖Function.extend g R 0 n‖) =
      Function.extend g (fun a => ‖L a‖ * ‖R a‖) 0 := by
    funext n
    by_cases hn : ∃ a, g a = n
    · obtain ⟨a, rfl⟩ := hn
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  have key2 : ∀ i j, (fun n => (Function.extend g L 0 n) i * star ((Function.extend g R 0 n) j)) =
      Function.extend g (fun a => L a i * star (R a j)) 0 := by
    intro i j
    funext n
    by_cases hn : ∃ a, g a = n
    · obtain ⟨a, rfl⟩ := hn
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  let e : NuclearExpansion X :=
    { left := Function.extend g L 0
      right := Function.extend g R 0
      summable := by
        rw [key1]
        exact (summable_extend_zero hg).mpr hw.summable
      coefficients := by
        intro i j
        rw [key2 i j, tsum_extend_zero hg]
        exact (hX i j).tsum_eq.symm }
  refine (iInf_le _ e).trans (le_of_eq ?_)
  congr 1
  show ∑' n, ‖Function.extend g L 0 n‖ * ‖Function.extend g R 0 n‖ = w
  rw [key1, tsum_extend_zero hg]
  exact hw.tsum_eq

/-- A nuclear expansion is a representation with the same weight. -/
private lemma rep_of_expansion {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    NucRep X (∑' n, ‖e.left n‖ * ‖e.right n‖) := by
  refine ⟨ℕ, inferInstance, e.left, e.right, e.summable.hasSum, fun i j => ?_⟩
  rw [e.coefficients i j]
  have h : Summable fun a => e.left a i * star (e.right a j) := by
    refine Summable.of_norm_bounded e.summable fun a => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) (e.left a) i)
      (lp.norm_apply_le_norm (by norm_num) (e.right a) j) (norm_nonneg _) (norm_nonneg _)
  exact h.hasSum

private lemma rep_neg {I : Type} {X : Matrix I I ℂ} {w : ℝ} (hX : NucRep X w) : NucRep (-X) w := by
  obtain ⟨ι, hι, L, R, hw, hX⟩ := hX
  refine ⟨ι, hι, fun a => -L a, R, ?_, fun i j => ?_⟩
  · simpa using hw
  · have h := (hX i j).neg
    simpa [neg_mul] using h

/-- Symmetry of the trace norm under negation. -/
private lemma traceSize_neg {I : Type} (X : Matrix I I ℂ) : traceSize (-X) = traceSize X := by
  have key : ∀ Y : Matrix I I ℂ, traceSize (-Y) ≤ traceSize Y := by
    intro Y
    show traceSize (-Y) ≤ ⨅ e : NuclearExpansion Y, ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖)
    exact le_iInf fun e => rep_traceSize (rep_neg (rep_of_expansion e))
  refine le_antisymm (key X) ?_
  have h := key (-X)
  rwa [neg_neg] at h

private lemma traceDist_comm' {I : Type} (A B : Matrix I I ℂ) : traceDist A B = traceDist B A := by
  unfold traceDist
  rw [← neg_sub B A, traceSize_neg]

/-! ### Trace-distance balls -/

/-- Closed trace-distance balls around a state are Borel sets of the trace-norm topology. -/
private lemma measurableSet_traceBall {I : Type} (ρ : State I) (ε : ℝ) (hε : 0 ≤ ε) :
    MeasurableSet {σ : State I | traceDist σ.coefficients ρ.coefficients ≤ ENNReal.ofReal ε} := by
  have e : {σ : State I | traceDist σ.coefficients ρ.coefficients ≤ ENNReal.ofReal ε} =
      ⋂ k : ℕ, {σ : State I | traceSize (σ.coefficients - ρ.coefficients) <
        ENNReal.ofReal (2 * ε + 1 / ((k : ℝ) + 1))} := by
    ext σ
    rw [Set.mem_iInter]
    show traceDist σ.coefficients ρ.coefficients ≤ ENNReal.ofReal ε ↔
      ∀ k : ℕ, traceSize (σ.coefficients - ρ.coefficients) <
        ENNReal.ofReal (2 * ε + 1 / ((k : ℝ) + 1))
    unfold traceDist
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    have h2 : ENNReal.ofReal ε * 2 = ENNReal.ofReal (2 * ε) := by
      rw [mul_comm 2 ε, ENNReal.ofReal_mul hε]
      simp
    rw [h2]
    constructor
    · intro h k
      refine h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · intro h
      refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ by exact_mod_cast hδ)
      refine (h k).le.trans ?_
      have h3 : ENNReal.ofReal (2 * ε) + (δ : ℝ≥0∞) = ENNReal.ofReal (2 * ε + δ) := by
        rw [ENNReal.ofReal_add (by positivity) δ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      rw [h3]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [e]
  refine MeasurableSet.iInter fun k => ?_
  have ho : IsOpen {σ : State I | traceSize (σ.coefficients - ρ.coefficients) <
      ENNReal.ofReal (2 * ε + 1 / ((k : ℝ) + 1))} :=
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨ρ, 2 * ε + 1 / ((k : ℝ) + 1), by positivity, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom ho

/-- A point within `ε` of two centres at trace-norm distance `≥ 5ε` does not exist. -/
private lemma ball_disjoint_aux (ε : ℝ) (hε : 0 < ε) (t : ℝ≥0∞) (h1 : ENNReal.ofReal (5 * ε) ≤ t)
    (h2 : t / 2 ≤ ENNReal.ofReal ε + ENNReal.ofReal ε) : False := by
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))] at h2
  have h3 : (ENNReal.ofReal ε + ENNReal.ofReal ε) * 2 = ENNReal.ofReal (4 * ε) := by
    rw [← ENNReal.ofReal_add hε.le hε.le, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [h3] at h2
  have h4 := h1.trans h2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h4
  linarith

/-! ### Counting disjoint events -/

private lemma packing_count {O ι : Type} [MeasurableSpace O] (μ : Measure O) [IsProbabilityMeasure μ]
    (T : Finset ι) (B : ι → Set O) (hB : ∀ X ∈ T, MeasurableSet (B X))
    (hdis : ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → Disjoint (B X) (B Y)) (a : ℝ)
    (ha : ∀ X ∈ T, a ≤ (μ (B X)).toReal) : (T.card : ℝ) * a ≤ 1 := by
  have h1 : μ (⋃ X ∈ T, B X) = ∑ X ∈ T, μ (B X) :=
    measure_biUnion_finset (fun X hX Y hY hXY => hdis X hX Y hY hXY) hB
  have h2 : ∑ X ∈ T, μ (B X) ≤ 1 := h1 ▸ prob_le_one
  have h3 : ∑ X ∈ T, (μ (B X)).toReal ≤ 1 := by
    rw [← ENNReal.toReal_sum (fun X _ => measure_ne_top μ _)]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h2)
  calc (T.card : ℝ) * a = ∑ _X ∈ T, a := by simp
    _ ≤ ∑ X ∈ T, (μ (B X)).toReal := Finset.sum_le_sum ha
    _ ≤ 1 := h3

/-! ### The Rényi-2 converse for one member of the family -/

private lemma renyi_bound {n N : ℕ}
    (E : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n))))
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef) (hR1 : (1 - R).PosDef) (r₀ : ℝ)
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hR2 : (((r₀ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R * R).PosDef)
    (K : ℝ)
    (hK : (1 - R).det.re ^ 2 / ((1 - r₀) ^ n * (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det.re) ≤ K)
    (B : Set (State (Occupation (Fin n)))) (hB : MeasurableSet B)
    (hsucc : ENNReal.ofReal (2 / 3) ≤
      E.law (WildeQIT.Schumacher.tensorPow N (fugacityCoeff R)) B) :
    IsDensity (Matrix.diagonal fun x : Fin N → Occupation (Fin n) =>
      ((∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x t i)) : ℝ) : ℂ)) ∧
    (4 / 9 : ℝ) ≤ (E.law (Matrix.diagonal fun x : Fin N → Occupation (Fin n) =>
      ((∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x t i)) : ℝ) : ℂ)) B).toReal * K ^ N := by
  obtain ⟨hdens, hp1, hdet, hq⟩ := fugacity_renyi2_tensorPow R hR hR1 r₀ h0 h1 hR2 N
  have hr1 : 0 < 1 - r₀ := by linarith
  have hp : ∀ x : Fin N → Occupation (Fin n), 0 < ∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x t i)) :=
    fun x => Finset.prod_pos fun t _ => by positivity
  obtain ⟨hσ, hineq⟩ := povm_renyi2_converse E _ hdens
    (fun x : Fin N → Occupation (Fin n) => ∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x t i))) hp hp1 _ hq B hB
  refine ⟨hσ, ?_⟩
  have hprob := E.law_prob _ hdens
  have h23 : (2 / 3 : ℝ) ≤ (E.law (WildeQIT.Schumacher.tensorPow N (fugacityCoeff R)) B).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hsucc
  have hq0 : 0 ≤ (1 - R).det.re ^ 2 / ((1 - r₀) ^ n * (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det.re) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hr1.le _) hdet.le)
  have hpow := pow_le_pow_left₀ hq0 hK N
  have hsq : (4 / 9 : ℝ) ≤
      (E.law (WildeQIT.Schumacher.tensorPow N (fugacityCoeff R)) B).toReal ^ 2 := by
    nlinarith
  refine hsq.trans (hineq.trans ?_)
  exact mul_le_mul_of_nonneg_left hpow ENNReal.toReal_nonneg

/-! ### The occupation family -/

private def occN {n : ℕ} (m ξ : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((m : ℝ) : ℂ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + ((ξ : ℝ) : ℂ) • X)

private def occR {n : ℕ} (m ξ : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  occN m ξ X * (1 + occN m ξ X)⁻¹

private lemma occN_sub {n : ℕ} (m ξ : ℝ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    occN m ξ X - occN m ξ Y = ((m * ξ : ℝ) : ℂ) • (X - Y) := by
  unfold occN
  push_cast
  module

private lemma occN_sep_hyp {n : ℕ} (m ξ : ℝ) (hm : 0 ≤ m) (hξ : 0 ≤ ξ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) (hXtr : X.trace = 0) (hYtr : Y.trace = 0)
    (hX4 : (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef)
    (hX4' : (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef)
    (hY4 : (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Y).PosSemidef)
    (hY4' : (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + Y).PosSemidef) :
    (occN m ξ X - occN m ξ Y).trace = 0 ∧
    (((8 * ξ * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      (occN m ξ X - occN m ξ Y)).PosSemidef ∧
    (((8 * ξ * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
      (occN m ξ X - occN m ξ Y)).PosSemidef ∧
    ((occN m ξ X - occN m ξ Y) * (occN m ξ X - occN m ξ Y)).trace.re =
      (m * ξ) ^ 2 * ((X - Y) * (X - Y)).trace.re := by
  have h0 : (0 : ℂ) ≤ ((m * ξ : ℝ) : ℂ) := by
    exact_mod_cast mul_nonneg hm hξ
  rw [occN_sub]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.trace_smul, Matrix.trace_sub, hXtr, hYtr]
    simp
  · have e : ((8 * ξ * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - ((m * ξ : ℝ) : ℂ) • (X - Y) =
        ((m * ξ : ℝ) : ℂ) • ((((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X) +
          (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + Y)) := by
      push_cast
      module
    rw [e]
    exact (hX4.add hY4').smul h0
  · have e : ((8 * ξ * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + ((m * ξ : ℝ) : ℂ) • (X - Y) =
        ((m * ξ : ℝ) : ℂ) • ((((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X) +
          (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Y)) := by
      push_cast
      module
    rw [e]
    exact (hX4'.add hY4).smul h0
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring

/-! ### Numerics -/

private lemma xi_numeric (κ ε s : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (hεlt : ε < 7 * κ / 2560)
    (hs : 7 / 2 ≤ s) :
    0 < 40 * ε / (κ * s) ∧ 40 * ε / (κ * s) ≤ 1 / 32 ∧ 8 * (40 * ε / (κ * s)) * s ≤ 7 / 8 ∧
      (40 * ε / (κ * s)) ^ 2 * s ^ 2 = 1600 * ε ^ 2 / κ ^ 2 := by
  have hs0 : 0 < s := by linarith
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have e : 8 * (40 * ε / (κ * s)) * s = 320 * ε / κ := by
      field_simp
      ring
    rw [e, div_le_iff₀ hκ]
    linarith
  · field_simp
    norm_num

private lemma sep_numeric (c₃ b m ξ s t ε κ : ℝ) (hc₃ : 0 < c₃) (hm : 1 ≤ m) (hξ : 0 < ξ)
    (hs : 0 < s) (ht : b * s ^ 2 ≤ t) (hκ : κ = c₃ * b) (hκ0 : 0 < κ)
    (hξdef : ξ = 40 * ε / (κ * s)) :
    5 * ε ≤ c₃ * ((m * ξ) ^ 2 * t) / (8 * ξ * m ^ 2 * s) := by
  have hm0 : 0 < m := by linarith
  have hε : ε = κ * ξ * s / 40 := by
    rw [hξdef]
    field_simp
  rw [le_div_iff₀ (by positivity), hε, hκ]
  have h := mul_le_mul_of_nonneg_left ht (show 0 ≤ c₃ * (m * ξ) ^ 2 by positivity)
  nlinarith

private lemma final_numeric (c κ ε x Nr A : ℝ) (hc : 0 < c) (hκ : 0 < κ) (hε : 0 < ε)
    (hx : 2 ≤ c * x) (hA : A = 33600 * ε ^ 2 / κ ^ 2 * Nr)
    (h : Real.exp (c * x) ≤ 9 / 4 * Real.exp A) : c * κ ^ 2 / 67200 * (x / ε ^ 2) ≤ Nr := by
  have he : (9 / 4 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h1 : Real.exp (c * x) ≤ Real.exp (1 + A) := by
    rw [Real.exp_add]
    exact h.trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le)
  have h2 : c * x ≤ 1 + A := Real.exp_le_exp.mp h1
  have h3 : c * x / 2 ≤ 33600 * ε ^ 2 / κ ^ 2 * Nr := by
    rw [← hA]
    linarith
  have h4 : c * κ ^ 2 / 67200 * (x / ε ^ 2) = c * x / 2 * (κ ^ 2 / (33600 * ε ^ 2)) := by
    field_simp
    ring
  rw [h4]
  calc c * x / 2 * (κ ^ 2 / (33600 * ε ^ 2))
      ≤ 33600 * ε ^ 2 / κ ^ 2 * Nr * (κ ^ 2 / (33600 * ε ^ 2)) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = Nr := by
        field_simp

/-! ### The statement -/

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, ∀ ν : ℝ, 0 < ν → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ n : ℕ, n₀ ≤ n →
      ∀ (N : ℕ) (E : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n)))),
        (∀ ρ ∈ promiseClass n ν, IsPassive ρ → ENNReal.ofReal (2 / 3) ≤ collectiveSuccess E ρ ε) →
        C * ((n : ℝ) ^ 2 / ε ^ 2) ≤ N := by
  obtain ⟨b, hb, c, hc, n₁, hpack⟩ := hermitian_packing
  obtain ⟨c₃, hc₃, hsep⟩ := occupation_count_separation
  have hκ : 0 < c₃ * b := by positivity
  refine ⟨c * (c₃ * b) ^ 2 / 67200, by positivity, 7 * (c₃ * b) / 2560, by positivity,
    max n₁ (max 13 ⌈2 / c⌉₊), ?_⟩
  intro ν hν ε hε hεlt n hn N E H
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn13 : 13 ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnc : ⌈2 / c⌉₊ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hn13r : (13 : ℝ) ≤ n := by exact_mod_cast hn13
  have hnpos : (0 : ℝ) < n := by linarith
  have hcn : 2 ≤ c * (n : ℝ) ^ 2 := by
    have h1 : 2 / c ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnc)
    rw [div_le_iff₀ hc] at h1
    nlinarith
  obtain ⟨T, hcard, hT, hTsep⟩ := hpack n hn1
  -- parameters
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hnpos.le
  have hs72 : (7 / 2 : ℝ) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hspos : 0 < Real.sqrt n := by linarith
  obtain ⟨hξ0, hξ32, hθ, hξn⟩ := xi_numeric (c₃ * b) ε (Real.sqrt n) hκ hε hεlt hs72
  set ξ : ℝ := 40 * ε / (c₃ * b * Real.sqrt n) with hξdef
  set m : ℝ := 1 + 2 * ν with hmdef
  have hm : 1 ≤ m := by rw [hmdef]; linarith
  have hm0 : 0 < m := by linarith
  have hνm : ν ≤ 7 / 8 * m := by rw [hmdef]; linarith
  rw [hs2] at hξn
  -- the family
  have hfam := fun X (hX : X ∈ T) => occupation_family X (hT X hX).1 (hT X hX).2.2.1
    (hT X hX).2.2.2 m ξ hm hξ0 hξ32 (occN m ξ X) (occR m ξ X) rfl rfl
  have hstate : ∀ X ∈ T, ∃ ρ : State (Occupation (Fin n)),
      ρ.coefficients = fugacityCoeff (occR m ξ X) ∧ IsPassive ρ ∧ ρ ∈ promiseClass n ν :=
    fun X hX => (hfam X hX).2.2.2.2.2.1 ν hν hνm
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (0 : ℝ) < T.card := lt_of_lt_of_le (Real.exp_pos _) hcard
    exact_mod_cast h1
  obtain ⟨X₀, hX₀⟩ := hTne
  have hne : Nonempty (State (Occupation (Fin n))) := ⟨(hstate X₀ hX₀).choose⟩
  choose! ρf hρco hρpas hρprom using hstate
  -- the balls
  set B : Matrix (Fin n) (Fin n) ℂ → Set (State (Occupation (Fin n))) := fun X =>
    {σ | traceDist σ.coefficients (ρf X).coefficients ≤ ENNReal.ofReal ε} with hBdef
  have hBmeas : ∀ X ∈ T, MeasurableSet (B X) := fun X _ => measurableSet_traceBall (ρf X) ε hε.le
  have hr0 : 0 < m / (1 + m) := by positivity
  have hr1 : m / (1 + m) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  -- the Rényi bound for each member
  have hren := fun X (hX : X ∈ T) => renyi_bound E (occR m ξ X) (hfam X hX).2.2.1
    (hfam X hX).2.2.2.1 (m / (1 + m)) hr0 hr1 (hfam X hX).2.2.2.2.1 (Real.exp (21 * ξ ^ 2 * n))
    (hfam X hX).2.2.2.2.2.2 (B X) (hBmeas X hX) (by
      have h := H (ρf X) (hρprom X hX) (hρpas X hX)
      rw [← hρco X hX]
      exact h)
  have hprob := E.law_prob _ (hren X₀ hX₀).1
  -- disjointness
  have hdis : ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → Disjoint (B X) (B Y) := by
    intro X hX Y hY hXY
    obtain ⟨htr, hp1, hp2, hsq⟩ := occN_sep_hyp m ξ hm0.le hξ0.le X Y (hT X hX).2.1 (hT Y hY).2.1
      (hT X hX).2.2.1 (hT X hX).2.2.2 (hT Y hY).2.2.1 (hT Y hY).2.2.2
    have h3 := hsep n m (8 * ξ) hm (by positivity) hθ (occN m ξ X) (occN m ξ Y)
      (hfam X hX).1 (hfam X hX).2.1 (hfam Y hY).1 (hfam Y hY).2.1 htr hp1 hp2
    rw [hsq] at h3
    have h5 : ENNReal.ofReal (5 * ε) ≤
        traceSize ((ρf X).coefficients - (ρf Y).coefficients) := by
      rw [hρco X hX, hρco Y hY]
      refine (ENNReal.ofReal_le_ofReal ?_).trans h3
      exact sep_numeric c₃ b m ξ (Real.sqrt n) _ ε (c₃ * b) hc₃ hm hξ0 hspos
        (by rw [hs2]; exact hTsep X hX Y hY hXY) rfl hκ hξdef
    rw [Set.disjoint_left]
    intro σ hσX hσY
    have h6 : traceDist (ρf X).coefficients (ρf Y).coefficients ≤
        ENNReal.ofReal ε + ENNReal.ofReal ε :=
      (traceDist_triangle _ σ.coefficients _).trans
        (add_le_add (by rw [traceDist_comm']; exact hσX) hσY)
    exact ball_disjoint_aux ε hε _ h5 h6
  -- counting
  have hKpos : 0 < Real.exp (21 * ξ ^ 2 * n) ^ N := by positivity
  have hcount := packing_count _ T B hBmeas hdis ((4 / 9) / Real.exp (21 * ξ ^ 2 * n) ^ N)
    (fun X hX => by
      rw [div_le_iff₀ hKpos]
      exact (hren X hX).2)
  have hcard2 : (T.card : ℝ) ≤ 9 / 4 * Real.exp (21 * ξ ^ 2 * n) ^ N := by
    rw [← mul_div_assoc, div_le_iff₀ hKpos] at hcount
    linarith
  have hfin : Real.exp (c * (n : ℝ) ^ 2) ≤ 9 / 4 * Real.exp ((N : ℝ) * (21 * ξ ^ 2 * n)) := by
    rw [Real.exp_nat_mul]
    exact hcard.trans hcard2
  refine final_numeric c (c₃ * b) ε ((n : ℝ) ^ 2) N _ hc hκ hε hcn ?_ hfin
  have e : (N : ℝ) * (21 * ξ ^ 2 * n) = 21 * (ξ ^ 2 * n) * N := by ring
  rw [e, hξn]
  ring
