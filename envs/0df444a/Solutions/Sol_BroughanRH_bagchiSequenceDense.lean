-- Prove2me | solution 1 for BroughanRH.bagchiSequenceDense
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T02:05:02.866249+00:00
-- url     : https://prove2.me/submissions/35b41116-8514-4362-98fb-3313c06fa899
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NymanBeurling_damped_spectral_vanishing_of_ratio_bound
import Theorems.Thm_NymanBeurling_damped_mellin_completion_of_polynomial_bound
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_NymanAux_moebiusPolynomialBoundaryBound_of_riemannHypothesis
import Theorems.Thm_NymanAux_shiftedZetaRatioBound_of_riemannHypothesis

open MeasureTheory
open scoped BigOperators

theorem bagchiConst_of_bounds (hA : NymanBeurling.MoebiusPolynomialBoundaryBound)
    (hB : NymanBeurling.ShiftedZetaRatioBound) :
    let err (f : ℕ → ℂ) (N : ℕ) (a : Fin N → ℂ) (n : ℕ) :=
      ‖f n - ∑ j, a j * ((Int.fract ((n : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 /
        ((n : ℝ)*(n+1))
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      Summable (fun m : ℕ => err (fun _ => 1) N a (m+1)) ∧
      (∑' m : ℕ, err (fun _ => 1) N a (m+1)) < ε := by
  intro err ε hε
  obtain ⟨e₀, he₀, he₀h, hvan⟩ :=
    NymanBeurling.damped_spectral_vanishing_of_ratio_bound hB (ε / 8) (by linarith)
  set e : ℝ := e₀ / 2 with he
  have he0 : 0 < e := by positivity
  have hee : e < e₀ := by linarith
  have heh : e < 1/2 := by linarith
  obtain ⟨hint, hsmall⟩ := hvan e he0 hee
  obtain ⟨hcompl, hprof⟩ := NymanBeurling.damped_mellin_completion_of_polynomial_bound hA
  obtain ⟨N₀, hN₀⟩ := hcompl e he0 heh (ε / 8) (by linarith)
  obtain ⟨hsum, -, hpl⟩ := hprof e he0 heh
  set P := fun n : ℕ => (NymanBeurling.dampedResidualProfile e (n+1))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ)) with hP
  have hPt : (∑' n, P n) < ε / 8 := by
    have h2 : (2 * Real.pi) * (∑' n, P n) < ε / 8 := by rw [← hpl]; exact hsmall
    have hpi : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hP0 : 0 ≤ ∑' n, P n := tsum_nonneg (fun n => by positivity)
    nlinarith
  refine ⟨N₀ + 1, fun j => if j.val = 0 then 0 else
      -(((ArithmeticFunction.moebius (j.val+1) : ℝ) / ((j.val+1 : ℕ) : ℝ)^e : ℝ) : ℂ), ?_⟩
  -- identify the error terms
  have key : ∀ m : ℕ, err (fun _ => 1) (N₀+1) (fun j => if j.val = 0 then 0 else
      -(((ArithmeticFunction.moebius (j.val+1) : ℝ) / ((j.val+1 : ℕ) : ℝ)^e : ℝ) : ℂ)) (m+1) =
      (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ)) := by
    intro m
    simp only [err]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, if_pos, zero_mul, zero_add, Fin.val_succ]
    have : ∀ i : Fin N₀, (if (i.val + 1 = 0) then (0:ℂ) else
        -(((ArithmeticFunction.moebius (i.val+1+1) : ℝ) / ((i.val+1+1 : ℕ) : ℝ)^e : ℝ) : ℂ)) *
        ((Int.fract (((m+1 : ℕ) : ℝ)/(i.val+1+1 : ℕ)) : ℝ) : ℂ) =
        -((((ArithmeticFunction.moebius (i.val+2) : ℝ) / (i.val+2 : ℝ)^e) *
          (((m+1) % (i.val+2) : ℕ) : ℝ) / (i.val+2 : ℝ) : ℝ) : ℂ) := by
      intro i
      rw [if_neg (by omega)]
      have h1 : (Int.fract (((m+1 : ℕ) : ℝ)/((i.val+1+1 : ℕ) : ℝ))) =
          (((m+1) % (i.val+2) : ℕ) : ℝ) / (i.val+2 : ℝ) := by
        rw [Int.fract_div_natCast_eq_div_natCast_mod]; push_cast; ring_nf
      rw [h1]; push_cast; ring_nf
    have hc : ((m+1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [show ((↑(m+1) : ℝ)) = ((m+1 : ℕ) : ℝ) from rfl] at *
    simp_rw [this]
    rw [Finset.sum_neg_distrib, sub_neg_eq_add]
    unfold NymanBeurling.dampedResidualFinite
    rw [show ((m+1 : ℕ) : ℝ) * (((m+1 : ℕ) : ℝ) + 1) = ((m+1 : ℝ)*(m+2 : ℝ)) by push_cast; ring]
    congr 1
    rw [← Complex.ofReal_sum, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hle : ∀ H : ℕ, ∑ m ∈ Finset.range H,
      (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ)) ≤ ε / 2 := by
    intro H
    have hw : ∀ m : ℕ, 0 < ((m+1 : ℝ)*(m+2 : ℝ)) := fun m => by positivity
    have h1 := hN₀ N₀ le_rfl H
    have h2 : ∑ m ∈ Finset.range H, P m ≤ ∑' n, P n :=
      hsum.sum_le_tsum _ (fun n _ => by positivity)
    calc ∑ m ∈ Finset.range H,
          (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ))
        ≤ ∑ m ∈ Finset.range H, (2 * ((NymanBeurling.dampedResidualFinite N₀ e (m+1) -
            NymanBeurling.dampedResidualProfile e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ))) + 2 * P m) := by
          apply Finset.sum_le_sum; intro m _
          rw [hP]; dsimp only
          rw [mul_div_assoc', mul_div_assoc', ← add_div]
          apply div_le_div_of_nonneg_right _ (hw m).le
          nlinarith [sq_nonneg (NymanBeurling.dampedResidualFinite N₀ e (m+1) -
            2 * NymanBeurling.dampedResidualProfile e (m+1))]
      _ = 2 * ∑ m ∈ Finset.range H, ((NymanBeurling.dampedResidualFinite N₀ e (m+1) -
            NymanBeurling.dampedResidualProfile e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ))) +
            2 * ∑ m ∈ Finset.range H, P m := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ε / 2 := by linarith
  have hnn : ∀ m : ℕ, 0 ≤ (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 /
      ((m+1 : ℝ)*(m+2 : ℝ)) := fun m => by positivity
  simp_rw [key]
  refine ⟨summable_of_sum_range_le hnn hle, ?_⟩
  have := Real.tsum_le_of_sum_range_le hnn hle
  linarith


open Filter Topology
open scoped BigOperators ENNReal

namespace NymanDense

/-- finite combination of fractional-part sequences, coefficients `c j` at divisor `j+1`. -/
noncomputable def W (N : ℕ) (c : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, c j * ((Int.fract ((m : ℝ) / ((j+1 : ℕ) : ℝ)) : ℝ) : ℂ)

noncomputable def wt (m : ℕ) : ℝ := 1 / ((m : ℝ) * (m + 1))

lemma wt_nonneg (m : ℕ) : 0 ≤ wt m := by unfold wt; positivity

/-- weighted squared norm, as an extended real. -/
noncomputable def Q (u : ℕ → ℂ) : ℝ≥0∞ := ∑' m : ℕ, ENNReal.ofReal (‖u m‖ ^ 2 * wt m)

def Approx (F : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ c : ℕ → ℂ, Q (fun m => F m - W N c m) < ENNReal.ofReal ε

lemma W_zero (N : ℕ) (c : ℕ → ℂ) : W N c 0 = 0 := by simp [W]

lemma Q_add_le (u v : ℕ → ℂ) : Q (fun m => u m + v m) ≤ 2 * Q u + 2 * Q v := by
  unfold Q
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro m
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by have := wt_nonneg m; positivity) (by have := wt_nonneg m; positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hw := wt_nonneg m
  have h1 : ‖u m + v m‖ ^ 2 ≤ 2 * ‖u m‖ ^ 2 + 2 * ‖v m‖ ^ 2 := by
    have := norm_add_le (u m) (v m)
    nlinarith [norm_nonneg (u m), norm_nonneg (v m), norm_nonneg (u m + v m),
      sq_nonneg (‖u m‖ - ‖v m‖)]
  nlinarith

lemma Q_congr {u v : ℕ → ℂ} (h : ∀ m, u m = v m) : Q u = Q v := by
  unfold Q; simp_rw [h]

lemma Q_smul (k : ℂ) (u : ℕ → ℂ) : Q (fun m => k * u m) = ENNReal.ofReal (‖k‖ ^ 2) * Q u := by
  unfold Q
  rw [← ENNReal.tsum_mul_left]
  congr 1; funext m
  rw [← ENNReal.ofReal_mul (by positivity), norm_mul, mul_pow, mul_assoc]

lemma W_extend (N M : ℕ) (h : N ≤ M) (c : ℕ → ℂ) (m : ℕ) :
    W M (fun j => if j < N then c j else 0) m = W N c m := by
  unfold W
  have : Finset.range N = (Finset.range M).filter (fun j => j < N) := by
    ext j; simp; omega
  rw [this, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < N <;> simp [hj]

lemma W_add (N : ℕ) (c d : ℕ → ℂ) (k : ℂ) (m : ℕ) :
    W N (fun j => c j + k * d j) m = W N c m + k * W N d m := by
  unfold W
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

lemma approx_congr {F G : ℕ → ℂ} (hF : Approx F) (h : ∀ m, F m = G m) : Approx G := by
  intro ε hε
  obtain ⟨N, c, hc⟩ := hF ε hε
  exact ⟨N, c, by rw [Q_congr (fun m => by rw [← h m])]; exact hc⟩

lemma approx_add {F G : ℕ → ℂ} (hF : Approx F) (hG : Approx G) (k : ℂ) :
    Approx (fun m => F m + k * G m) := by
  intro ε hε
  have hk : 0 < 8 * (‖k‖ ^ 2 + 1) := by positivity
  obtain ⟨N1, c1, h1⟩ := hF (ε / 8) (by positivity)
  obtain ⟨N2, c2, h2⟩ := hG (ε / (8 * (‖k‖ ^ 2 + 1))) (by positivity)
  set N := max N1 N2
  refine ⟨N, fun j => (if j < N1 then c1 j else 0) + k * (if j < N2 then c2 j else 0), ?_⟩
  have hW : ∀ m, W N (fun j => (if j < N1 then c1 j else 0) + k * (if j < N2 then c2 j else 0)) m
      = W N1 c1 m + k * W N2 c2 m := by
    intro m
    rw [W_add, W_extend N1 N (le_max_left _ _), W_extend N2 N (le_max_right _ _)]
  rw [Q_congr (v := fun m => (F m - W N1 c1 m) + k * (G m - W N2 c2 m)) (fun m => by
    rw [hW]; ring)]
  refine lt_of_le_of_lt (Q_add_le _ _) ?_
  rw [Q_smul]
  have e1 : 2 * Q (fun m => F m - W N1 c1 m) ≤ 2 * ENNReal.ofReal (ε / 8) := by gcongr
  have e2 : 2 * (ENNReal.ofReal (‖k‖ ^ 2) * Q (fun m => G m - W N2 c2 m)) ≤
      2 * (ENNReal.ofReal (‖k‖ ^ 2) * ENNReal.ofReal (ε / (8 * (‖k‖ ^ 2 + 1)))) := by gcongr
  refine lt_of_le_of_lt (add_le_add e1 e2) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [ENNReal.ofReal_lt_ofReal_iff hε]
  have : ‖k‖ ^ 2 * (ε / (8 * (‖k‖ ^ 2 + 1))) ≤ ε / 8 := by
    rw [mul_div_assoc', div_le_div_iff₀ hk (by norm_num)]
    nlinarith [sq_nonneg ‖k‖]
  norm_num
  nlinarith

/-- `{⌊m/q⌋/k} = {m/(qk)} - {m/q}/k`. -/
lemma fract_div_div (m q k : ℕ) (hq : 0 < q) (hk : 0 < k) :
    Int.fract (((m / q : ℕ) : ℝ) / (k : ℝ)) =
      Int.fract ((m : ℝ) / ((q * k : ℕ) : ℝ)) - Int.fract ((m : ℝ) / (q : ℝ)) / k := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod, Int.fract_div_natCast_eq_div_natCast_mod,
    Int.fract_div_natCast_eq_div_natCast_mod]
  have h := (Nat.mod_mul (a := q) (b := k) (x := m))
  have h' : ((m % (q * k) : ℕ) : ℝ) = ((m % q : ℕ) : ℝ) + (q : ℝ) * ((m / q % k : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [h']
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  push_cast
  field_simp
  ring

/-- dilation: the span is stable under `m ↦ ⌊m/q⌋`. -/
lemma W_dilate (N q : ℕ) (hq : 0 < q) (c : ℕ → ℂ) :
    ∃ N' : ℕ, ∃ c' : ℕ → ℂ, ∀ m, W N' c' m = W N c (m / q) := by
  set S : ℂ := ∑ j ∈ Finset.range N, c j / ((j+1 : ℕ) : ℂ)
  refine ⟨q * (N + 1), fun i => (∑ j ∈ Finset.range N, if q * (j+1) = i + 1 then c j else 0) -
      (if i + 1 = q then S else 0), ?_⟩
  intro m
  set X : ℕ → ℂ := fun i => ((Int.fract ((m : ℝ) / ((i+1 : ℕ) : ℝ)) : ℝ) : ℂ)
  unfold W
  change ∑ i ∈ Finset.range (q * (N+1)), ((∑ j ∈ Finset.range N,
      if q * (j+1) = i + 1 then c j else 0) - (if i + 1 = q then S else 0)) * X i = _
  simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ j ∈ Finset.range N, ∑ i ∈ Finset.range (q * (N+1)),
      (if q * (j+1) = i + 1 then c j else 0) * X i = c j * X (q * (j+1) - 1) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [Finset.sum_eq_single (q * (j+1) - 1)]
    · rw [if_pos (by have : 1 ≤ q * (j+1) := Nat.one_le_iff_ne_zero.mpr (by positivity); omega)]
    · intro i _ hi
      rw [if_neg (by omega), zero_mul]
    · intro hi
      exfalso; apply hi
      rw [Finset.mem_range]
      have : q * (j+1) ≤ q * (N+1) := Nat.mul_le_mul_left _ (by omega)
      have : 1 ≤ q * (j+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
  have h2 : ∑ i ∈ Finset.range (q * (N+1)), (if i + 1 = q then S else 0) * X i = S * X (q - 1) := by
    rw [Finset.sum_eq_single (q - 1)]
    · rw [if_pos (by omega)]
    · intro i _ hi; rw [if_neg (by omega), zero_mul]
    · intro hi; exfalso; apply hi; rw [Finset.mem_range]
      have : q ≤ q * (N+1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  rw [Finset.sum_congr rfl h1, h2]
  simp only [S, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [X]
  have e1 : q * (j+1) - 1 + 1 = q * (j + 1) := by
    have : 1 ≤ q * (j+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have e2 : q - 1 + 1 = q := by omega
  rw [e1, e2, fract_div_div m q (j+1) hq (Nat.succ_pos j)]
  push_cast
  have : ((j:ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  field_simp

lemma telescope (A : ℝ) (hA : 0 < A) (q : ℕ) :
    ∑ i ∈ Finset.range q, 1 / ((A + i) * (A + i + 1)) = 1 / A - 1 / (A + q) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 0 < A + n := by positivity
    push_cast
    field_simp
    ring

lemma approx_ge (h1 : Approx (fun _ => 1)) (q : ℕ) (hq : 0 < q) :
    Approx (fun m => if q ≤ m then 1 else 0) := by
  have : NeZero q := ⟨hq.ne'⟩
  intro ε hε
  obtain ⟨N, c, hc⟩ := h1 ε hε
  obtain ⟨N', c', hc'⟩ := W_dilate N q hq c
  refine ⟨N', c', lt_of_le_of_lt ?_ hc⟩
  unfold Q
  rw [← (Nat.divModEquiv q).symm.tsum_eq, ENNReal.tsum_prod']
  apply ENNReal.tsum_le_tsum
  intro r
  rw [tsum_fintype]
  simp only [Nat.divModEquiv_symm_apply]
  have hdiv : ∀ i : Fin q, (r * q + (i : ℕ)) / q = r := by
    intro i
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  simp_rw [hc', hdiv]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp only [zero_mul, zero_add, W_zero, sub_zero]
    have : ∀ i : Fin q, ¬ q ≤ (i : ℕ) := fun i => by have := i.isLt; omega
    simp [this]
  · have hge : ∀ i : Fin q, q ≤ r * q + (i : ℕ) := fun i => by
      have : q ≤ r * q := Nat.le_mul_of_pos_left q hr
      omega
    simp only [hge, if_true]
    set φ := ‖(1:ℂ) - W N c r‖ ^ 2
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := wt_nonneg (r * q + i); positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hr' : (0:ℝ) < r := by exact_mod_cast hr
    have hq' : (0:ℝ) < q := by exact_mod_cast hq
    have hsum : ∑ i : Fin q, wt (r * q + (i : ℕ)) = 1 / ((r:ℝ) * q) - 1 / ((r:ℝ) * q + q) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => wt (r * q + i))]
      rw [← telescope ((r:ℝ) * q) (by positivity) q]
      apply Finset.sum_congr rfl; intro i _
      unfold wt; push_cast; ring_nf
    rw [hsum]
    unfold wt
    rw [show (1:ℝ) / ((r:ℝ) * q) - 1 / ((r:ℝ) * q + q) = 1 / ((r:ℝ) * (r + 1)) / q by
      field_simp; ring]
    rw [div_le_iff₀ hq']
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
    have : 0 ≤ 1 / ((r:ℝ) * (r + 1)) := by positivity
    nlinarith

lemma approx_delta (h1 : Approx (fun _ => 1)) (r : ℕ) :
    Approx (fun m => if m = r then 1 else 0) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    intro ε hε
    refine ⟨0, 0, ?_⟩
    have : Q (fun m => (if m = 0 then (1:ℂ) else 0) - W 0 0 m) = 0 := by
      unfold Q
      apply ENNReal.tsum_eq_zero.mpr
      intro m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp [wt]
      · simp [W, hm.ne']
    rw [this]; exact ENNReal.ofReal_pos.mpr hε
  · have ha := approx_add (approx_ge h1 r hr) (approx_ge h1 (r+1) (by omega)) (-1)
    apply approx_congr ha
    intro m
    split_ifs <;> first | (exfalso; omega) | simp

lemma approx_finite (h1 : Approx (fun _ => 1)) (F : ℕ → ℂ) (K : ℕ) :
    Approx (fun m => if m < K then F m else 0) := by
  induction K with
  | zero =>
    intro ε hε
    refine ⟨0, 0, ?_⟩
    have : Q (fun m => (if m < 0 then F m else 0) - W 0 0 m) = 0 := by
      unfold Q; apply ENNReal.tsum_eq_zero.mpr; intro m; simp [W]
    rw [this]; exact ENNReal.ofReal_pos.mpr hε
  | succ K ih =>
    have ha := approx_add ih (approx_delta h1 K) (F K)
    apply approx_congr ha
    intro m
    by_cases h : m < K
    · have : m ≠ K := by omega
      simp [h, this, show m < K + 1 by omega]
    · by_cases h' : m = K
      · subst h'; simp
      · simp [h, h', show ¬ m < K + 1 by omega]

lemma approx_all (h1 : Approx (fun _ => 1)) (F : ℕ → ℂ) (hF : Q F ≠ ∞) : Approx F := by
  intro ε hε
  -- tail
  have htail : Tendsto (fun K : ℕ => Q (fun m => F m - (if m < K then F m else 0))) atTop (𝓝 0) := by
    have hfin : ∑' m : ℕ, ENNReal.ofReal (‖F m‖ ^ 2 * wt m) ≠ ∞ := hF
    have := ENNReal.tendsto_tsum_compl_atTop_zero hfin
    have hmono : ∀ K : ℕ, Q (fun m => F m - (if m < K then F m else 0)) =
        ∑' (m : {x // x ∉ Finset.range K}), ENNReal.ofReal (‖F m‖ ^ 2 * wt m) := by
      intro K
      unfold Q
      rw [← tsum_subtype_eq_of_support_subset (s := {x | x ∉ Finset.range K})]
      · apply tsum_congr; intro m
        have : ¬ (m : ℕ) < K := by have := m.2; simpa using this
        simp [this]
      · intro m hm
        simp only [Function.mem_support] at hm
        simp only [Set.mem_setOf_eq, Finset.mem_range]
        intro hmK
        apply hm; simp [hmK]
    simp_rw [hmono]
    exact this.comp tendsto_finset_range
  have hev := (ENNReal.tendsto_nhds_zero.mp htail) (ENNReal.ofReal (ε / 8))
    (by simp; positivity)
  obtain ⟨K, hK⟩ := hev.exists_forall_of_atTop
  obtain ⟨N, c, hc⟩ := approx_finite h1 F K (ε / 8) (by positivity)
  refine ⟨N, c, ?_⟩
  have hle := Q_add_le (fun m => (if m < K then F m else 0) - W N c m)
    (fun m => F m - (if m < K then F m else 0))
  rw [Q_congr (v := fun m => ((if m < K then F m else 0) - W N c m) +
    (F m - (if m < K then F m else 0))) (fun m => by ring)]
  refine lt_of_le_of_lt hle ?_
  have e1 : 2 * Q (fun m => (if m < K then F m else 0) - W N c m) ≤ 2 * ENNReal.ofReal (ε / 8) := by
    gcongr
  have e2 : 2 * Q (fun m => F m - (if m < K then F m else 0)) ≤ 2 * ENNReal.ofReal (ε / 8) := by
    gcongr; exact hK K le_rfl
  refine lt_of_le_of_lt (add_le_add e1 e2) ?_
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_lt_ofReal_iff hε]
  linarith

/-- the final transfer from Bagchi's constant criterion to density. -/
theorem dense_of_bagchi
    (hb : let err (f : ℕ → ℂ) (N : ℕ) (a : Fin N → ℂ) (n : ℕ) :=
                ‖f n - ∑ j, a j * ((Int.fract ((n : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 /
                  ((n : ℝ)*(n+1))
              ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
                Summable (fun m : ℕ => err (fun _ => 1) N a (m+1)) ∧
                (∑' m : ℕ, err (fun _ => 1) N a (m+1)) < ε) :
    let w (n : ℕ) := ((n+1 : ℕ) : ℝ) * (n+2 : ℕ)
    ∀ f : ℕ → ℂ, Summable (fun n : ℕ => ‖f n‖^2 / w n) →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
        let g (n : ℕ) := ‖f n - ∑ j, a j *
          ((Int.fract (((n+1 : ℕ) : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 / w n
        Summable g ∧ (∑' n : ℕ, g n) < ε := by
  intro w f hf ε hε
  -- shift lemma for Q
  have hshift : ∀ u : ℕ → ℂ, Q u = ∑' n : ℕ, ENNReal.ofReal (‖u (n+1)‖ ^ 2 / (((n+1 : ℕ) : ℝ) * (n+2 : ℕ))) := by
    intro u
    unfold Q
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [wt, Nat.cast_zero, zero_mul, div_zero, mul_zero, ENNReal.ofReal_zero, zero_add]
    apply tsum_congr; intro n
    congr 1
    push_cast; ring
  have hconv : ∀ v : ℕ → ℝ, (∀ n, 0 ≤ v n) → ∀ B : ℝ, 0 < B →
      ∑' n : ℕ, ENNReal.ofReal (v n) < ENNReal.ofReal B → Summable v ∧ ∑' n, v n < B := by
    intro v hv B hB h
    have hfin : ∑' n : ℕ, ENNReal.ofReal (v n) ≠ ∞ := ne_top_of_lt h
    have hs : Summable v := by
      have := ENNReal.summable_toReal hfin
      simpa [ENNReal.toReal_ofReal (hv _)] using this
    refine ⟨hs, ?_⟩
    rw [← ENNReal.ofReal_tsum_of_nonneg hv hs] at h
    exact (ENNReal.ofReal_lt_ofReal_iff hB).mp h
  -- Approx 1 from Bagchi
  have h1 : Approx (fun _ => 1) := by
    intro δ hδ
    obtain ⟨N, a, hs, hlt⟩ := hb δ hδ
    refine ⟨N, fun j => if h : j < N then a ⟨j, h⟩ else 0, ?_⟩
    rw [hshift]
    have hW : ∀ n : ℕ, W N (fun j => if h : j < N then a ⟨j, h⟩ else 0) (n+1) =
        ∑ j : Fin N, a j * ((Int.fract (((n+1 : ℕ) : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ) := by
      intro n
      unfold W
      rw [← Fin.sum_univ_eq_sum_range (fun j => (if h : j < N then a ⟨j, h⟩ else 0) *
        ((Int.fract (((n+1 : ℕ) : ℝ) / ((j+1 : ℕ) : ℝ)) : ℝ) : ℂ))]
      apply Finset.sum_congr rfl; intro j _
      rw [dif_pos j.isLt]
    simp_rw [hW]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)]
    · rw [ENNReal.ofReal_lt_ofReal_iff hδ]
      convert hlt using 2
      funext n; dsimp only; congr 1; push_cast; ring
    · convert hs using 1
      funext n; dsimp only; congr 1; push_cast; ring
  -- F from f
  set F : ℕ → ℂ := fun m => if m = 0 then 0 else f (m - 1) with hFdef
  have hQF : Q F ≠ ∞ := by
    rw [hshift]
    simp only [hFdef, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hf]
    exact ENNReal.ofReal_ne_top
  obtain ⟨N, c, hc⟩ := approx_all h1 F hQF ε hε
  refine ⟨N, fun j => c j.val, ?_⟩
  rw [hshift] at hc
  apply hconv _ (fun n => by positivity) ε hε
  convert hc using 3 with n
  simp only [hFdef, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, W]
  congr 3
  rw [Fin.sum_univ_eq_sum_range (fun j => c j * ((Int.fract (((n+1 : ℕ) : ℝ) / ((j+1 : ℕ) : ℝ)) : ℝ) : ℂ))]

end NymanDense

theorem solution :
    let w (n : ℕ) := ((n+1 : ℕ) : ℝ) * (n+2 : ℕ)
    ∀ f : ℕ → ℂ, Summable (fun n : ℕ => ‖f n‖^2 / w n) →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
        let g (n : ℕ) := ‖f n - ∑ j, a j *
          ((Int.fract (((n+1 : ℕ) : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 / w n
        Summable g ∧ (∑' n : ℕ, g n) < ε :=
  NymanDense.dense_of_bagchi (bagchiConst_of_bounds
    (NymanAux.moebiusPolynomialBoundaryBound_of_riemannHypothesis riemann_hypothesis)
    (NymanAux.shiftedZetaRatioBound_of_riemannHypothesis riemann_hypothesis))
