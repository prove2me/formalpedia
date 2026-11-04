-- Prove2me | solution 1 for BlindProphetSec.Blind.corollary_4_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:12:38.706041+00:00
-- url     : https://prove2.me/submissions/0eecef1e-0c0b-49a9-afb7-55de38a0f758
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting
import Theorems.Thm_BlindProphetSec_Blind_lemma_4_3

open MeasureTheory

namespace BPSCor44

open BlindProphetSec.Blind

/-- Rational upper bound for `-log (1 - x)` (truncated Taylor series plus tail). -/
def UQ (x : ℚ) : ℚ := x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 + x ^ 6 / (1 - x)

/-- `∏_{l ∈ [1, k)} r_l`. -/
def PQ (r : ℕ → ℚ) (k : ℕ) : ℚ := ∏ l ∈ Finset.Ico 1 k, r l

/-- Rational lower bound of the `k`-th summand `(∏_{l<k} α_l)^{1/m} (1 - α_k^{1/m}) / (-ln α_k)`. -/
def hq (m : ℕ) (r : ℕ → ℚ) (k : ℕ) : ℚ := PQ r k * (1 - r k) / (m * UQ (1 - r k))

/-- `g_{m, α_1}` with `α_1 = r_1 ^ m`, in `ℚ`. -/
def gQ (m : ℕ) (r : ℕ → ℚ) (k : ℕ) : ℚ :=
  if (k : ℚ) ≤ (m : ℚ) / 2 then 1 / (1 - (k : ℚ) / m * (1 - r 1 ^ m)) else 2 / (1 + r 1 ^ m)

/-- Rational lower bound of `f_j(α_1,…,α_m)` with `α_k = r_k ^ m`. -/
def FQ (m : ℕ) (r : ℕ → ℚ) (j : ℕ) : ℚ :=
  if j = 1 then ∑ k ∈ Finset.Icc 1 m, hq m r k
  else if j ≤ m then
    ∑ k ∈ Finset.Ico 1 j, (1 - r k ^ m) / (m * (1 - r j ^ m)) +
      ∑ k ∈ Finset.Icc j m, hq m r k * gQ m r (k - 1)
  else (1 / (m : ℚ)) * ∑ k ∈ Finset.Icc 1 m, (1 - r k ^ m)

lemma neg_log_le_UQ (r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    -Real.log (r : ℝ) ≤ ((UQ (1 - r) : ℚ) : ℝ) := by
  have h0' : (0 : ℝ) < r := by exact_mod_cast h0
  have h1' : (r : ℝ) < 1 := by exact_mod_cast h1
  have hx : |(1 - (r : ℝ))| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have H := Real.abs_log_sub_add_sum_range_le hx 5
  have habs : |(1 - (r : ℝ))| = 1 - r := abs_of_pos (by linarith)
  rw [habs] at H
  have e : (1 : ℝ) - (1 - r) = r := by ring
  rw [e] at H
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at H
  have H2 := (abs_le.mp H).1
  unfold UQ
  push_cast
  norm_num at H2 ⊢
  linarith

lemma term_ge (m : ℕ) (hm : m ≠ 0) (r : ℕ → ℚ) (hr : ∀ l ∈ Finset.Icc 1 m, 0 < r l ∧ r l < 1)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 m) :
    ((hq m r k : ℚ) : ℝ) ≤ (∏ l ∈ Finset.Ico 1 k, ((r l : ℝ)) ^ m) ^ ((1 : ℝ) / m) *
      ((1 - (((r k : ℝ)) ^ m) ^ ((1 : ℝ) / m)) / (-Real.log (((r k : ℝ)) ^ m))) := by
  have hk' := Finset.mem_Icc.mp hk
  have hprod : 0 ≤ ∏ l ∈ Finset.Ico 1 k, (r l : ℝ) := by
    apply Finset.prod_nonneg
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have := (hr l (Finset.mem_Icc.mpr ⟨hl'.1, by omega⟩)).1
    exact_mod_cast this.le
  obtain ⟨hr0, hr1⟩ := hr k hk
  have hr0' : (0 : ℝ) < r k := by exact_mod_cast hr0
  have hr1' : (r k : ℝ) < 1 := by exact_mod_cast hr1
  rw [Finset.prod_pow, one_div, Real.pow_rpow_inv_natCast hprod hm,
    Real.pow_rpow_inv_natCast hr0'.le hm, Real.log_pow]
  have hlog : Real.log (r k : ℝ) < 0 := Real.log_neg hr0' hr1'
  have hU := neg_log_le_UQ (r k) hr0 hr1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  unfold hq PQ
  push_cast
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hprod
  have e : -((m : ℝ) * Real.log (r k)) = (m : ℝ) * (-Real.log (r k)) := by ring
  rw [e]
  apply div_le_div_of_nonneg_left (by linarith)
  · exact mul_pos hmpos (by linarith)
  · apply mul_le_mul_of_nonneg_left _ hmpos.le
    exact hU

lemma gQ_cast (m : ℕ) (r : ℕ → ℚ) (k : ℕ) :
    ((gQ m r k : ℚ) : ℝ) = gFun m (((r 1 : ℚ) : ℝ) ^ m) k := by
  unfold gQ gFun
  split_ifs with h1 h2 h2
  · push_cast; rfl
  · exfalso; apply h2
    have : ((k : ℚ) : ℝ) ≤ (((m : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h1
    push_cast at this; exact this
  · exfalso; apply h1
    have : (((k : ℚ) : ℝ)) ≤ (((m : ℚ) / 2 : ℚ) : ℝ) := by push_cast; exact h2
    exact Rat.cast_le.mp this
  · push_cast; rfl

lemma FQ_le_fFun (m : ℕ) (hm : 1 ≤ m) (r : ℕ → ℚ) (hr : ∀ l ∈ Finset.Icc 1 m, 0 < r l ∧ r l < 1)
    (hg : ∀ k ∈ Finset.range m, 0 ≤ gQ m r k) (j : ℕ) (hj : j ∈ Finset.Icc 1 (m + 1)) :
    ((FQ m r j : ℚ) : ℝ) ≤ fFun m (fun k => ((r k : ℚ) : ℝ) ^ m) j := by
  have hj' := Finset.mem_Icc.mp hj
  have hm0 : m ≠ 0 := by omega
  unfold FQ fFun
  split_ifs with h1 h2
  · rw [Rat.cast_sum]
    apply Finset.sum_le_sum
    intro k hk
    exact term_ge m hm0 r hr k hk
  · rw [Rat.cast_add, Rat.cast_sum, Rat.cast_sum]
    apply add_le_add
    · apply le_of_eq
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    · apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      rw [Rat.cast_mul, gQ_cast]
      beta_reduce
      have T := term_ge m hm0 r hr k (Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩)
      have G : (0 : ℝ) ≤ gFun m (((r 1 : ℚ) : ℝ) ^ m) (k - 1) := by
        rw [← gQ_cast]
        exact_mod_cast hg (k - 1) (Finset.mem_range.mpr (by omega))
      calc _ ≤ _ := mul_le_mul_of_nonneg_right T G
        _ = _ := by ring
  · apply le_of_eq
    push_cast
    ring

def rL : List ℚ := [247/250, 9879/10000, 2469/2500, 9873/10000, 2467/2500, 9863/10000, 616/625, 1231/1250, 4919/5000, 2457/2500, 9817/10000, 2451/2500, 612/625, 4889/5000, 2441/2500, 9751/10000, 9737/10000, 389/400, 1943/2000, 2427/2500, 4851/5000, 606/625, 1211/1250, 121/125, 1209/1250, 4831/5000, 9651/10000, 4819/5000, 77/80, 9609/10000, 1199/1250, 2393/2500, 191/200, 2381/2500, 9493/10000, 591/625, 9409/10000, 2337/2500, 463/500, 2277/2500]

def r40 (k : ℕ) : ℚ := rL.getD (k - 1) 0

set_option maxRecDepth 100000 in
theorem check :
    (∀ j ∈ Finset.Icc 1 41, (66975 / 100000 : ℚ) ≤ FQ 40 r40 j) ∧
    (∀ k ∈ Finset.Icc 1 40, 0 < r40 k ∧ r40 k < 1) ∧
    (∀ k ∈ Finset.range 40, 0 ≤ gQ 40 r40 k) ∧
    (∀ k ∈ Finset.Ico 1 40, r40 (k + 1) ≤ r40 k) := by
  decide +kernel

lemma r40_anti (h : ∀ k ∈ Finset.Ico 1 40, r40 (k + 1) ≤ r40 k) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i ≤ j) (hj : j ≤ 40) : r40 j ≤ r40 i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact le_trans (h j (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)) (ih (by omega))

end BPSCor44

open BlindProphetSec.Blind BPSCor44 in
theorem solution :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ a : ℕ → ℝ, a 1 ≤ 1 ∧ AntitoneOn a (Set.Icc 1 m) ∧ 0 ≤ a m ∧
      ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)],
        (∀ i, μ i (Set.Iio 0) = 0) →
        ENNReal.ofReal (66975 / 100000) * Emax μ ≤ blindValue (pieceAlpha m a) μ := by
  obtain ⟨hF, hr, hg, hanti⟩ := check
  have hr1 := hr 1 (by decide)
  have hr40 := hr 40 (by decide)
  have hpos : ∀ k ∈ Finset.Icc 1 40, (0 : ℝ) < ((r40 k : ℚ) : ℝ) := fun k hk => by
    exact_mod_cast (hr k hk).1
  have hA : AntitoneOn (fun k => ((r40 k : ℚ) : ℝ) ^ 40) (Set.Icc 1 40) := by
    intro i hi j hj hij
    have hi' := hi; have hj' := hj
    simp only [Set.mem_Icc] at hi' hj'
    have hle : r40 j ≤ r40 i := r40_anti hanti i j hi'.1 hij hj'.2
    have hj0 : (0 : ℝ) ≤ ((r40 j : ℚ) : ℝ) := (hpos j (Finset.mem_Icc.mpr hj')).le
    exact pow_le_pow_left₀ hj0 (by exact_mod_cast hle) 40
  have ha1 : ((r40 1 : ℚ) : ℝ) ^ 40 < 1 := by
    apply pow_lt_one₀ (by exact_mod_cast hr1.1.le) (by exact_mod_cast hr1.2) (by norm_num)
  have ham : (0 : ℝ) < ((r40 40 : ℚ) : ℝ) ^ 40 := pow_pos (by exact_mod_cast hr40.1) 40
  refine ⟨40, by norm_num, fun k => ((r40 k : ℚ) : ℝ) ^ 40, ha1.le, hA, ham.le, ?_⟩
  intro n μ _ _ hnn
  have H := lemma_4_3 40 (by norm_num) (fun k => ((r40 k : ℚ) : ℝ) ^ 40) hA ham ha1 μ hnn
  refine le_trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) H
  apply Finset.le_inf'
  intro j hj
  have h1 : ((66975 / 100000 : ℚ) : ℝ) ≤ ((FQ 40 r40 j : ℚ) : ℝ) := by exact_mod_cast hF j hj
  have h2 := FQ_le_fFun 40 (by norm_num) r40 hr hg j hj
  push_cast at h1
  linarith
