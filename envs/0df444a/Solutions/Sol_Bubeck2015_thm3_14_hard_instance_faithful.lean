-- Prove2me | solution 1 for Bubeck2015.thm3_14_hard_instance_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:16:09.104844+00:00
-- url     : https://prove2.me/submissions/b5d639fc-f1a9-47e9-b6d5-36d3e3f3fde5

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

namespace BU86N

def rowF (k : ℕ) (y : ℕ → ℝ) (a : ℕ) : ℝ :=
  if a < k then 2 * y a - (if 1 ≤ a then y (a - 1) else 0) - (if a + 1 < k then y (a + 1) else 0) else 0

/-- bilinear form `uᵀ A_k v`. -/
def bf (k : ℕ) (u v : ℕ → ℝ) : ℝ := ∑ a ∈ Finset.range k, u a * rowF k v a

lemma bf_eq (m : ℕ) (u v : ℕ → ℝ) : bf (m + 1) u v =
    2 * ∑ a ∈ Finset.range (m + 1), u a * v a
      - ∑ a ∈ Finset.range m, (u (a + 1) * v a + u a * v (a + 1)) := by
  unfold bf
  have h : ∀ a ∈ Finset.range (m + 1), u a * rowF (m + 1) v a =
      2 * (u a * v a) - u a * (if 1 ≤ a then v (a - 1) else 0) - u a * (if a + 1 < m + 1 then v (a + 1) else 0) := by
    intro a ha
    rw [Finset.mem_range] at ha
    simp only [rowF, ha, if_true]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_range_succ' (fun a => u a * (if 1 ≤ a then v (a - 1) else 0)),
    Finset.sum_range_succ (fun a => u a * (if a + 1 < m + 1 then v (a + 1) else 0)), Finset.sum_add_distrib]
  have h1 : ∀ a ∈ Finset.range m, u (a + 1) * (if 1 ≤ a + 1 then v (a + 1 - 1) else 0) = u (a + 1) * v a := by
    intro a _; simp
  have h2 : ∀ a ∈ Finset.range m, u a * (if a + 1 < m + 1 then v (a + 1) else 0) = u a * v (a + 1) := by
    intro a ha; rw [Finset.mem_range] at ha; simp [ha]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  simp; ring

lemma bf_zero (u v : ℕ → ℝ) : bf 0 u v = 0 := by simp [bf]

lemma bf_symm (k : ℕ) (u v : ℕ → ℝ) : bf k u v = bf k v u := by
  rcases k with _ | m
  · simp [bf_zero]
  · rw [bf_eq, bf_eq]
    congr 1
    · congr 1; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    · exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma bf_add_left (k : ℕ) (u u' v : ℕ → ℝ) : bf k (u + u') v = bf k u v + bf k u' v := by
  simp [bf, add_mul, Finset.sum_add_distrib]

lemma bf_smul_left (k : ℕ) (c : ℝ) (u v : ℕ → ℝ) : bf k (c • u) v = c * bf k u v := by
  simp [bf, Finset.mul_sum, mul_assoc]

lemma bf_sub_left (k : ℕ) (u u' v : ℕ → ℝ) : bf k (u - u') v = bf k u v - bf k u' v := by
  simp [bf, sub_mul, Finset.sum_sub_distrib]

lemma bf_add_right (k : ℕ) (u v v' : ℕ → ℝ) : bf k u (v + v') = bf k u v + bf k u v' := by
  rw [bf_symm, bf_add_left, bf_symm k v, bf_symm k v']

lemma bf_smul_right (k : ℕ) (c : ℝ) (u v : ℕ → ℝ) : bf k u (c • v) = c * bf k u v := by
  rw [bf_symm, bf_smul_left, bf_symm]

lemma bf_sub_right (k : ℕ) (u v v' : ℕ → ℝ) : bf k u (v - v') = bf k u v - bf k u v' := by
  rw [bf_symm, bf_sub_left, bf_symm k v, bf_symm k v']

/-- Sum of squares form. -/
lemma bf_sos (m : ℕ) (y : ℕ → ℝ) : bf (m + 1) y y =
    y 0 ^ 2 + y m ^ 2 + ∑ a ∈ Finset.range m, (y a - y (a + 1)) ^ 2 := by
  rw [bf_eq]
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun a => (y a - y (a + 1)) ^ 2),
      Finset.sum_range_succ (fun a => y (a + 1) * y a + y a * y (a + 1))]
    have := ih
    nlinarith [this]

lemma bf_nonneg (k : ℕ) (y : ℕ → ℝ) : 0 ≤ bf k y y := by
  rcases k with _ | m
  · simp [bf_zero]
  · rw [bf_sos]; positivity

/-- The minimizer. -/
noncomputable def ystar (k : ℕ) (a : ℕ) : ℝ := if a < k then 1 - ((a : ℝ) + 1) / ((k : ℝ) + 1) else 0

lemma row_ystar {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (ha : a < k) :
    rowF k (ystar k) a = if a = 0 then 1 else 0 := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  unfold rowF ystar
  simp only [ha, if_true]
  by_cases h0 : a = 0
  · subst h0
    by_cases h1 : 1 < k
    · simp [h1]; field_simp; ring
    · have : k = 1 := by omega
      subst this; norm_num
  · have h1 : 1 ≤ a := by omega
    have h2 : a - 1 < k := by omega
    simp only [h0, h1, h2, if_true, if_false]
    have hc : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub h1]; simp
    by_cases h3 : a + 1 < k
    · simp only [h3, if_true]; push_cast; rw [hc]; field_simp; ring
    · have : a + 1 = k := by omega
      simp only [h3, if_false]
      rw [hc, ← this]; push_cast; field_simp; ring

lemma bf_ystar_right {k : ℕ} (hk : 1 ≤ k) (u : ℕ → ℝ) : bf k u (ystar k) = u 0 := by
  unfold bf
  rw [Finset.sum_congr rfl (fun a ha => by rw [row_ystar hk a (Finset.mem_range.mp ha)])]
  simp [mul_ite, Finset.sum_ite_eq', Finset.mem_range]; omega

/-- Minimum value of `bf k y y - 2 y 0`. -/
lemma min_val {k : ℕ} (hk : 1 ≤ k) (y : ℕ → ℝ) :
    -(1 - 1 / ((k : ℝ) + 1)) ≤ bf k y y - 2 * y 0 := by
  set d := y - ystar k
  have hy : y = ystar k + d := by simp [d]
  have e : bf k y y = bf k (ystar k) (ystar k) + 2 * bf k d (ystar k) + bf k d d := by
    rw [hy, bf_add_left, bf_add_right, bf_add_right, bf_symm k (ystar k) d]; ring
  rw [e, bf_ystar_right hk, bf_ystar_right hk, hy]
  have := bf_nonneg k d
  have h0 : ystar k 0 = 1 - 1 / ((k : ℝ) + 1) := by simp [ystar, show 0 < k by omega]
  simp only [Pi.add_apply]
  rw [h0]; linarith

/-- Restriction to a smaller block. -/
lemma bf_restrict {m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (y : ℕ → ℝ) (hy : ∀ a, m ≤ a → y a = 0) :
    bf k y y = bf m y y := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [bf_eq, bf_eq]
  have h1 : ∑ a ∈ Finset.range (k' + 1), y a * y a = ∑ a ∈ Finset.range (m' + 1), y a * y a := by
    symm; apply Finset.sum_subset (Finset.range_subset_range.mpr hmk)
    intro a ha hna; simp at ha hna; simp [hy a (by omega)]
  have h2 : ∑ a ∈ Finset.range k', (y (a + 1) * y a + y a * y (a + 1)) =
      ∑ a ∈ Finset.range m', (y (a + 1) * y a + y a * y (a + 1)) := by
    symm; apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro a ha hna; simp at ha hna; simp [hy (a + 1) (by omega)]
  rw [h1, h2]

/-- Support propagation. -/
lemma row_supp {k m : ℕ} (y : ℕ → ℝ) (hy : ∀ a, m ≤ a → y a = 0) (a : ℕ) (ha : m + 1 ≤ a) :
    rowF k y a = 0 := by
  unfold rowF
  have h1 : 1 ≤ a := by omega
  simp only [h1, if_true, hy a (by omega), hy (a - 1) (by omega), hy (a + 1) (by omega)]
  split_ifs <;> ring

/-- Row bound: `‖A_k y‖² ≤ 16 ‖y‖²` on the block. -/
lemma row_bound (k : ℕ) (y : ℕ → ℝ) :
    ∑ a ∈ Finset.range k, (rowF k y a) ^ 2 ≤ 16 * ∑ a ∈ Finset.range k, y a ^ 2 := by
  have hpt : ∀ a ∈ Finset.range k, (rowF k y a) ^ 2 ≤
      8 * y a ^ 2 + 4 * (if 1 ≤ a then y (a - 1) ^ 2 else 0) + 4 * (if a + 1 < k then y (a + 1) ^ 2 else 0) := by
    intro a ha
    rw [Finset.mem_range] at ha
    unfold rowF
    simp only [ha, if_true]
    split_ifs <;> nlinarith [sq_nonneg (y a - y (a - 1)), sq_nonneg (y a - y (a + 1)),
      sq_nonneg (y (a - 1) - y (a + 1)), sq_nonneg (y a + y (a - 1)), sq_nonneg (y a + y (a + 1))]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hA : ∑ a ∈ Finset.range k, (if 1 ≤ a then y (a - 1) ^ 2 else 0) ≤ ∑ a ∈ Finset.range k, y a ^ 2 := by
    rcases k with _ | m
    · simp
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [le_add_iff_nonneg_left, Nat.add_sub_cancel, if_true, show ¬ (1 ≤ 0) by omega, if_false, add_zero]
    simp only [zero_le, if_true]
    linarith [sq_nonneg (y m)]
  have hB : ∑ a ∈ Finset.range k, (if a + 1 < k then y (a + 1) ^ 2 else 0) ≤ ∑ a ∈ Finset.range k, y a ^ 2 := by
    rcases k with _ | m
    · simp
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [lt_irrefl, if_false, add_zero]
    have : ∀ a ∈ Finset.range m, (if a + 1 < m + 1 then y (a + 1) ^ 2 else 0) = y (a + 1) ^ 2 := by
      intro a ha; rw [Finset.mem_range] at ha; simp [ha]
    rw [Finset.sum_congr rfl this]; linarith [sq_nonneg (y 0)]
  linarith

end BU86N


open scoped InnerProductSpace
open ConvexOptAlg.LowerBounds Matrix

namespace BU86

/-- ℕ-indexed extension by zero. -/
def ex {n : ℕ} (v : Fin n → ℝ) (a : ℕ) : ℝ := if h : a < n then v ⟨a, h⟩ else 0

lemma ex_fin {n : ℕ} (v : Fin n → ℝ) (a : Fin n) : ex v a = v a := by
  simp [ex, a.isLt]

lemma ex_ge {n : ℕ} (v : Fin n → ℝ) {a : ℕ} (h : n ≤ a) : ex v a = 0 := by
  simp [ex, not_lt.mpr h]

lemma sum_fin {n : ℕ} (F : ℕ → ℝ) : ∑ a : Fin n, F a = ∑ a ∈ Finset.range n, F a :=
  Fin.sum_univ_eq_sum_range F n

lemma row {n k : ℕ} (hk : k ≤ n) (v : Fin n → ℝ) (a : Fin n) :
    (tridiag n k *ᵥ v) a = BU86N.rowF k (ex v) a := by
  simp only [Matrix.mulVec, dotProduct, tridiag, Matrix.of_apply]
  let G : ℕ → ℝ := fun c => (if c = (a : ℕ) then (if (a : ℕ) < k then 2 * ex v a else 0) else 0)
        + (if 1 ≤ (a : ℕ) ∧ c = (a : ℕ) - 1 then (if (a : ℕ) < k then -ex v ((a : ℕ) - 1) else 0) else 0)
        + (if c = (a : ℕ) + 1 then (if (a : ℕ) + 1 < k then -ex v ((a : ℕ) + 1) else 0) else 0)
  have hF : ∀ b : Fin n, (if (a : ℕ) = b ∧ (a : ℕ) < k then (2 : ℝ)
      else if ((b : ℕ) + 1 = a ∨ (b : ℕ) = (a : ℕ) + 1) ∧ (a : ℕ) < k ∧ (b : ℕ) ≠ k then -1 else 0) * v b =
      G b := by
    intro b
    have hb := b.isLt
    simp only [G]
    rw [← ex_fin v b]
    by_cases h1 : (b : ℕ) = a
    · rw [h1]; split_ifs <;> first | (exfalso; omega) | ring1 | simp
    by_cases h2 : 1 ≤ (a : ℕ) ∧ (b : ℕ) = (a : ℕ) - 1
    · rw [h2.2]; split_ifs <;> first | (exfalso; omega) | ring1 | simp
    by_cases h3 : (b : ℕ) = (a : ℕ) + 1
    · rw [h3]; split_ifs <;> first | (exfalso; omega) | ring1 | simp
    · split_ifs <;> first | (exfalso; omega) | ring1 | simp
  rw [Finset.sum_congr rfl (fun b _ => hF b), Fin.sum_univ_eq_sum_range G n]
  simp only [G]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [ite_and]
  rw [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have ha := a.isLt
  simp only [Finset.mem_range, ha, if_true, Finset.sum_const_zero]
  unfold BU86N.rowF
  by_cases hak : (a : ℕ) < k
  · by_cases h1 : 1 ≤ (a : ℕ)
    · have : (a : ℕ) - 1 < n := by omega
      by_cases h2 : (a : ℕ) + 1 < k
      · have : (a : ℕ) + 1 < n := by omega
        simp [hak, h1, h2, *] <;> ring1
      · simp [hak, h1, h2, *] <;> ring1
    · by_cases h2 : (a : ℕ) + 1 < k
      · have : (a : ℕ) + 1 < n := by omega
        simp [hak, h1, h2, *] <;> ring1
      · simp [hak, h1, h2, *] <;> ring1
  · have : ¬ ((a : ℕ) + 1 < k) := by omega
    simp [hak, this]

end BU86

namespace BU86

open BU86N

/-- coordinates of a Euclidean vector as an ℕ-indexed sequence -/
noncomputable def Y {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℕ → ℝ := ex x.ofLp

lemma Y_add {n : ℕ} (u w : EuclideanSpace ℝ (Fin n)) : Y (u + w) = Y u + Y w := by
  funext a; simp only [Y, ex, Pi.add_apply, WithLp.ofLp_add]; split_ifs <;> simp

lemma Y_sub {n : ℕ} (u w : EuclideanSpace ℝ (Fin n)) : Y (u - w) = Y u - Y w := by
  funext a; simp only [Y, ex, Pi.sub_apply, WithLp.ofLp_sub]; split_ifs <;> simp

lemma Y_smul {n : ℕ} (c : ℝ) (u : EuclideanSpace ℝ (Fin n)) : Y (c • u) = c • Y u := by
  funext a; simp only [Y, ex, Pi.smul_apply, WithLp.ofLp_smul, smul_eq_mul]; split_ifs <;> simp

lemma Y_zero {n : ℕ} : Y (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  funext a; simp [Y, ex]

lemma inner_Y {n : ℕ} (u w : EuclideanSpace ℝ (Fin n)) :
    ⟪u, w⟫_ℝ = ∑ a ∈ Finset.range n, Y u a * Y w a := by
  have : ⟪u, w⟫_ℝ = ∑ i : Fin n, u.ofLp i * w.ofLp i := by simp [PiLp.inner_apply, mul_comm]
  rw [this, ← Fin.sum_univ_eq_sum_range (fun a => Y u a * Y w a) n]
  simp [Y, ex_fin]

lemma normsq_Y {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    ‖u‖ ^ 2 = ∑ a ∈ Finset.range n, Y u a ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_Y]; simp [sq]

lemma Y_ge {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) {a : ℕ} (h : n ≤ a) : Y u a = 0 := ex_ge _ h

lemma sumk_le {n k : ℕ} (hk : k ≤ n) (u : EuclideanSpace ℝ (Fin n)) :
    ∑ a ∈ Finset.range k, Y u a ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [normsq_Y]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hk) (fun _ _ _ => sq_nonneg _)

lemma rowF_zero_ge {k : ℕ} (y : ℕ → ℝ) {a : ℕ} (h : k ≤ a) : rowF k y a = 0 := by
  simp [rowF, not_lt.mpr h]

lemma rowF_sub (k : ℕ) (u w : ℕ → ℝ) (a : ℕ) : rowF k (u - w) a = rowF k u a - rowF k w a := by
  simp only [rowF, Pi.sub_apply]; split_ifs <;> ring

lemma quad_eq {n k : ℕ} (hk : k ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    quadForm (tridiag n k) x = bf k (Y x) (Y x) := by
  unfold quadForm bf
  simp only [dotProduct]
  rw [Finset.sum_congr rfl (fun a _ => by rw [row hk])]
  calc ∑ a : Fin n, x.ofLp a * rowF k (ex x.ofLp) ↑a
      = ∑ a : Fin n, (fun c : ℕ => Y x c * rowF k (Y x) c) a := by simp [Y, ex_fin]
    _ = ∑ a ∈ Finset.range n, Y x a * rowF k (Y x) a :=
      Fin.sum_univ_eq_sum_range (fun c : ℕ => Y x c * rowF k (Y x) c) n
    _ = ∑ a ∈ Finset.range k, Y x a * rowF k (Y x) a := by
      symm; apply Finset.sum_subset (Finset.range_subset_range.mpr hk)
      intro a _ ha; rw [rowF_zero_ge _ (by simpa using ha), mul_zero]

lemma inner_e1 {n : ℕ} (hn : 1 ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, basisVec n 1⟫_ℝ = Y x 0 := by
  rw [inner_Y]
  have : ∀ a ∈ Finset.range n, Y x a * Y (basisVec n 1) a = if a = 0 then Y x 0 else 0 := by
    intro a ha
    rw [Finset.mem_range] at ha
    simp only [Y, ex, ha, dif_pos, basisVec]
    by_cases h : a = 0 <;> (try simp [h]) <;> (try (intro h'; omega))
  rw [Finset.sum_congr rfl this]; simp; omega

lemma f_eq {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fK n β k x = β / 8 * bf k (Y x) (Y x) - β / 4 * Y x 0 := by
  rw [fK, quad_eq hk, inner_e1 hn]

/-- the gradient -/
noncomputable def grad (n k : ℕ) (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun a : Fin n => β / 4 * (rowF k (Y x) a - if (a : ℕ) = 0 then 1 else 0))

lemma Y_grad {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) (a : ℕ) :
    Y (grad n k β x) a = β / 4 * (rowF k (Y x) a - if a = 0 then 1 else 0) := by
  by_cases ha : a < n
  · simp [Y, ex, ha, grad]
  · rw [Y_ge _ (not_lt.mp ha), rowF_zero_ge _ (by omega)]
    have : a ≠ 0 := by omega
    simp [this]

lemma inner_grad {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) (β : ℝ) (x h : EuclideanSpace ℝ (Fin n)) :
    ⟪grad n k β x, h⟫_ℝ = β / 4 * (bf k (Y h) (Y x) - Y h 0) := by
  rw [inner_Y]
  simp only [Y_grad hn hk]
  have e1 : ∑ a ∈ Finset.range n, β / 4 * (rowF k (Y x) a - if a = 0 then 1 else 0) * Y h a =
      β / 4 * (∑ a ∈ Finset.range n, Y h a * rowF k (Y x) a - ∑ a ∈ Finset.range n, if a = 0 then Y h 0 else 0) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    split_ifs with h0
    · subst h0; ring
    · ring
  rw [e1]
  congr 2
  · unfold bf
    symm; apply Finset.sum_subset (Finset.range_subset_range.mpr hk)
    intro a _ ha; rw [rowF_zero_ge _ (by simpa using ha), mul_zero]
  · simp; omega

lemma bf_le {n k : ℕ} (hk : k ≤ n) (h : EuclideanSpace ℝ (Fin n)) :
    bf k (Y h) (Y h) ≤ 4 * ‖h‖ ^ 2 := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (Y h) (rowF k (Y h))
  have rb := row_bound k (Y h)
  have hs := sumk_le hk h
  have h0 : 0 ≤ ∑ a ∈ Finset.range k, Y h a ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : bf k (Y h) (Y h) ^ 2 ≤ (4 * ‖h‖ ^ 2) ^ 2 := by
    unfold bf
    calc _ ≤ _ := cs
      _ ≤ (∑ a ∈ Finset.range k, Y h a ^ 2) * (16 * ∑ a ∈ Finset.range k, Y h a ^ 2) :=
          mul_le_mul_of_nonneg_left rb h0
      _ = 16 * (∑ a ∈ Finset.range k, Y h a ^ 2) ^ 2 := by ring
      _ ≤ 16 * (‖h‖ ^ 2) ^ 2 := by gcongr
      _ = (4 * ‖h‖ ^ 2) ^ 2 := by ring
  exact (sq_le_sq₀ (bf_nonneg k _) (by positivity)).mp hb |>.trans' le_rfl

lemma hasGrad {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) {β : ℝ} (hβ : 0 < β) (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (fK n β k) (grad n k β x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have key : ∀ h, fK n β k (x + h) - fK n β k x - (InnerProductSpace.toDual ℝ _ (grad n k β x)) h =
      β / 8 * bf k (Y h) (Y h) := by
    intro h
    rw [InnerProductSpace.toDual_apply_apply, inner_grad hn hk, f_eq hn hk, f_eq hn hk, Y_add,
      bf_add_left, bf_add_right, bf_add_right, bf_symm k (Y x) (Y h)]
    simp only [Pi.add_apply]; ring
  simp_rw [key]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * c / β) ∈ nhds 0 :=
    Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  have h1 := bf_le hk h
  have h2 := bf_nonneg k (Y h)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : β / 8 * bf k (Y h) (Y h) ≤ β / 2 * ‖h‖ * ‖h‖ := by nlinarith
  have h3 : β / 2 * ‖h‖ ≤ c := by
    have := mul_lt_mul_of_pos_left hh (by positivity : (0:ℝ) < β / 2)
    rw [show β / 2 * (2 * c / β) = c by field_simp] at this; linarith
  nlinarith [norm_nonneg h]

lemma smooth {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) {β : ℝ} (hβ : 0 < β) :
    IsBetaSmooth (grad n k β) β := by
  intro x z
  have hY : ∀ a, Y (grad n k β x - grad n k β z) a = β / 4 * rowF k (Y (x - z)) a := by
    intro a
    rw [Y_sub, Pi.sub_apply, Y_grad hn hk, Y_grad hn hk, Y_sub, rowF_sub]; ring
  have hsq : ‖grad n k β x - grad n k β z‖ ^ 2 ≤ (β * ‖x - z‖) ^ 2 := by
    rw [normsq_Y]
    simp only [hY]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hk)
      (fun a _ ha => by rw [rowF_zero_ge _ (by simpa using ha)]; ring)]
    have rb := row_bound k (Y (x - z))
    have hs := sumk_le hk (x - z)
    calc ∑ a ∈ Finset.range k, (β / 4 * rowF k (Y (x - z)) a) ^ 2
        = (β / 4) ^ 2 * ∑ a ∈ Finset.range k, rowF k (Y (x - z)) a ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ (β / 4) ^ 2 * (16 * ‖x - z‖ ^ 2) := by gcongr; linarith
      _ = (β * ‖x - z‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

lemma convex {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) {β : ℝ} (hβ : 0 < β) :
    ConvexOn ℝ Set.univ (fK n β k) := by
  refine ⟨convex_univ, fun x _ z _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [f_eq hn hk, f_eq hn hk, f_eq hn hk, Y_add, Y_smul, Y_smul]
  set X := Y x
  set Z := Y z
  have e : bf k (a • X + b • Z) (a • X + b • Z) =
      a ^ 2 * bf k X X + 2 * a * b * bf k X Z + b ^ 2 * bf k Z Z := by
    rw [bf_add_left, bf_add_right, bf_add_right, bf_smul_left, bf_smul_left, bf_smul_left, bf_smul_left,
      bf_smul_right, bf_smul_right, bf_smul_right, bf_smul_right, bf_symm k Z X]; ring
  have hd := bf_nonneg k (X - Z)
  rw [bf_sub_left, bf_sub_right, bf_sub_right, bf_symm k Z X] at hd
  rw [e]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg (mul_nonneg ha hb) hd, hβ]

lemma Y_xstar {n k : ℕ} (hk : k ≤ n) : Y (xstarK n k) = ystar k := by
  funext a
  by_cases ha : a < n
  · simp only [Y, ex, ha, dif_pos, xstarK, ystar]
    by_cases h : a < k
    · simp [h, show a + 1 ≤ k by omega]
    · simp [h, show ¬ (a + 1 ≤ k) by omega]
  · rw [Y_ge _ (not_lt.mp ha)]; simp [ystar, show ¬ a < k by omega]

lemma f_star {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) (hk1 : 1 ≤ k) (β : ℝ) :
    fK n β k (xstarK n k) = -(β / 8) * (1 - 1 / ((k : ℝ) + 1)) := by
  rw [f_eq hn hk, Y_xstar hk, bf_ystar_right hk1]
  simp [ystar, show 0 < k by omega]; ring

lemma f_lower {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) {β : ℝ} (hβ : 0 < β) {m : ℕ} (hmk : m ≤ k)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ∀ a, m ≤ a → Y x a = 0) :
    -(β / 8) * (1 - 1 / ((m : ℝ) + 1)) ≤ fK n β k x := by
  rw [f_eq hn hk]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : Y x = 0 := funext (fun a => hx a (Nat.zero_le _))
    rw [this]; simp [bf]
  · rw [bf_restrict hm hmk _ hx]
    have := BU86N.min_val hm (Y x)
    nlinarith

/-- `‖x*‖² ≤ (k+1)/3`. -/
lemma xstar_norm {n k : ℕ} (hk : k ≤ n) : ‖xstarK n k‖ ^ 2 ≤ ((k : ℝ) + 1) / 3 := by
  rw [normsq_Y, Y_xstar hk]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hk)
      (fun a _ ha => by simp only [ystar, show ¬ a < k by simpa using ha, if_false]; ring)]
  have e1 : ∀ a ∈ Finset.range k, ystar k a ^ 2 = (((k - 1 - a : ℕ) : ℝ) + 1) ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro a ha
    rw [Finset.mem_range] at ha
    simp only [ystar, ha, if_true]
    have : ((k - 1 - a : ℕ) : ℝ) = (k : ℝ) - 1 - a := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [this]; field_simp; ring
  rw [Finset.sum_congr rfl e1, ← Finset.sum_div,
    Finset.sum_range_reflect (fun j => ((j : ℝ) + 1) ^ 2) k]
  have hsum : ∀ k : ℕ, ∑ j ∈ Finset.range k, ((j : ℝ) + 1) ^ 2 = (k : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) / 6 := by
    intro k; induction k with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [hsum, div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- support subspaces -/
def V (n m : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {v | ∀ a, m ≤ a → Y v a = 0}
  add_mem' := by
    intro u w hu hw a ha; rw [Y_add]; simp [hu a ha, hw a ha]
  zero_mem' := by intro a _; rw [Y_zero]; rfl
  smul_mem' := by
    intro c u hu a ha; rw [Y_smul]; simp [hu a ha]

lemma grad_mem {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) (β : ℝ) {m : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ V n m) : grad n k β x ∈ V n (m + 1) := by
  intro a ha
  rw [Y_grad hn hk, row_supp _ hx a ha]
  simp [show a ≠ 0 by omega]

lemma V_mono {n m m' : ℕ} (h : m ≤ m') : V n m ≤ V n m' := fun _ hv a ha => hv a (h.trans ha)

lemma span_supp {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) (β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hsc : SatisfiesSpanCondition (grad n k β) x) : ∀ t, x (t + 1) ∈ V n t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    have h := hsc.2 t
    refine (Submodule.span_le.mpr ?_) h
    rintro _ ⟨s, ⟨hs1, hst⟩, rfl⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have := grad_mem hn hk β (ih s' (by omega))
    exact V_mono hst this

end BU86

open BU86 in
theorem solution (n t : ℕ) (β : ℝ) (ht : 1 ≤ t)
    (htn : 2 * t + 1 ≤ n) (hβ : 0 < β) :
    ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ y, HasGradientAt (fK n β (2 * t + 1)) (g y) y) ∧ IsBetaSmooth g β ∧
        ConvexOn ℝ Set.univ (fK n β (2 * t + 1)) ∧
        (∀ y, fK n β (2 * t + 1) (xstarK n (2 * t + 1)) ≤ fK n β (2 * t + 1) y) ∧
        ∀ x : ℕ → EuclideanSpace ℝ (Fin n), SatisfiesSpanCondition g x →
          ∀ s ∈ Finset.Icc 1 t,
            fK n β (2 * t + 1) (x s) - fK n β (2 * t + 1) (xstarK n (2 * t + 1)) ≥
              3 * β / 32 * (‖x 1 - xstarK n (2 * t + 1)‖ ^ 2 / ((t : ℝ) + 1) ^ 2) := by
  have hn : 1 ≤ n := by omega
  set k := 2 * t + 1 with hkdef
  have hk : k ≤ n := htn
  have hk1 : 1 ≤ k := by omega
  refine ⟨grad n k β, fun y => hasGrad hn hk hβ y, smooth hn hk hβ, convex hn hk hβ, ?_, ?_⟩
  · intro y
    rw [f_star hn hk hk1]
    rw [f_eq hn hk]
    have := BU86N.min_val hk1 (Y y)
    nlinarith
  · intro x hsc s hs
    rw [Finset.mem_Icc] at hs
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hsupp := span_supp hn hk β x hsc s'
    have hlow := f_lower hn hk hβ (m := s') (by omega) (x (s' + 1)) hsupp
    rw [f_star hn hk hk1, hsc.1, zero_sub, norm_neg]
    have hxs := xstar_norm (n := n) hk
    have hkr : (k : ℝ) = 2 * t + 1 := by rw [hkdef]; push_cast; ring
    rw [hkr] at hxs ⊢
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hs' : (s' : ℝ) + 1 ≤ t := by exact_mod_cast hs.2
    have h0 : (0 : ℝ) ≤ s' := Nat.cast_nonneg s'
    -- lower bound on the gap
    have gap : β / (16 * ((t : ℝ) + 1)) ≤
        -(β / 8) * (1 - 1 / ((s' : ℝ) + 1)) - -(β / 8) * (1 - 1 / (2 * (t : ℝ) + 1 + 1)) := by
      have e : -(β / 8) * (1 - 1 / ((s' : ℝ) + 1)) - -(β / 8) * (1 - 1 / (2 * (t : ℝ) + 1 + 1)) =
          β / 8 * (1 / ((s' : ℝ) + 1) - 1 / (2 * (t : ℝ) + 2)) := by ring
      rw [e]
      have h1 : 1 / ((t : ℝ) + 1) ≤ 1 / ((s' : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : 1 / (2 * (t : ℝ) + 2) = 1 / ((t : ℝ) + 1) / 2 := by field_simp; try ring
      rw [h2]
      have h3 : β / (16 * ((t : ℝ) + 1)) = β / 8 * (1 / ((t : ℝ) + 1) / 2) := by field_simp; try ring
      rw [h3]
      have : 0 < 1 / ((t : ℝ) + 1) := by positivity
      nlinarith
    have rhs : 3 * β / 32 * (‖xstarK n k‖ ^ 2 / ((t : ℝ) + 1) ^ 2) ≤ β / (16 * ((t : ℝ) + 1)) := by
      have htp : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      have : ‖xstarK n k‖ ^ 2 ≤ (2 * (t : ℝ) + 1 + 1) / 3 := hxs
      calc 3 * β / 32 * (‖xstarK n k‖ ^ 2 / ((t : ℝ) + 1) ^ 2)
          ≤ 3 * β / 32 * ((2 * (t : ℝ) + 1 + 1) / 3 / ((t : ℝ) + 1) ^ 2) := by gcongr
        _ = β / (16 * ((t : ℝ) + 1)) := by field_simp; try ring
    linarith
