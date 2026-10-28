-- Prove2me | solution 1 for EthierKurtz.kmt_dyadic_blocks_glue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T02:17:51.954644+00:00
-- url     : https://prove2.me/submissions/c8536b75-fc2a-4fa5-a60a-6279c8d4910b

import Mathlib

section X0_Tree

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Dyadic index type: `Idx 0 = Unit`, `Idx (n+1) = Idx n ⊕ Idx n` (left half first). -/
@[reducible] def Idx : ℕ → Type
  | 0 => Unit
  | n + 1 => Idx n ⊕ Idx n

instance instFintypeIdx : ∀ n, Fintype (Idx n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => haveI := instFintypeIdx n; inferInstanceAs (Fintype (Idx n ⊕ Idx n))

instance instDecEqIdx : ∀ n, DecidableEq (Idx n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => haveI := instDecEqIdx n; inferInstanceAs (DecidableEq (Idx n ⊕ Idx n))

instance instUniqueIdx0 : Unique (Idx 0) := inferInstanceAs (Unique Unit)

/-- Node Gaussians: one real per internal node. -/
@[reducible] def Zn : ℕ → Type
  | 0 => Unit
  | n + 1 => ℝ × Zn n × Zn n

/-- Constructor for `Zn (n+1)`. -/
@[reducible] def Zn.mk {n : ℕ} (z0 : ℝ) (zL zR : Zn n) : Zn (n + 1) := (z0, zL, zR)

/-- In-order position of a leaf. -/
def toNat : (n : ℕ) → Idx n → ℕ
  | 0, _ => 0
  | n + 1, Sum.inl i => toNat n i
  | n + 1, Sum.inr i => 2 ^ n + toNat n i

lemma toNat_lt : ∀ (n : ℕ) (i : Idx n), toNat n i < 2 ^ n
  | 0, _ => by simp [toNat]
  | n + 1, Sum.inl i => by
      have := toNat_lt n i; simp only [toNat, pow_succ]; omega
  | n + 1, Sum.inr i => by
      have := toNat_lt n i; simp only [toNat, pow_succ]; omega

/-- Partial sum over the first `k` leaves. -/
noncomputable def ps (n : ℕ) (f : Idx n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => toNat n i < k), f i

lemma ps_zero (n : ℕ) (f : Idx n → ℝ) : ps n f 0 = 0 := by
  simp [ps]

lemma ps_full (n : ℕ) (f : Idx n → ℝ) {k : ℕ} (hk : 2 ^ n ≤ k) : ps n f k = ∑ i, f i := by
  unfold ps
  rw [Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le (toNat_lt n i) hk]

lemma ps_succ (n : ℕ) (f : Idx (n + 1) → ℝ) (k : ℕ) :
    ps (n + 1) f k = ps n (fun i => f (Sum.inl i)) k + ps n (fun i => f (Sum.inr i)) (k - 2 ^ n) := by
  unfold ps
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [show (∑ a : Idx (n + 1), if toNat (n + 1) a < k then f a else 0) =
      ∑ a : Idx n ⊕ Idx n, if toNat (n + 1) a < k then f a else 0 from rfl, Fintype.sum_sum_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [toNat]
  congr 1
  apply propext
  omega


end P99bcb804

end X0_Tree

section X1_Block

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma measurable_ps (n k : ℕ) : Measurable fun f : Idx n → ℝ => ps n f k := by
  unfold ps; exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i

end P99bcb804

end X1_Block

section X2_Tail

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma markov_exp {α : Type*} [MeasurableSpace α] (μ : Measure α) {g : α → ℝ} (hg : Measurable g)
    {c : ℝ} (hc : 0 < c) {M : ℝ≥0∞} (hM : ∫⁻ a, ENNReal.ofReal (exp (c * g a)) ∂μ ≤ M) (s : ℝ) :
    μ {a | s < g a} ≤ M * ENNReal.ofReal (exp (-(c * s))) := by
  have hsub : {a | s < g a} ⊆ {a | ENNReal.ofReal (exp (c * s)) ≤ ENNReal.ofReal (exp (c * g a))} := by
    intro a ha
    have ha' : s < g a := ha
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div ((Real.measurable_exp.comp
    (measurable_const.mul hg)).ennreal_ofReal.aemeasurable)
    (by simpa using Real.exp_pos (c * s)) ENNReal.ofReal_ne_top).trans ?_
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
  exact mul_le_mul_of_nonneg_right hM zero_le


end P99bcb804

end X2_Tail

section X3_Glue1


/-! P8 part 1: the per-block maximal deviation `Dl`, a tail-to-mgf conversion, and the block mgf. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Largest partial-sum deviation inside one block. -/
noncomputable def Dl (n : ℕ) (p : (Idx n → ℝ) × (Idx n → ℝ)) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' (by simp) fun k => |ps n p.1 k - ps n p.2 k|

lemma measurable_Dl (n : ℕ) : Measurable (Dl n) := by
  unfold Dl
  exact Finset.measurable_range_sup''
    (f := fun k (p : (Idx n → ℝ) × (Idx n → ℝ)) => |ps n p.1 k - ps n p.2 k|) fun k _ =>
    (((measurable_ps n k).comp measurable_fst).sub ((measurable_ps n k).comp measurable_snd)).abs

lemma le_Dl (n k : ℕ) (p : (Idx n → ℝ) × (Idx n → ℝ)) :
    |ps n p.1 k - ps n p.2 k| ≤ Dl n p := by
  unfold Dl
  by_cases hk : k ≤ 2 ^ n
  · exact Finset.le_sup' (fun k => |ps n p.1 k - ps n p.2 k|) (Finset.mem_range.2 (by omega))
  · rw [ps_full n p.1 (k := k) (by omega), ps_full n p.2 (k := k) (by omega),
      ← ps_full n p.1 (k := 2 ^ n) le_rfl, ← ps_full n p.2 (k := 2 ^ n) le_rfl]
    exact Finset.le_sup' (fun k => |ps n p.1 k - ps n p.2 k|) (Finset.mem_range.2 (by omega))

lemma Dl_nonneg (n : ℕ) (p : (Idx n → ℝ) × (Idx n → ℝ)) : 0 ≤ Dl n p :=
  (abs_nonneg _).trans (le_Dl n 0 p)

lemma Dl_lt (n : ℕ) (p : (Idx n → ℝ) × (Idx n → ℝ)) {t : ℝ} (h : t < Dl n p) :
    ∃ k : ℕ, t < |ps n p.1 k - ps n p.2 k| := by
  unfold Dl at h
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (2 ^ n + 1)) (by simp)
    (fun k => |ps n p.1 k - ps n p.2 k|)
  exact ⟨k, hk ▸ h⟩

/-- Tail bound to exponential moment. -/
lemma mgf_of_tail {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {g : α → ℝ} (hg : Measurable g) {a C c A : ℝ} (hC : 0 < C) (hc : 0 < c) (hA : 0 ≤ A)
    (h : ∀ s : ℝ, 0 ≤ s → μ {x | a + C * s < g x} ≤ ENNReal.ofReal (A * exp (-(c * s)))) :
    ∫⁻ x, ENNReal.ofReal (exp (c / (2 * C) * g x)) ∂μ ≤
      ENNReal.ofReal (exp (c / (2 * C) * (a + C)) +
        A * exp (c / (2 * C) * (a + 2 * C)) / (1 - exp (-(c / 2)))) := by
  set l := c / (2 * C) with hl
  have hl0 : 0 < l := by positivity
  have hlC : l * C = c / 2 := by rw [hl]; field_simp
  set q := exp (-(c / 2)) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hS : ∀ m : ℕ, MeasurableSet {x | a + C * (m : ℝ) < g x} := fun m =>
    measurableSet_lt measurable_const hg
  have hpt : ∀ x, ENNReal.ofReal (exp (l * g x)) ≤ ENNReal.ofReal (exp (l * (a + C))) +
      ∑' m : ℕ, ENNReal.ofReal (exp (l * (a + C * ((m : ℝ) + 2)))) *
        Set.indicator {x | a + C * (m : ℝ) < g x} 1 x := by
    intro x
    by_cases h1 : g x ≤ a + C
    · exact le_add_right (ENNReal.ofReal_le_ofReal
        (exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 hl0.le)))
    · push Not at h1
      set m := ⌊(g x - a) / C⌋₊ with hm
      have hpos : 1 ≤ (g x - a) / C := by rw [le_div_iff₀ hC]; linarith
      have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hpos)
      have hfl : (m : ℝ) ≤ (g x - a) / C := Nat.floor_le (by linarith)
      have hlt : (g x - a) / C < m + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hC] at hfl
      rw [div_lt_iff₀ hC] at hlt
      have hcast : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm1]; simp
      refine le_add_left (le_trans ?_ (ENNReal.le_tsum (m - 1)))
      have hmem : x ∈ {x | a + C * ((m - 1 : ℕ) : ℝ) < g x} := by
        show a + C * ((m - 1 : ℕ) : ℝ) < g x
        rw [hcast]; nlinarith
      rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hl0.le))
      rw [hcast]; nlinarith
  have hterm : ∀ m : ℕ, ENNReal.ofReal (exp (l * (a + C * ((m : ℝ) + 2)))) *
      μ {x | a + C * (m : ℝ) < g x} ≤
        ENNReal.ofReal (A * exp (l * (a + 2 * C)) * q ^ m) := by
    intro m
    refine (mul_le_mul' le_rfl (h m (Nat.cast_nonneg m))).trans ?_
    rw [← ENNReal.ofReal_mul (exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [hq, ← Real.exp_nat_mul]
    have : exp (l * (a + C * ((m : ℝ) + 2))) * (A * exp (-(c * m))) =
        A * (exp (l * (a + C * ((m : ℝ) + 2))) * exp (-(c * m))) := by ring
    rw [this, ← exp_add, mul_assoc, ← exp_add]
    congr 2
    have : l * (a + C * ((m : ℝ) + 2)) = l * (a + 2 * C) + (l * C) * m := by ring
    rw [this, hlC]; ring
  have hsum : Summable fun m : ℕ => A * exp (l * (a + 2 * C)) * q ^ m :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc ∫⁻ x, ENNReal.ofReal (exp (l * g x)) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (exp (l * (a + C))) +
          ∑' m : ℕ, ENNReal.ofReal (exp (l * (a + C * ((m : ℝ) + 2)))) *
            Set.indicator {x | a + C * (m : ℝ) < g x} 1 x) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (exp (l * (a + C))) + ∑' m : ℕ,
          ENNReal.ofReal (exp (l * (a + C * ((m : ℝ) + 2)))) * μ {x | a + C * (m : ℝ) < g x} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun m => ((measurable_one.indicator (hS m)).const_mul _).aemeasurable]
        congr 1
        refine tsum_congr fun m => ?_
        rw [lintegral_const_mul _ (measurable_one.indicator (hS m)), lintegral_indicator_one (hS m)]
    _ ≤ ENNReal.ofReal (exp (l * (a + C))) +
          ∑' m : ℕ, ENNReal.ofReal (A * exp (l * (a + 2 * C)) * q ^ m) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal (exp (l * (a + C)) + A * exp (l * (a + 2 * C)) / (1 - q)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum, tsum_mul_left,
          tsum_geometric_of_lt_one hq0 hq1, ← ENNReal.ofReal_add (exp_pos _).le
            (by have : 0 < 1 - q := by linarith
                positivity)]
        rfl

end P99bcb804


end X3_Glue1

section X4_Glue2

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma toNat_inj : ∀ (n : ℕ) (i j : Idx n), toNat n i = toNat n j → i = j
  | 0, i, j, _ => Subsingleton.elim i j
  | n + 1, Sum.inl i, Sum.inl j, h => by
      simp only [toNat] at h; rw [toNat_inj n i j h]
  | n + 1, Sum.inl i, Sum.inr j, h => by
      simp only [toNat] at h; have := toNat_lt n i; omega
  | n + 1, Sum.inr i, Sum.inl j, h => by
      simp only [toNat] at h; have := toNat_lt n j; omega
  | n + 1, Sum.inr i, Sum.inr j, h => by
      simp only [toNat] at h; rw [toNat_inj n i j (by omega)]

lemma toNat_surj : ∀ (n r : ℕ), r < 2 ^ n → ∃ i : Idx n, toNat n i = r
  | 0, r, hr => ⟨(), by simp [toNat]; omega⟩
  | n + 1, r, hr => by
      by_cases h : r < 2 ^ n
      · obtain ⟨i, hi⟩ := toNat_surj n r h
        exact ⟨Sum.inl i, by simp [toNat, hi]⟩
      · obtain ⟨i, hi⟩ := toNat_surj n (r - 2 ^ n) (by rw [pow_succ] at hr; omega)
        exact ⟨Sum.inr i, by simp only [toNat, hi]; omega⟩

lemma ps_step (n : ℕ) (f : Idx n → ℝ) (i : Idx n) (r : ℕ) (hi : toNat n i = r) :
    ps n f (r + 1) = ps n f r + f i := by
  unfold ps
  rw [Finset.sum_filter, Finset.sum_filter]
  have key : ∀ j, (if toNat n j < r + 1 then f j else 0) =
      (if toNat n j < r then f j else 0) + (if j = i then f j else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [hi]
    · have : toNat n j ≠ r := fun h => hj (toNat_inj n j i (h.trans hi.symm))
      by_cases h : toNat n j < r
      · simp [h, hj, show toNat n j < r + 1 by omega]
      · simp [h, hj, show ¬ toNat n j < r + 1 by omega]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib]
  simp



end P99bcb804

end X4_Glue2

section X5_Glue3


/-! P8 part 3: blocks of size `2^(2^j)` laid end to end; the position equivalence and the
prefix-sum identity. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Block sizes `2^(2^j)`. -/
def bsz (j : ℕ) : ℕ := 2 ^ (2 ^ j)

/-- Block starts. -/
def st (j : ℕ) : ℕ := ∑ l ∈ Finset.range j, bsz l

lemma bsz_pos (j : ℕ) : 0 < bsz j := by unfold bsz; positivity

lemma st_zero : st 0 = 0 := by simp [st]

lemma st_succ (j : ℕ) : st (j + 1) = st j + bsz j := by simp [st, Finset.sum_range_succ]

lemma st_mono {j j' : ℕ} (h : j ≤ j') : st j ≤ st j' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma le_st (j : ℕ) : j ≤ st j := by
  induction j with
  | zero => simp [st_zero]
  | succ j ih => rw [st_succ]; have := bsz_pos j; omega

/-- Position of leaf `i` of block `j` in the glued sequence. -/
def pos (p : Σ j : ℕ, Idx (2 ^ j)) : ℕ := st p.1 + toNat (2 ^ p.1) p.2

lemma toNat_lt_bsz (j : ℕ) (i : Idx (2 ^ j)) : toNat (2 ^ j) i < bsz j := toNat_lt _ i

lemma block_unique {j j' a b : ℕ} (ha : a < bsz j) (hb : b < bsz j')
    (h : st j + a = st j' + b) : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := st_mono (Nat.succ_le_of_lt hlt); rw [st_succ] at this; omega
  · have := st_mono (Nat.succ_le_of_lt hlt); rw [st_succ] at this; omega

lemma pos_injective : Function.Injective pos := by
  rintro ⟨j, a⟩ ⟨j', b⟩ h
  simp only [pos] at h
  obtain rfl := block_unique (toNat_lt_bsz j a) (toNat_lt_bsz j' b) h
  have : a = b := toNat_inj _ a b (by omega)
  subst this; rfl

lemma exists_block (k : ℕ) : ∃ j r, k = st j + r ∧ r < bsz j := by
  classical
  have hex : ∃ j, k < st (j + 1) := ⟨k, by have := le_st (k + 1); omega⟩
  set j := Nat.find hex with hj
  have h1 : k < st (j + 1) := Nat.find_spec hex
  have h2 : st j ≤ k := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, st_zero]; exact Nat.zero_le _
    · have hmin := Nat.find_min hex (show j - 1 < Nat.find hex by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hmin
      omega
  refine ⟨j, k - st j, by omega, ?_⟩
  rw [st_succ] at h1; omega

lemma pos_surjective : Function.Surjective pos := by
  intro k
  obtain ⟨j, r, rfl, hr⟩ := exists_block k
  obtain ⟨i, hi⟩ := toNat_surj (2 ^ j) r hr
  exact ⟨⟨j, i⟩, by simp [pos, hi]⟩

/-- The glued index set. -/
noncomputable def E : (Σ j : ℕ, Idx (2 ^ j)) ≃ ℕ :=
  Equiv.ofBijective pos ⟨pos_injective, pos_surjective⟩

lemma E_symm_pos (j : ℕ) (i : Idx (2 ^ j)) : E.symm (st j + toNat (2 ^ j) i) = ⟨j, i⟩ := by
  rw [Equiv.symm_apply_eq]; rfl

/-- Prefix sums of a glued sequence: completed blocks plus a partial block. -/
lemma prefix_sum (Y : (Σ j : ℕ, Idx (2 ^ j)) → ℝ) : ∀ J r : ℕ, r ≤ bsz J →
    ∑ k ∈ range (st J + r), Y (E.symm k) =
      ∑ j ∈ range J, ps (2 ^ j) (fun i => Y ⟨j, i⟩) (bsz j) +
        ps (2 ^ J) (fun i => Y ⟨J, i⟩) r := by
  have step : ∀ (J r : ℕ) (A : ℝ), r < bsz J →
      ∑ k ∈ range (st J + r), Y (E.symm k) = A + ps (2 ^ J) (fun i => Y ⟨J, i⟩) r →
      ∑ k ∈ range (st J + (r + 1)), Y (E.symm k) = A + ps (2 ^ J) (fun i => Y ⟨J, i⟩) (r + 1) := by
    intro J r A hr h
    obtain ⟨i, hi⟩ := toNat_surj (2 ^ J) r hr
    rw [← add_assoc, Finset.sum_range_succ, h, ps_step _ _ i r hi]
    have : E.symm (st J + r) = ⟨J, i⟩ := by rw [← hi]; exact E_symm_pos J i
    rw [this]; ring
  intro J
  induction J with
  | zero =>
    intro r hr
    induction r with
    | zero => simp [st_zero, ps_zero]
    | succ r ih =>
      have h := ih (by omega)
      simp only [Finset.range_zero, Finset.sum_empty] at h ⊢
      exact step 0 r 0 (by omega) h
  | succ J ihJ =>
    intro r hr
    induction r with
    | zero =>
      rw [add_zero, ps_zero, add_zero, st_succ, ihJ (bsz J) le_rfl, Finset.sum_range_succ]
    | succ r ih => exact step (J + 1) r _ (by omega) (ih (by omega))

lemma dev_le_glue (Y1 Y2 : (Σ j : ℕ, Idx (2 ^ j)) → ℝ) (J r : ℕ) (hr : r ≤ bsz J) :
    |∑ k ∈ range (st J + r), Y1 (E.symm k) - ∑ k ∈ range (st J + r), Y2 (E.symm k)| ≤
      ∑ j ∈ range (J + 1), Dl (2 ^ j) (fun i => Y1 ⟨j, i⟩, fun i => Y2 ⟨j, i⟩) := by
  rw [prefix_sum Y1 J r hr, prefix_sum Y2 J r hr, Finset.sum_range_succ]
  have h1 : ∀ j ∈ range J, |ps (2 ^ j) (fun i => Y1 ⟨j, i⟩) (bsz j) -
      ps (2 ^ j) (fun i => Y2 ⟨j, i⟩) (bsz j)| ≤
        Dl (2 ^ j) (fun i => Y1 ⟨j, i⟩, fun i => Y2 ⟨j, i⟩) := fun j _ =>
    le_Dl (2 ^ j) (bsz j) (fun i => Y1 ⟨j, i⟩, fun i => Y2 ⟨j, i⟩)
  calc _ = |∑ j ∈ range J, (ps (2 ^ j) (fun i => Y1 ⟨j, i⟩) (bsz j) -
          ps (2 ^ j) (fun i => Y2 ⟨j, i⟩) (bsz j)) +
          (ps (2 ^ J) (fun i => Y1 ⟨J, i⟩) r - ps (2 ^ J) (fun i => Y2 ⟨J, i⟩) r)| := by
        rw [Finset.sum_sub_distrib]; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ ≤ _ := add_le_add (Finset.sum_le_sum h1)
        (le_Dl (2 ^ J) r (fun i => Y1 ⟨J, i⟩, fun i => Y2 ⟨J, i⟩))

lemma locate (k : ℕ) (hk : 1 ≤ k) : ∃ J r, k = st J + r ∧ 1 ≤ r ∧ r ≤ bsz J := by
  obtain ⟨J, r, h, hr⟩ := exists_block (k - 1)
  exact ⟨J, r + 1, by omega, by omega, by omega⟩

lemma block_le {k n J J' r r' : ℕ} (hk : k ≤ n) (h1 : k = st J + r) (h1r : 1 ≤ r)
    (h2 : n = st J' + r') (h2r : r' ≤ bsz J') : J ≤ J' := by
  by_contra h
  have := st_mono (show J' + 1 ≤ J by omega)
  rw [st_succ] at this; omega

lemma bsz_le_of_block {n J r : ℕ} (hJ : 1 ≤ J) (h : n = st J + r) : bsz (J - 1) ≤ n := by
  have := st_succ (J - 1)
  rw [Nat.sub_add_cancel hJ] at this
  omega

end P99bcb804


end X5_Glue3

section X6_Glue4

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma sum_two_pow_le : ∀ J : ℕ, ∑ j ∈ range J, 2 ^ (j + 1) ≤ 2 ^ (J + 1)
  | 0 => by simp
  | J + 1 => by
      rw [Finset.sum_range_succ]
      have := sum_two_pow_le J
      rw [pow_succ 2 (J + 1)]; omega

lemma glue_marg (G : Measure ℝ) [IsProbabilityMeasure G] (μ : ∀ j : ℕ, Measure (Idx (2 ^ j) → ℝ))
    [∀ j, IsProbabilityMeasure (μ j)] (hμ : ∀ j, μ j = Measure.pi (fun _ : Idx (2 ^ j) => G)) :
    (Measure.infinitePi μ).map (fun ω k => ω (E.symm k).1 (E.symm k).2) =
      Measure.infinitePi (fun _ : ℕ => G) := by
  have hμ' : μ = fun j => Measure.infinitePi (fun _ : Idx (2 ^ j) => G) := by
    funext j; rw [hμ j, Measure.infinitePi_eq_pi]
  subst hμ'
  have hcomp : (fun ω : (Π j : ℕ, Idx (2 ^ j) → ℝ) => fun k => ω (E.symm k).1 (E.symm k).2) =
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) E) ∘
        (MeasurableEquiv.piCurry (fun j (_ : Idx (2 ^ j)) => ℝ)).symm := by
    funext ω k
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply, MeasurableEquiv.coe_piCurry_symm,
      Sigma.uncurry]
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    Measure.infinitePi_map_piCurry_symm (fun j (_ : Idx (2 ^ j)) => G)]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => G) E


end P99bcb804

end X6_Glue4

section X7_Gl1


/-! R4 / Gl1 (Q8 glue): generic block exponential moment from a tail bound (`block_mgf_gen`) and
generic gluing of dyadic block couplings (`glue_gen`, the Glue4 proof with the block family abstracted). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Block exponential moment of `Dl` from a tail bound at level `C (n+1+s)`. -/
theorem block_mgf_gen {n : ℕ} (Q : Measure ((Idx n → ℝ) × (Idx n → ℝ))) [IsProbabilityMeasure Q]
    {C A R : ℝ} (hC : 0 < C) (hA : 0 < A) (hR : 1 ≤ R)
    (H : ∀ s : ℝ, 0 ≤ s → Q {q | ∃ k : ℕ, C * (n + 1 + s) < |ps n q.1 k - ps n q.2 k|} ≤
      ENNReal.ofReal (A * R ^ n * exp (-s))) :
    ∫⁻ p, ENNReal.ofReal (exp (1 / (2 * C) * Dl n p)) ∂Q ≤
      ENNReal.ofReal (((exp 1 + A * exp (3 / 2) / (1 - exp (-(1 / 2)))) * (R * exp (1 / 2))) ^ (n + 1)) := by
  have htail : ∀ s : ℝ, 0 ≤ s → Q {p | C * (n + 1) + C * s < Dl n p} ≤
      ENNReal.ofReal (A * R ^ n * exp (-(1 * s))) := by
    intro s hs
    rw [one_mul]
    refine le_trans (measure_mono fun p hp => ?_) (H s hs)
    obtain ⟨k, hk⟩ := Dl_lt n p hp
    exact ⟨k, by rw [show C * ((n : ℝ) + 1 + s) = C * (n + 1) + C * s by ring]; exact hk⟩
  refine (mgf_of_tail Q (measurable_Dl n) hC one_pos (by positivity) htail).trans
    (ENNReal.ofReal_le_ofReal ?_)
  set q := exp (-(1 / 2 : ℝ)) with hq
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have h1q : 0 < 1 - q := by linarith
  set e := exp (1 / 2 : ℝ) with he
  have he1 : 1 ≤ e := one_le_exp (by norm_num)
  have e1 : exp (1 / (2 * C) * (C * (n + 1) + C)) = e ^ n * exp 1 := by
    rw [he, ← Real.exp_nat_mul, ← exp_add]; congr 1; field_simp; ring
  have e2 : exp (1 / (2 * C) * (C * (n + 1) + 2 * C)) = e ^ n * exp (3 / 2) := by
    rw [he, ← Real.exp_nat_mul, ← exp_add]; congr 1; field_simp; ring
  rw [e1, e2]
  set K1 := exp 1 + A * exp (3 / 2) / (1 - q) with hK1
  have hK1' : 1 ≤ K1 := by
    have : 0 ≤ A * exp (3 / 2) / (1 - q) := div_nonneg (by positivity) h1q.le
    have : (1 : ℝ) ≤ exp 1 := one_le_exp (by norm_num)
    linarith
  have hRn : 1 ≤ R ^ n := one_le_pow₀ hR
  have hen : 0 ≤ e ^ n := by positivity
  have step1 : e ^ n * exp 1 + A * R ^ n * (e ^ n * exp (3 / 2)) / (1 - q) ≤ (R * e) ^ n * K1 := by
    rw [hK1, mul_pow]
    have : A * R ^ n * (e ^ n * exp (3 / 2)) / (1 - q) = R ^ n * e ^ n * (A * exp (3 / 2) / (1 - q)) := by
      ring
    rw [this, mul_add]
    have : e ^ n * exp 1 ≤ R ^ n * e ^ n * exp 1 :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hen hRn) (exp_pos _).le
    linarith
  refine step1.trans ?_
  have hRe : 1 ≤ R * e := one_le_mul_of_one_le_of_one_le hR he1
  have : (R * e) ^ n * K1 ≤ K1 ^ n * K1 * (R * e) ^ (n + 1) := by
    have a1 : (R * e) ^ n ≤ (R * e) ^ (n + 1) := pow_le_pow_right₀ hRe (Nat.le_succ n)
    have a2 : 1 ≤ K1 ^ n := one_le_pow₀ hK1'
    have a3 : 0 ≤ (R * e) ^ n := by positivity
    calc (R * e) ^ n * K1 ≤ (R * e) ^ (n + 1) * K1 := mul_le_mul_of_nonneg_right a1 (by linarith)
      _ = 1 * K1 * (R * e) ^ (n + 1) := by ring
      _ ≤ K1 ^ n * K1 * (R * e) ^ (n + 1) := by gcongr
  rw [mul_pow K1 (R * e) (n + 1), pow_succ K1 n]
  exact this

set_option maxHeartbeats 1000000 in
/-- Generic gluing of independent dyadic block couplings with exponential moments. -/
theorem glue_gen (F : Measure ℝ) [IsProbabilityMeasure F] {l M : ℝ} (hl : 0 < l) (hM : 1 ≤ M)
    (H : ∀ n : ℕ, ∃ Q : Measure ((Idx n → ℝ) × (Idx n → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Idx n => F) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Idx n => gaussianReal 0 1) ∧
        ∫⁻ p, ENNReal.ofReal (exp (l * Dl n p)) ∂Q ≤ ENNReal.ofReal (M ^ (n + 1))) :
    ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F) ∧
      Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1) ∧
      ∃ C K' lam : ℝ, 0 < C ∧ 0 < K' ∧ 0 < lam ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
            |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
            ENNReal.ofReal (K' * Real.exp (-lam * x)) := by
  choose Q hQp hQ1 hQ2 hQ3 using H
  have hQp' : ∀ j : ℕ, IsProbabilityMeasure (Q (2 ^ j)) := fun j => hQp _
  have hQf : ∀ j : ℕ, IsProbabilityMeasure ((Q (2 ^ j)).map Prod.fst) := fun j =>
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hQs : ∀ j : ℕ, IsProbabilityMeasure ((Q (2 ^ j)).map Prod.snd) := fun j =>
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  set P := Measure.infinitePi (fun j : ℕ => Q (2 ^ j)) with hP
  set Ψ : (Π j : ℕ, (Idx (2 ^ j) → ℝ) × (Idx (2 ^ j) → ℝ)) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun ω => (fun k => (ω (E.symm k).1).1 (E.symm k).2,
      fun k => (ω (E.symm k).1).2 (E.symm k).2) with hΨ
  have hf1 : Measurable fun ω : (Π j : ℕ, (Idx (2 ^ j) → ℝ) × (Idx (2 ^ j) → ℝ)) =>
      fun j => (ω j).1 :=
    measurable_pi_lambda _ fun j => measurable_fst.comp (measurable_pi_apply j)
  have hf2 : Measurable fun ω : (Π j : ℕ, (Idx (2 ^ j) → ℝ) × (Idx (2 ^ j) → ℝ)) =>
      fun j => (ω j).2 :=
    measurable_pi_lambda _ fun j => measurable_snd.comp (measurable_pi_apply j)
  have hg : Measurable fun ω : (Π j : ℕ, Idx (2 ^ j) → ℝ) => fun k => ω (E.symm k).1 (E.symm k).2 :=
    measurable_pi_lambda _ fun k => (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hΨm : Measurable Ψ := (hg.comp hf1).prodMk (hg.comp hf2)
  -- moment bound
  have hX : ∀ j, Measurable (fun p : (Idx (2 ^ j) → ℝ) × (Idx (2 ^ j) → ℝ) =>
      ENNReal.ofReal (exp (l * Dl (2 ^ j) p))) := fun j =>
    ENNReal.measurable_ofReal.comp ((measurable_Dl _).const_mul l).exp
  have hind := iIndepFun_infinitePi (P := fun j : ℕ => Q (2 ^ j)) hX
  have hmgf : ∀ J : ℕ, ∫⁻ ω, ENNReal.ofReal (exp (l * ∑ j ∈ range J, Dl (2 ^ j) (ω j))) ∂P ≤
      ENNReal.ofReal (M ^ (2 ^ (J + 1))) := by
    intro J
    have e2 : ∀ j, ∫⁻ ω, ENNReal.ofReal (exp (l * Dl (2 ^ j) (ω j))) ∂P ≤
        ENNReal.ofReal (M ^ (2 ^ (j + 1))) := by
      intro j
      rw [show (∫⁻ ω, ENNReal.ofReal (exp (l * Dl (2 ^ j) (ω j))) ∂P) =
          ∫⁻ p, ENNReal.ofReal (exp (l * Dl (2 ^ j) p)) ∂(Q (2 ^ j)) from
        (measurePreserving_eval_infinitePi (fun j : ℕ => Q (2 ^ j)) j).lintegral_comp (hX j)]
      refine (hQ3 (2 ^ j)).trans (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hM ?_))
      rw [pow_succ]; have := Nat.one_le_two_pow (n := j); omega
    calc ∫⁻ ω, ENNReal.ofReal (exp (l * ∑ j ∈ range J, Dl (2 ^ j) (ω j))) ∂P
        = ∫⁻ ω, ∏ j ∈ range J, ENNReal.ofReal (exp (l * Dl (2 ^ j) (ω j))) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [Finset.mul_sum, Real.exp_sum,
            ENNReal.ofReal_prod_of_nonneg (fun j _ => (exp_pos _).le)]
      _ = ∏ j ∈ range J, ∫⁻ ω, ENNReal.ofReal (exp (l * Dl (2 ^ j) (ω j))) ∂P := by
          have hprod := lintegral_prod_eq_prod_lintegral_of_indepFun (range J) _ hind
            (fun j => (hX j).comp (measurable_pi_apply j))
          beta_reduce at hprod
          exact hprod
      _ ≤ ∏ j ∈ range J, ENNReal.ofReal (M ^ (2 ^ (j + 1))) := Finset.prod_le_prod' fun j _ => e2 j
      _ = ENNReal.ofReal (∏ j ∈ range J, M ^ (2 ^ (j + 1))) :=
          (ENNReal.ofReal_prod_of_nonneg (fun j _ => by positivity)).symm
      _ ≤ ENNReal.ofReal (M ^ (2 ^ (J + 1))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.prod_pow_eq_pow_sum]
          exact pow_le_pow_right₀ hM (sum_two_pow_le J)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  set C' := 8 * Real.log M / (l * Real.log 2) + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  have hpow : ∀ m : ℕ, M ^ m = exp (m * Real.log M) := fun m => by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  refine ⟨P.map Ψ, Measure.isProbabilityMeasure_map hΨm.aemeasurable, ?_, ?_,
    C', 2 * M ^ 4, l, hC'0, by positivity, hl, ?_⟩
  · rw [Measure.map_map measurable_fst hΨm]
    have : Prod.fst ∘ Ψ = (fun ω : (Π j : ℕ, Idx (2 ^ j) → ℝ) =>
        fun k => ω (E.symm k).1 (E.symm k).2) ∘ (fun ω j => (ω j).1) := rfl
    rw [this, ← Measure.map_map hg hf1,
      Measure.infinitePi_map_pi _ (f := fun _ => Prod.fst) (fun j => measurable_fst)]
    exact glue_marg F _ (fun j => hQ1 (2 ^ j))
  · rw [Measure.map_map measurable_snd hΨm]
    have : Prod.snd ∘ Ψ = (fun ω : (Π j : ℕ, Idx (2 ^ j) → ℝ) =>
        fun k => ω (E.symm k).1 (E.symm k).2) ∘ (fun ω j => (ω j).2) := rfl
    rw [this, ← Measure.map_map hg hf2,
      Measure.infinitePi_map_pi _ (f := fun _ => Prod.snd) (fun j => measurable_snd)]
    exact glue_marg (gaussianReal 0 1) _ (fun j => hQ2 (2 ^ j))
  intro n hn x hx
  obtain ⟨Jn, rn, hnJ, hrn1, hrnJ⟩ := locate n hn
  set t := C' * Real.log (n : ℝ) + x with ht
  set S := {z : (ℕ → ℝ) × (ℕ → ℝ) | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ t <
      |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} with hS
  have hSm : MeasurableSet S := by
    have : S = ⋃ k : ℕ, ⋃ (_ : 1 ≤ k ∧ k ≤ n), {z : (ℕ → ℝ) × (ℕ → ℝ) |
        t < |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} := by
      ext z; simp [hS, and_assoc]
    rw [this]
    refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
    exact measurableSet_lt measurable_const (by fun_prop)
  set g : (Π j : ℕ, (Idx (2 ^ j) → ℝ) × (Idx (2 ^ j) → ℝ)) → ℝ :=
    fun ω => ∑ j ∈ range (Jn + 1), Dl (2 ^ j) (ω j) with hgdef
  have hgm : Measurable g :=
    Finset.measurable_sum _ fun j _ => (measurable_Dl _).comp (measurable_pi_apply j)
  have hsub : Ψ ⁻¹' S ⊆ {ω | t < g ω} := by
    intro ω hω
    obtain ⟨k, hk1, hkn, hk⟩ := hω
    obtain ⟨J, r, hkJ, hr1, hrJ⟩ := locate k hk1
    have hJ := block_le hkn hkJ hr1 hnJ hrnJ
    have hd := dev_le_glue (fun p => (ω p.1).1 p.2) (fun p => (ω p.1).2 p.2) J r hrJ
    rw [← hkJ] at hd
    have hmono : ∑ j ∈ range (J + 1), Dl (2 ^ j) (ω j) ≤ g ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun j _ _ => Dl_nonneg _ _)
    exact lt_of_lt_of_le hk (hd.trans hmono)
  have hmk := markov_exp P hgm hl (hmgf (Jn + 1)) t
  rw [Measure.map_apply hΨm hSm]
  refine lt_of_le_of_lt ((measure_mono hsub).trans hmk) ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  -- arithmetic
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hkey : ((2 ^ (Jn + 1 + 1) : ℕ) : ℝ) * Real.log M ≤ 4 * Real.log M + l * C' * Real.log n := by
    rcases Nat.eq_zero_or_pos Jn with h0 | h0
    · subst h0
      have : 0 ≤ l * C' * Real.log n := by positivity
      norm_num; linarith
    · have hb := bsz_le_of_block h0 hnJ
      have hb' : ((2 : ℝ) ^ (2 ^ (Jn - 1))) ≤ n := by
        have : ((bsz (Jn - 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast hb
        simpa [bsz] using this
      have hl2 : ((2 ^ (Jn - 1) : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hb')
      have h8 : ((2 ^ (Jn + 1 + 1) : ℕ) : ℝ) = 8 * ((2 ^ (Jn - 1) : ℕ) : ℝ) := by
        have : Jn + 1 + 1 = (Jn - 1) + 3 := by omega
        rw [this]; push_cast; ring
      rw [h8]
      have e : l * C' * Real.log n = 8 * Real.log M / Real.log 2 * Real.log n + l * Real.log n := by
        rw [hC']; field_simp
      rw [e]
      have : 8 * ((2 ^ (Jn - 1) : ℕ) : ℝ) * Real.log M ≤ 8 * Real.log M / Real.log 2 * Real.log n := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        nlinarith [mul_le_mul_of_nonneg_left hl2 (by positivity : (0:ℝ) ≤ 8 * Real.log M)]
      have : 0 ≤ l * Real.log n := by positivity
      linarith
  rw [hpow, hpow, ← exp_add, mul_assoc, ← exp_add, neg_mul]
  have : exp ((2 ^ (Jn + 1 + 1) : ℕ) * Real.log M + -(l * t)) ≤ exp ((4 : ℕ) * Real.log M + -(l * x)) := by
    refine exp_le_exp.2 ?_
    rw [ht]; push_cast at hkey ⊢; nlinarith
  have hpos := exp_pos ((4 : ℕ) * Real.log M + -(l * x))
  linarith

end P99bcb804


end X7_Gl1

section X8_Gc

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma one_le_Mgen {A R : ℝ} (hA : 0 < A) (hR : 1 ≤ R) :
    1 ≤ (exp 1 + A * exp (3 / 2) / (1 - exp (-(1 / 2)))) * (R * exp (1 / 2)) := by
  have hq1 : exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have h0 : 0 ≤ A * exp (3 / 2) / (1 - exp (-(1 / 2))) := div_nonneg (by positivity) (by linarith)
  have h1 : (1 : ℝ) ≤ exp 1 := one_le_exp (by norm_num)
  have h2 : (1 : ℝ) ≤ exp (1 / 2) := one_le_exp (by norm_num)
  exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le hR h2)


end P99bcb804

end X8_Gc

section Tail
open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- In-order positions identify the dyadic index type with `Fin (2^n)`. -/
noncomputable def eFin (n : ℕ) : Idx n ≃ Fin (2 ^ n) :=
  Equiv.ofBijective (fun i => ⟨toNat n i, toNat_lt n i⟩)
    ⟨fun i j h => toNat_inj n i j (congrArg Fin.val h),
     fun r => by
       obtain ⟨i, hi⟩ := toNat_surj n r.1 r.2
       exact ⟨i, Fin.ext hi⟩⟩

lemma eFin_val (n : ℕ) (i : Idx n) : ((eFin n i : Fin (2 ^ n)) : ℕ) = toNat n i := rfl

lemma ps_eFin (n : ℕ) (g : Fin (2 ^ n) → ℝ) (k : ℕ) :
    ps n (fun i => g (eFin n i)) k =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ n) => (i : ℕ) < k), g i := by
  unfold ps
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Equiv.sum_comp (eFin n) (fun j : Fin (2 ^ n) => if (j : ℕ) < k then g j else 0)

lemma pi_eFin (n : ℕ) (F : Measure ℝ) [IsProbabilityMeasure F] :
    (Measure.pi (fun _ : Fin (2 ^ n) => F)).map (fun g : Fin (2 ^ n) → ℝ => fun i => g (eFin n i)) =
      Measure.pi (fun _ : Idx n => F) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Idx n => F) (eFin n).symm).map_eq
  have hf : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Idx n => ℝ) (eFin n).symm) :
      (Fin (2 ^ n) → ℝ) → (Idx n → ℝ)) = fun g i => g (eFin n i) := by
    funext g i
    have := Equiv.piCongrLeft_apply_apply (fun _ : Idx n => ℝ) (eFin n).symm g (eFin n i)
    simp only [Equiv.symm_apply_apply] at this
    rw [← this]; rfl
  rw [hf] at h
  exact h

end P99bcb804


end Tail

open MeasureTheory ProbabilityTheory in
theorem solution (F : Measure ℝ) [IsProbabilityMeasure F]
    (h : ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => F) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 < x →
          Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
              (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x))) :
    ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F) ∧
      Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
            |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  obtain ⟨C, K, lam, hC, hK, hlam, H⟩ := h
  set C' : ℝ := C * Real.log 2 + 1 / lam with hC'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC'0 : 0 < C' := by positivity
  refine P99bcb804.glue_gen F (l := 1 / (2 * C')) (by positivity)
    (P99bcb804.one_le_Mgen hK le_rfl) ?_
  intro n
  obtain ⟨Q, hQp, hQ1, hQ2, hQ3⟩ := H n
  set T : (Fin (2 ^ n) → ℝ) × (Fin (2 ^ n) → ℝ) → (P99bcb804.Idx n → ℝ) × (P99bcb804.Idx n → ℝ) :=
    fun q => (fun i => q.1 (P99bcb804.eFin n i), fun i => q.2 (P99bcb804.eFin n i)) with hT
  have hTm : Measurable T := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_snd
  have hQT : IsProbabilityMeasure (Q.map T) := Measure.isProbabilityMeasure_map hTm.aemeasurable
  refine ⟨Q.map T, hQT, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hTm]
    have : (Prod.fst ∘ T) = (fun g : Fin (2 ^ n) → ℝ => fun i => g (P99bcb804.eFin n i)) ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply _) measurable_fst,
      hQ1, P99bcb804.pi_eFin]
  · rw [Measure.map_map measurable_snd hTm]
    have : (Prod.snd ∘ T) = (fun g : Fin (2 ^ n) → ℝ => fun i => g (P99bcb804.eFin n i)) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply _) measurable_snd,
      hQ2, P99bcb804.pi_eFin]
  · refine P99bcb804.block_mgf_gen (Q.map T) hC'0 hK le_rfl ?_
    intro s hs
    have hx : 0 < (1 + s) / lam := by positivity
    have hmeas : MeasurableSet {q : (P99bcb804.Idx n → ℝ) × (P99bcb804.Idx n → ℝ) |
        ∃ k : ℕ, C' * (n + 1 + s) < |P99bcb804.ps n q.1 k - P99bcb804.ps n q.2 k|} := by
      have : {q : (P99bcb804.Idx n → ℝ) × (P99bcb804.Idx n → ℝ) |
          ∃ k : ℕ, C' * (n + 1 + s) < |P99bcb804.ps n q.1 k - P99bcb804.ps n q.2 k|} =
          ⋃ k : ℕ, {q | C' * (n + 1 + s) < |P99bcb804.ps n q.1 k - P99bcb804.ps n q.2 k|} := by
        ext q; simp
      rw [this]
      refine MeasurableSet.iUnion fun k => measurableSet_lt measurable_const ?_
      exact (((P99bcb804.measurable_ps n k).comp measurable_fst).sub
        ((P99bcb804.measurable_ps n k).comp measurable_snd)).abs
    rw [Measure.map_apply hTm hmeas]
    refine le_trans (measure_mono ?_) ((hQ3 _ hx).le.trans (ENNReal.ofReal_le_ofReal ?_))
    · intro q hq
      obtain ⟨k, hk⟩ := hq
      simp only [hT, P99bcb804.ps_eFin] at hk
      have hpos : (0 : ℝ) < C' * (n + 1 + s) := by positivity
      -- reduce to 1 ≤ k ≤ 2^n
      set S : ℕ → ℝ := fun k => (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ n) => (i : ℕ) < k), q.1 i) -
        (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ n) => (i : ℕ) < k), q.2 i) with hS
      have hcap : ∀ k : ℕ, 2 ^ n ≤ k → S k = S (2 ^ n) := by
        intro k hk2
        simp only [hS]
        congr 1 <;>
        · refine Finset.sum_congr ?_ fun _ _ => rfl
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro _; exact i.2
          · intro _; omega
      have hthr : C * Real.log ((2 ^ n : ℕ) : ℝ) + (1 + s) / lam ≤ C' * (n + 1 + s) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, hC']
        have h1 : (1 + s) / lam ≤ (n + 1 + s) / lam :=
          div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hlam.le
        have h2 : C * ((n : ℝ) * Real.log 2) ≤ C * Real.log 2 * (n + 1 + s) := by
          have : (n : ℝ) ≤ n + 1 + s := by linarith
          nlinarith [mul_pos hC hl2]
        have h3 : (n + 1 + s) / lam = 1 / lam * (n + 1 + s) := by ring
        nlinarith
      by_cases hk0 : k = 0
      · subst hk0
        have : S 0 = 0 := by simp [hS]
        simp only [hS] at this
        rw [this, abs_zero] at hk
        exact absurd hk (not_lt.2 hpos.le)
      by_cases hk2 : k ≤ 2 ^ n
      · exact ⟨k, Nat.one_le_iff_ne_zero.2 hk0, hk2, lt_of_le_of_lt hthr hk⟩
      · refine ⟨2 ^ n, Nat.one_le_two_pow, le_rfl, lt_of_le_of_lt hthr ?_⟩
        have := hcap k (by omega)
        simp only [hS] at this
        rw [← this]; exact hk
    · rw [one_pow, mul_one]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK.le
      rw [neg_mul, mul_div_cancel₀ _ hlam.ne']
      linarith
