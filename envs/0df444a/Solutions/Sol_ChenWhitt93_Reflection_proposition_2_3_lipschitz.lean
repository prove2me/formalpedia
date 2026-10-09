-- Prove2me | solution 1 for ChenWhitt93.Reflection.proposition_2_3_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T15:52:35.167786+00:00
-- url     : https://prove2.me/submissions/9d13c46a-4232-4cb8-bfc2-7caf4fc650f3

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

set_option autoImplicit false

open Filter Topology Matrix

namespace CW93Lip

open ChenWhitt93.Reflection

variable {n : ℕ}

/-! ## Stieltjes key lemma (one-dimensional Skorokhod comparison) -/

lemma stieltjes_key (F : StieltjesFunction ℝ) (T t a : ℝ) (P : ℝ → Prop) (ht : t ≤ T)
    (ha : 0 ≤ a) (hneg : ∀ s < 0, F s = 0)
    (hmeas : F.measure {s | s ∈ Set.Icc (0:ℝ) T ∧ P s} = 0)
    (hP : ∀ s, 0 ≤ s → s ≤ t → a < F s → P s) : F t ≤ a := by
  by_contra hlt
  push Not at hlt
  set S : Set ℝ := {s | s ≤ t ∧ a < F s} with hS
  have hSsub : S ⊆ {s | s ∈ Set.Icc (0:ℝ) T ∧ P s} := by
    intro s hs
    obtain ⟨hst, hFs⟩ := hs
    have hs0 : 0 ≤ s := by
      by_contra h
      push Not at h
      rw [hneg s h] at hFs
      linarith
    exact ⟨⟨hs0, hst.trans ht⟩, hP s hs0 hst hFs⟩
  have hS0 : F.measure S = 0 := MeasureTheory.measure_mono_null hSsub hmeas
  have htS : t ∈ S := ⟨le_rfl, hlt⟩
  have hbdd : BddBelow S := ⟨0, fun s hs => by
      by_contra h
      push Not at h
      have := hs.2
      rw [hneg s h] at this
      linarith⟩
  set τ := sInf S with hτ
  have hτt : τ ≤ t := csInf_le hbdd htS
  have hIoc : Set.Ioc τ t ⊆ S := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    obtain ⟨s', hs'S, hs's⟩ := exists_lt_of_csInf_lt ⟨t, htS⟩ hs1
    exact ⟨hs2, lt_of_lt_of_le hs'S.2 (F.mono hs's.le)⟩
  have hlow : ∀ s < τ, F s ≤ a := by
    intro s hs
    have hns : s ∉ S := notMem_of_lt_csInf hs hbdd
    by_contra h
    push Not at h
    exact hns ⟨hs.le.trans hτt, h⟩
  by_cases hτS : τ ∈ S
  · have hIcc : Set.Icc τ t ⊆ S := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      rcases hs1.lt_or_eq with h | h
      · exact hIoc ⟨h, hs2⟩
      · rw [← h]; exact hτS
    have h0 : F.measure (Set.Icc τ t) = 0 := MeasureTheory.measure_mono_null hIcc hS0
    rw [StieltjesFunction.measure_Icc, ENNReal.ofReal_eq_zero] at h0
    have hll : Function.leftLim F τ ≤ a :=
      le_of_tendsto (F.mono.tendsto_leftLim τ)
        (eventually_nhdsWithin_of_forall (fun s hs => hlow s hs))
    linarith
  · have h0 : F.measure (Set.Ioc τ t) = 0 := MeasureTheory.measure_mono_null hIoc hS0
    rw [StieltjesFunction.measure_Ioc, ENNReal.ofReal_eq_zero] at h0
    have : F τ ≤ a := by
      by_contra h
      push Not at h
      exact hτS ⟨hτt, h⟩
    linarith

/-! ## colNorm facts -/

lemma colNorm_nonneg (M : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ colNorm M :=
  Real.iSup_nonneg (fun j => Finset.sum_nonneg (fun i _ => abs_nonneg (M i j)))

lemma col_le_colNorm (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    ∑ i, |M i j| ≤ colNorm M :=
  le_ciSup (f := fun j : Fin n => ∑ i, |M i j|) (Finite.bddAbove_range _) j

lemma colNorm_le_of (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ j, ∑ i, |M i j| ≤ c) : colNorm M ≤ c :=
  Real.iSup_le h hc

lemma double_sum_le (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∑ j, ∑ i, |M j i| * v i ≤ colNorm M * ∑ i, v i := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (col_le_colNorm M i) (hv i)

lemma colNorm_mul_le (A B : Matrix (Fin n) (Fin n) ℝ) :
    colNorm (A * B) ≤ colNorm A * colNorm B := by
  apply colNorm_le_of _ _ (mul_nonneg (colNorm_nonneg A) (colNorm_nonneg B))
  intro j
  calc ∑ i, |(A * B) i j| ≤ ∑ i, ∑ l, |A i l| * |B l j| := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [Matrix.mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl (fun l _ => abs_mul _ _)
    _ = ∑ l, |B l j| * ∑ i, |A i l| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ ≤ ∑ l, |B l j| * colNorm A := Finset.sum_le_sum (fun l _ =>
        mul_le_mul_of_nonneg_left (col_le_colNorm A l) (abs_nonneg _))
    _ = colNorm A * ∑ l, |B l j| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ colNorm A * colNorm B :=
        mul_le_mul_of_nonneg_left (col_le_colNorm B j) (colNorm_nonneg A)

lemma col_one (j : Fin n) : ∑ i, |(1 : Matrix (Fin n) (Fin n) ℝ) i j| = 1 := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma colNorm_one_le : colNorm (1 : Matrix (Fin n) (Fin n) ℝ) ≤ 1 :=
  colNorm_le_of _ _ zero_le_one (fun j => (col_one j).le)

lemma colNorm_pow_le (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    colNorm (A ^ m) ≤ colNorm A ^ m := by
  induction m with
  | zero => simpa using colNorm_one_le
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact (colNorm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (colNorm_nonneg A))

lemma powNonneg (Q : Matrix (Fin n) (Fin n) ℝ) (h : ∀ i j, 0 ≤ Q i j) (k : ℕ) :
    ∀ i j, 0 ≤ (Q ^ k) i j := by
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (h l j))

lemma colNorm_Q_le_one (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsTransientSubstochasticT Q) :
    colNorm Q ≤ 1 := by
  apply colNorm_le_of _ _ zero_le_one
  intro j
  calc ∑ i, |Q i j| = ∑ i, Q i j :=
        Finset.sum_congr rfl (fun i _ => abs_of_nonneg (hQ.nonneg i j))
    _ ≤ 1 := hQ.colSum_le_one j

lemma colNorm_pow_le_one (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsTransientSubstochasticT Q)
    (k : ℕ) : colNorm (Q ^ k) ≤ 1 :=
  (colNorm_pow_le Q k).trans (pow_le_one₀ (colNorm_nonneg Q) (colNorm_Q_le_one Q hQ))

lemma colNorm_one_sub_le (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsTransientSubstochasticT Q) :
    colNorm (1 - Q) ≤ 2 := by
  apply colNorm_le_of _ _ (by norm_num)
  intro j
  calc ∑ i, |(1 - Q) i j| ≤ ∑ i, (|(1 : Matrix (Fin n) (Fin n) ℝ) i j| + Q i j) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [Matrix.sub_apply]
        have := hQ.nonneg i j
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg this])
    _ = ∑ i, |(1 : Matrix (Fin n) (Fin n) ℝ) i j| + ∑ i, Q i j := Finset.sum_add_distrib
    _ ≤ 2 := by rw [col_one]; linarith [hQ.colSum_le_one j]

/-! ## Gamma < 1 (copied from our accepted sibling c568f359) -/

noncomputable def s (Q : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (j : Fin n) : ℝ :=
  ∑ i, (Q ^ k) i j

lemma s_succ (Q : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (j : Fin n) :
    s Q (k + 1) j = ∑ i, s Q k i * Q i j := by
  unfold s
  simp only [pow_succ, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma s_zero (Q : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : s Q 0 j = 1 := by
  simp [s, Matrix.one_apply]

lemma s_le_one (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (k : ℕ) :
    ∀ j, s Q k j ≤ 1 := by
  induction k with
  | zero => intro j; rw [s_zero]
  | succ k ih =>
    intro j
    rw [s_succ]
    calc ∑ i, s Q k i * Q i j ≤ ∑ i, Q i j := Finset.sum_le_sum (fun i _ => by
          have := hQ.nonneg i j
          have := ih i
          nlinarith)
      _ ≤ 1 := hQ.colSum_le_one j

noncomputable def A (Q : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => s Q k j = 1)

noncomputable def Fs (Q : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∑ i, Q i j = 1 ∧ ∀ i, 0 < Q i j → i ∈ S)

lemma mem_A (Q : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (j : Fin n) :
    j ∈ A Q k ↔ s Q k j = 1 := by
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]

lemma A_succ (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (k : ℕ) :
    A Q (k + 1) = Fs Q (A Q k) := by
  ext j
  simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and, mem_A]
  rw [s_succ]
  constructor
  · intro h
    have hle : ∑ i, s Q k i * Q i j ≤ ∑ i, Q i j := Finset.sum_le_sum (fun i _ => by
          have := hQ.nonneg i j
          have := s_le_one Q hQ k i
          nlinarith)
    have h1 : ∑ i, Q i j = 1 := le_antisymm (hQ.colSum_le_one j) (h ▸ hle)
    have h2 : ∑ i, (1 - s Q k i) * Q i j = 0 := by
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
      linarith
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg
      (by linarith [s_le_one Q hQ k i]) (hQ.nonneg i j))).1 h2
    refine ⟨h1, fun i hi => ?_⟩
    have := h3 i (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h4 | h4
    · linarith
    · exact absurd h4 hi.ne'
  · rintro ⟨h1, h2⟩
    rw [← h1]
    apply Finset.sum_congr rfl
    intro i _
    rcases (hQ.nonneg i j).lt_or_eq with hp | hp
    · rw [h2 i hp, one_mul]
    · rw [← hp, mul_zero]

lemma Fs_mono (Q : Matrix (Fin n) (Fin n) ℝ) {S T : Finset (Fin n)} (h : S ⊆ T) :
    Fs Q S ⊆ Fs Q T := by
  intro j hj
  simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨hj.1, fun i hi => h (hj.2 i hi)⟩

lemma A_anti (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (k : ℕ) :
    A Q (k + 1) ⊆ A Q k := by
  induction k with
  | zero =>
    intro j _
    rw [mem_A, s_zero]
  | succ k ih =>
    calc A Q (k + 1 + 1) = Fs Q (A Q (k + 1)) := A_succ Q hQ (k + 1)
      _ ⊆ Fs Q (A Q k) := Fs_mono Q ih
      _ = A Q (k + 1) := (A_succ Q hQ k).symm

lemma A_stable (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (k : ℕ)
    (hk : A Q (k + 1) = A Q k) : ∀ m, A Q (k + m) = A Q k := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, A_succ Q hQ, ih, ← A_succ Q hQ, hk]

lemma s_tendsto (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (j : Fin n) :
    Tendsto (fun k => s Q k j) atTop (𝓝 0) := by
  have hij : ∀ i, Tendsto (fun k : ℕ => (Q ^ k) i j) atTop (𝓝 0) := by
    intro i
    have := ((continuous_id.matrix_elem i j).tendsto (0 : Matrix (Fin n) (Fin n) ℝ)).comp
      hQ.pow_tendsto_zero
    simpa [Function.comp_def] using this
  have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ => hij i)
  simpa [s] using this

lemma card_bound (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q)
    (hall : ∀ k < n, A Q (k + 1) ≠ A Q k) : ∀ k ≤ n, (A Q k).card + k ≤ n := by
  intro k
  induction k with
  | zero =>
    intro _
    have := Finset.card_le_univ (A Q 0)
    simpa using this
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hss : A Q (k + 1) ⊂ A Q k :=
      Finset.ssubset_iff_subset_ne.2 ⟨A_anti Q hQ k, hall k (by omega)⟩
    have := Finset.card_lt_card hss
    omega

lemma A_n_empty (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) : A Q n = ∅ := by
  by_contra hne
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hex : ∃ k < n, A Q (k + 1) = A Q k := by
    by_contra hall
    push Not at hall
    have := card_bound Q hQ hall n le_rfl
    have h0 : (A Q n).card = 0 := by omega
    rw [Finset.card_eq_zero] at h0
    exact hne h0
  obtain ⟨k, hkn, hk⟩ := hex
  have hst := A_stable Q hQ k hk
  have hAn : A Q n = A Q k := by
    have := hst (n - k)
    rwa [Nat.add_sub_cancel' hkn.le] at this
  have hev : ∀ m ≥ n, s Q m j = 1 := by
    intro m hm
    have := hst (m - k)
    rw [Nat.add_sub_cancel' (by omega)] at this
    rw [← mem_A, this, ← hAn]
    exact hj
  have ht := s_tendsto Q hQ j
  have ht1 : Tendsto (fun k => s Q k j) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop n] with m hm
      exact (hev m hm).symm)
  have := tendsto_nhds_unique ht ht1
  norm_num at this

lemma gamma_lt_one (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) :
    colNorm (Q ^ n) < 1 := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · simp [colNorm, Real.iSup_of_isEmpty]
  · obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j : Fin n => ∑ i, |(Q ^ n) i j|)
    unfold colNorm
    rw [← hj]
    have he : ∑ i, |(Q ^ n) i j| = s Q n j := by
      unfold s
      exact Finset.sum_congr rfl (fun i _ =>
        abs_of_nonneg (powNonneg Q hQ.nonneg n i j))
    rw [he]
    refine lt_of_le_of_ne (s_le_one Q hQ n j) (fun h1 => ?_)
    have hm : j ∈ A Q n := (mem_A Q n j).2 h1
    rw [A_n_empty Q hQ] at hm
    simp at hm

/-! ## Geometric bound for ∑ colNorm (Q^k) -/

lemma partial_le (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsTransientSubstochasticT Q) (m : ℕ) :
    ∑ k ∈ Finset.range (n * m), colNorm (Q ^ k)
      ≤ n * ∑ i ∈ Finset.range m, colNorm (Q ^ n) ^ i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, mul_add]
    have h2 : ∑ x ∈ Finset.range n, colNorm (Q ^ (n * m + x)) ≤ n * colNorm (Q ^ n) ^ m := by
      calc ∑ x ∈ Finset.range n, colNorm (Q ^ (n * m + x))
          ≤ ∑ x ∈ Finset.range n, colNorm (Q ^ n) ^ m := by
            refine Finset.sum_le_sum (fun x _ => ?_)
            rw [pow_add, pow_mul]
            calc colNorm ((Q ^ n) ^ m * Q ^ x) ≤ colNorm ((Q ^ n) ^ m) * colNorm (Q ^ x) :=
                  colNorm_mul_le _ _
              _ ≤ colNorm (Q ^ n) ^ m * 1 :=
                  mul_le_mul (colNorm_pow_le _ m) (colNorm_pow_le_one Q hQ x)
                    (colNorm_nonneg _) (pow_nonneg (colNorm_nonneg _) m)
              _ = colNorm (Q ^ n) ^ m := mul_one _
        _ = n * colNorm (Q ^ n) ^ m := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith

lemma summable_and_bound (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsTransientSubstochasticT Q)
    (hn : 1 ≤ n) :
    Summable (fun k : ℕ => colNorm (Q ^ k)) ∧
      ∑' k : ℕ, colNorm (Q ^ k) ≤ (n : ℝ) / (1 - colNorm (Q ^ n)) := by
  have hγ := gamma_lt_one Q hQ
  have hγ0 := colNorm_nonneg (Q ^ n)
  have hbound : ∀ N, ∑ k ∈ Finset.range N, colNorm (Q ^ k) ≤ (n : ℝ) / (1 - colNorm (Q ^ n)) := by
    intro N
    have hsub : ∑ k ∈ Finset.range N, colNorm (Q ^ k) ≤ ∑ k ∈ Finset.range (n * N), colNorm (Q ^ k) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by nlinarith))
        (fun k _ _ => colNorm_nonneg _)
    have hgeo : ∑ i ∈ Finset.range N, colNorm (Q ^ n) ^ i ≤ (1 - colNorm (Q ^ n))⁻¹ := by
      rw [← tsum_geometric_of_lt_one hγ0 hγ]
      exact (summable_geometric_of_lt_one hγ0 hγ).sum_le_tsum _
        (fun i _ => pow_nonneg hγ0 i)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc ∑ k ∈ Finset.range N, colNorm (Q ^ k) ≤ n * ∑ i ∈ Finset.range N, colNorm (Q ^ n) ^ i :=
          hsub.trans (partial_le Q hQ N)
      _ ≤ n * (1 - colNorm (Q ^ n))⁻¹ := mul_le_mul_of_nonneg_left hgeo hn0
      _ = (n : ℝ) / (1 - colNorm (Q ^ n)) := (div_eq_mul_inv _ _).symm
  exact ⟨summable_of_sum_range_le (fun k => colNorm_nonneg _) hbound,
    Real.tsum_le_of_sum_range_le (fun k => colNorm_nonneg _) hbound⟩

/-! ## Neumann series -/

noncomputable def NN (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑' k : ℕ, (Q ^ k) i j

lemma entry_summable (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsTransientSubstochasticT Q)
    (hn : 1 ≤ n) (i j : Fin n) : Summable (fun k : ℕ => (Q ^ k) i j) := by
  refine Summable.of_nonneg_of_le (fun k => powNonneg Q hQ.nonneg k i j) (fun k => ?_)
    (summable_and_bound Q hQ hn).1
  calc (Q ^ k) i j = |(Q ^ k) i j| := (abs_of_nonneg (powNonneg Q hQ.nonneg k i j)).symm
    _ ≤ ∑ l, |(Q ^ k) l j| :=
        Finset.single_le_sum (f := fun l => |(Q ^ k) l j|) (fun l _ => abs_nonneg _)
          (Finset.mem_univ i)
    _ ≤ colNorm (Q ^ k) := col_le_colNorm _ j

lemma neumann_left (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsTransientSubstochasticT Q)
    (hn : 1 ≤ n) : NN Q * (1 - Q) = 1 := by
  have hs := entry_summable Q hQ hn
  ext i j
  have h1 : (NN Q * Q) i j = ∑' k : ℕ, (Q ^ (k + 1)) i j := by
    simp only [Matrix.mul_apply, NN, Matrix.of_apply]
    simp_rw [← tsum_mul_right]
    rw [← Summable.tsum_finsetSum (fun l _ => (hs i l).mul_right (Q l j))]
    congr 1
  have h0 : NN Q i j = (Q ^ 0) i j + ∑' k : ℕ, (Q ^ (k + 1)) i j := by
    simp only [NN, Matrix.of_apply]
    exact (hs i j).tsum_eq_zero_add
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, h1, h0, pow_zero]
  ring

lemma NN_nonneg (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsTransientSubstochasticT Q) (i j : Fin n) :
    0 ≤ NN Q i j :=
  tsum_nonneg (fun k => powNonneg Q hQ.nonneg k i j)

lemma colNorm_NN_le (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsTransientSubstochasticT Q)
    (hn : 1 ≤ n) : colNorm (NN Q) ≤ ∑' k : ℕ, colNorm (Q ^ k) := by
  have hs := entry_summable Q hQ hn
  have hsum := (summable_and_bound Q hQ hn).1
  apply colNorm_le_of _ _ (tsum_nonneg (fun k => colNorm_nonneg _))
  intro j
  calc ∑ i, |NN Q i j| = ∑ i, ∑' k : ℕ, (Q ^ k) i j :=
        Finset.sum_congr rfl (fun i _ => abs_of_nonneg (NN_nonneg Q hQ i j))
    _ = ∑' k : ℕ, ∑ i, (Q ^ k) i j :=
        (Summable.tsum_finsetSum (fun i _ => hs i j)).symm
    _ ≤ ∑' k : ℕ, colNorm (Q ^ k) := by
        refine Summable.tsum_le_tsum (fun k => ?_) (summable_sum (fun i _ => hs i j)) hsum
        calc ∑ i, (Q ^ k) i j = ∑ i, |(Q ^ k) i j| :=
              Finset.sum_congr rfl (fun i _ => (abs_of_nonneg (powNonneg Q hQ.nonneg k i j)).symm)
          _ ≤ colNorm (Q ^ k) := col_le_colNorm _ j

lemma le_inv_mulVec (Q N : Matrix (Fin n) (Fin n) ℝ) (hinv : N * (1 - Q) = 1)
    (hN : ∀ i j, 0 ≤ N i j) (v w : Fin n → ℝ) (h : ∀ j, v j ≤ (Q *ᵥ v) j + w j) :
    ∀ j, v j ≤ (N *ᵥ w) j := by
  have h1 : ∀ j, ((1 - Q) *ᵥ v) j ≤ w j := by
    intro j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    linarith [h j]
  have hv : v = N *ᵥ ((1 - Q) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  intro j
  rw [hv]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h1 i) (hN j i))

/-! ## sup-vector facts -/

lemma bound_of_bdd {x : ℝ → Fin n → ℝ} {T : ℝ} (h : Bornology.IsBounded (x '' Set.Icc 0 T)) :
    ∃ C, ∀ s ∈ Set.Icc (0:ℝ) T, ∀ j, |x s j| ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 h
  refine ⟨C, fun s hs j => ?_⟩
  have h1 := norm_le_pi_norm (x s) j
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (hC _ (Set.mem_image_of_mem x hs))

lemma diff_bound {a b : ℝ → Fin n → ℝ} {T : ℝ} (ha : Bornology.IsBounded (a '' Set.Icc 0 T))
    (hb : Bornology.IsBounded (b '' Set.Icc 0 T)) :
    ∃ C, ∀ s ∈ Set.Icc (0:ℝ) T, ∀ j, |(a - b) s j| ≤ C := by
  obtain ⟨Ca, hCa⟩ := bound_of_bdd ha
  obtain ⟨Cb, hCb⟩ := bound_of_bdd hb
  refine ⟨Ca + Cb, fun s hs j => ?_⟩
  have h1 := hCa s hs j
  have h2 := hCb s hs j
  show |a s j - b s j| ≤ Ca + Cb
  rw [abs_le]
  constructor <;>
    linarith [neg_abs_le (a s j), le_abs_self (a s j), neg_abs_le (b s j), le_abs_self (b s j)]

lemma le_supVec {d : ℝ → Fin n → ℝ} {T C : ℝ} (hC : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ j, |d s j| ≤ C)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) (j : Fin n) : |d s j| ≤ supVec T d j := by
  unfold supVec
  exact le_ciSup (f := fun t : Set.Icc (0:ℝ) T => |d t j|)
    ⟨C, by rintro _ ⟨t, rfl⟩; exact hC t t.2 j⟩ ⟨s, hs⟩

lemma supVec_nonneg (d : ℝ → Fin n → ℝ) (T : ℝ) (j : Fin n) : 0 ≤ supVec T d j :=
  Real.iSup_nonneg (fun _ => abs_nonneg _)

lemma supVec_le {d : ℝ → Fin n → ℝ} {T : ℝ} {c : Fin n → ℝ} (hc : ∀ j, 0 ≤ c j)
    (h : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ j, |d s j| ≤ c j) (j : Fin n) : supVec T d j ≤ c j :=
  Real.iSup_le (fun t => h t t.2 j) (hc j)

lemma mulVec_abs_le (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) (h : ∀ i, |a i| ≤ b i)
    (j : Fin n) : |(M *ᵥ a) j| ≤ ∑ i, |M j i| * b i := by
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)

lemma l1_nonneg (v : Fin n → ℝ) : 0 ≤ l1 v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-! ## One-sided comparison -/

lemma one_side (Q : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (x₁ x₂ y₁ z₁ y₂ z₂ : ℝ → Fin n → ℝ)
    (h₁ : IsReflection Q T x₁ y₁ z₁) (h₂ : IsReflection Q T x₂ y₂ z₂)
    (c : Fin n → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hbound : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ j,
      (x₂ s j - x₁ s j) + ((Q *ᵥ y₁ s) j - (Q *ᵥ y₂ s) j) ≤ c j) :
    ∀ t ∈ Set.Icc (0:ℝ) T, ∀ j, y₁ t j - y₂ t j ≤ c j := by
  intro t ht j
  obtain ⟨F, hFy, hFneg, hFm⟩ := h₁.2.2.2 j
  have h0T : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hy2mono := h₂.2.2.1.1 j
  have hy20 : y₂ 0 j = 0 := by rw [h₂.2.2.1.2]; rfl
  have hy2t : 0 ≤ y₂ t j := by
    have := hy2mono h0T ht ht.1
    simp only at this
    linarith
  have key := stieltjes_key F T t (y₂ t j + c j) (fun s => 0 < z₁ s j) ht.2
    (by linarith [hc j]) hFneg hFm (by
      intro s hs0 hst hFs
      have hs : s ∈ Set.Icc (0:ℝ) T := ⟨hs0, hst.trans ht.2⟩
      rw [hFy s hs] at hFs
      have hz1 := (h₁.2.1 s hs).1
      have hz2 := (h₂.2.1 s hs).1
      have hz2nn := (h₂.2.1 s hs).2 j
      have e1 : z₁ s j = x₁ s j + y₁ s j - (Q *ᵥ y₁ s) j := by
        rw [hz1, Pi.add_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]; ring
      have e2 : z₂ s j = x₂ s j + y₂ s j - (Q *ᵥ y₂ s) j := by
        rw [hz2, Pi.add_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]; ring
      have hmono : y₂ s j ≤ y₂ t j := hy2mono hs ht hst
      have hb := hbound s hs j
      have hz2nn' : 0 ≤ z₂ s j := hz2nn
      show 0 < z₁ s j
      rw [e2] at hz2nn'
      rw [e1]
      linarith)
  rw [hFy t ht] at key
  linarith

end CW93Lip

open ChenWhitt93.Reflection Filter Topology Matrix in
theorem solution {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (T : ℝ) (x₁ x₂ y₁ z₁ y₂ z₂ : ℝ → Fin n → ℝ)
    (hx₁ : IsCadlagOn T x₁) (hx₂ : IsCadlagOn T x₂)
    (h₁ : IsReflection Q T x₁ y₁ z₁) (h₂ : IsReflection Q T x₂ y₂ z₂) :
    -- (2.9)
    supVec T (y₁ - y₂) ≤ (1 - Q)⁻¹ *ᵥ supVec T (x₁ - x₂) ∧
    -- (2.10)
    sumSupNorm T (y₁ - y₂) ≤ colNorm (1 - Q)⁻¹ * sumSupNorm T (x₁ - x₂) ∧
    Summable (fun k : ℕ => colNorm (Q ^ k)) ∧
    colNorm (1 - Q)⁻¹ * sumSupNorm T (x₁ - x₂)
        ≤ (∑' k : ℕ, colNorm (Q ^ k)) * sumSupNorm T (x₁ - x₂) ∧
    (∑' k : ℕ, colNorm (Q ^ k)) * sumSupNorm T (x₁ - x₂)
        ≤ (n : ℝ) / (1 - colNorm (Q ^ n)) * sumSupNorm T (x₁ - x₂) ∧
    -- (2.11)
    sumSupNorm T (z₁ - z₂)
        ≤ (1 + colNorm (1 - Q) * colNorm (1 - Q)⁻¹) * sumSupNorm T (x₁ - x₂) ∧
    (1 + colNorm (1 - Q) * colNorm (1 - Q)⁻¹) * sumSupNorm T (x₁ - x₂)
        ≤ (1 + 2 * (n : ℝ) / (1 - colNorm (Q ^ n))) * sumSupNorm T (x₁ - x₂) := by
  open CW93Lip in
  focus
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hl : ∀ x : ℝ → Fin 0 → ℝ, sumSupNorm T x = 0 := by
        intro x; simp [sumSupNorm, l1]
      have hc : ∀ M : Matrix (Fin 0) (Fin 0) ℝ, colNorm M = 0 := by
        intro M; simp [colNorm, Real.iSup_of_isEmpty]
      refine ⟨fun j => j.elim0, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hl, hc]
    have hn1 : 1 ≤ n := hn
    have hinvL := neumann_left Q hQ hn1
    have hinv : (1 - Q)⁻¹ = NN Q := Matrix.inv_eq_left_inv hinvL
    rw [hinv]
    obtain ⟨hsum, htsum⟩ := summable_and_bound Q hQ hn1
    have hγ := gamma_lt_one Q hQ
    set v := supVec T (y₁ - y₂) with hvdef
    set w := supVec T (x₁ - x₂) with hwdef
    obtain ⟨Cy, hCy⟩ := diff_bound h₁.1.2.2 h₂.1.2.2
    obtain ⟨Cx, hCx⟩ := diff_bound hx₁.2.2 hx₂.2.2
    have hv0 : ∀ j, 0 ≤ v j := supVec_nonneg _ _
    have hw0 : ∀ j, 0 ≤ w j := supVec_nonneg _ _
    have hX : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ j, |x₁ s j - x₂ s j| ≤ w j :=
      fun s hs j => le_supVec hCx hs j
    have hYv : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ i, |(y₁ s - y₂ s) i| ≤ v i :=
      fun s hs i => le_supVec hCy hs i
    have hY : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ j,
        |(Q *ᵥ y₁ s) j - (Q *ᵥ y₂ s) j| ≤ ∑ i, |Q j i| * v i := by
      intro s hs j
      rw [← Pi.sub_apply (Q *ᵥ y₁ s), ← Matrix.mulVec_sub]
      exact mulVec_abs_le Q _ v (hYv s hs) j
    set c : Fin n → ℝ := fun j => ∑ i, |Q j i| * v i + w j with hcdef
    have hc0 : ∀ j, 0 ≤ c j := fun j =>
      add_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hv0 i))) (hw0 j)
    have hA := one_side Q T x₁ x₂ y₁ z₁ y₂ z₂ h₁ h₂ c hc0 (by
      intro s hs j
      have a1 := hX s hs j
      have a2 := hY s hs j
      show _ ≤ ∑ i, |Q j i| * v i + w j
      rw [abs_le] at a1 a2
      linarith [a1.1, a2.2])
    have hB := one_side Q T x₂ x₁ y₂ z₂ y₁ z₁ h₂ h₁ c hc0 (by
      intro s hs j
      have a1 := hX s hs j
      have a2 := hY s hs j
      show _ ≤ ∑ i, |Q j i| * v i + w j
      rw [abs_le] at a1 a2
      linarith [a1.2, a2.1])
    have hvc : ∀ j, v j ≤ c j := supVec_le hc0 (by
      intro t ht j
      show |y₁ t j - y₂ t j| ≤ c j
      rw [abs_sub_le_iff]
      exact ⟨hA t ht j, hB t ht j⟩)
    have hQv : ∀ j, ∑ i, |Q j i| * v i = (Q *ᵥ v) j := by
      intro j
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun i _ => by rw [abs_of_nonneg (hQ.nonneg j i)])
    have h29 : ∀ j, v j ≤ (NN Q *ᵥ w) j :=
      le_inv_mulVec Q (NN Q) hinvL (NN_nonneg Q hQ) v w (fun j => by
        have := hvc j
        simp only [hcdef] at this
        rw [hQv j] at this
        exact this)
    -- (2.10a)
    have h210 : l1 v ≤ colNorm (NN Q) * l1 w := by
      calc l1 v = ∑ j, v j := Finset.sum_congr rfl (fun j _ => abs_of_nonneg (hv0 j))
        _ ≤ ∑ j, ∑ i, |NN Q j i| * |w i| := Finset.sum_le_sum (fun j _ =>
            (h29 j).trans ((le_abs_self _).trans (mulVec_abs_le _ w _ (fun i => le_rfl) j)))
        _ ≤ colNorm (NN Q) * ∑ i, |w i| := double_sum_le _ _ (fun i => abs_nonneg _)
        _ = colNorm (NN Q) * l1 w := rfl
    have hS0 : 0 ≤ l1 w := l1_nonneg w
    have hNN := colNorm_NN_le Q hQ hn1
    have hNNb : colNorm (NN Q) ≤ (n : ℝ) / (1 - colNorm (Q ^ n)) := hNN.trans htsum
    -- (2.11a)
    have hZ : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ j,
        |(z₁ - z₂) s j| ≤ w j + ∑ i, |(1 - Q) j i| * v i := by
      intro s hs j
      have hz1 := (h₁.2.1 s hs).1
      have hz2 := (h₂.2.1 s hs).1
      have e : (z₁ - z₂) s j = (x₁ s j - x₂ s j) + ((1 - Q) *ᵥ (y₁ s - y₂ s)) j := by
        rw [Pi.sub_apply, hz1, hz2, Matrix.mulVec_sub]
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      rw [e]
      have a1 := hX s hs j
      have a2 := mulVec_abs_le (1 - Q) _ v (hYv s hs) j
      rw [abs_le] at a1 ⊢
      constructor <;>
        linarith [a1.1, a1.2, neg_abs_le (((1 - Q) *ᵥ (y₁ s - y₂ s)) j),
          le_abs_self (((1 - Q) *ᵥ (y₁ s - y₂ s)) j)]
    have hu : ∀ j, supVec T (z₁ - z₂) j ≤ w j + ∑ i, |(1 - Q) j i| * v i :=
      supVec_le (fun j => add_nonneg (hw0 j)
        (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hv0 i)))) hZ
    have h211 : sumSupNorm T (z₁ - z₂) ≤ l1 w + colNorm (1 - Q) * l1 v := by
      calc sumSupNorm T (z₁ - z₂) = ∑ j, supVec T (z₁ - z₂) j := by
            unfold sumSupNorm l1
            exact Finset.sum_congr rfl (fun j _ => abs_of_nonneg (supVec_nonneg _ _ j))
        _ ≤ ∑ j, (w j + ∑ i, |(1 - Q) j i| * v i) := Finset.sum_le_sum (fun j _ => hu j)
        _ = ∑ j, w j + ∑ j, ∑ i, |(1 - Q) j i| * v i := Finset.sum_add_distrib
        _ ≤ l1 w + colNorm (1 - Q) * ∑ i, v i := by
            have e1 : ∑ j, w j = l1 w :=
              Finset.sum_congr rfl (fun j _ => (abs_of_nonneg (hw0 j)).symm)
            rw [e1]
            linarith [double_sum_le (1 - Q) v hv0]
        _ = l1 w + colNorm (1 - Q) * l1 v := by
            congr 2
            exact Finset.sum_congr rfl (fun j _ => (abs_of_nonneg (hv0 j)).symm)
    have hD := colNorm_one_sub_le Q hQ
    have hDn := colNorm_nonneg (1 - Q)
    have hNn := colNorm_nonneg (NN Q)
    refine ⟨fun j => h29 j, h210, hsum, ?_, ?_, ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_right hNN hS0
    · exact mul_le_mul_of_nonneg_right htsum hS0
    · have := mul_le_mul_of_nonneg_left h210 hDn
      show sumSupNorm T (z₁ - z₂) ≤ (1 + colNorm (1 - Q) * colNorm (NN Q)) * l1 w
      nlinarith
    · show (1 + colNorm (1 - Q) * colNorm (NN Q)) * l1 w
          ≤ (1 + 2 * (n : ℝ) / (1 - colNorm (Q ^ n))) * l1 w
      apply mul_le_mul_of_nonneg_right _ hS0
      have hm : colNorm (1 - Q) * colNorm (NN Q) ≤ 2 * ((n : ℝ) / (1 - colNorm (Q ^ n))) :=
        mul_le_mul hD hNNb hNn (by norm_num)
      rw [mul_div_assoc]
      linarith
