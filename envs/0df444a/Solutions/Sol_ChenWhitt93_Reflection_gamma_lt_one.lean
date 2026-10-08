-- Prove2me | solution 1 for ChenWhitt93.Reflection.gamma_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:36:36.458686+00:00
-- url     : https://prove2.me/submissions/4331cf4a-a94a-44ea-b0ec-9e960ba44897

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

set_option autoImplicit false

open Filter Topology Matrix

namespace ChenWhitt93GammaAux

variable {n : ℕ}

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
    (hQ : ChenWhitt93.Reflection.IsTransientSubstochasticT Q) (k : ℕ) :
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

noncomputable def F (Q : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∑ i, Q i j = 1 ∧ ∀ i, 0 < Q i j → i ∈ S)

lemma mem_A (Q : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (j : Fin n) :
    j ∈ A Q k ↔ s Q k j = 1 := by
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]

lemma A_succ (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ChenWhitt93.Reflection.IsTransientSubstochasticT Q) (k : ℕ) :
    A Q (k + 1) = F Q (A Q k) := by
  ext j
  simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, mem_A]
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

lemma F_mono (Q : Matrix (Fin n) (Fin n) ℝ) {S T : Finset (Fin n)} (h : S ⊆ T) :
    F Q S ⊆ F Q T := by
  intro j hj
  simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨hj.1, fun i hi => h (hj.2 i hi)⟩

lemma A_anti (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ChenWhitt93.Reflection.IsTransientSubstochasticT Q) (k : ℕ) :
    A Q (k + 1) ⊆ A Q k := by
  induction k with
  | zero =>
    intro j _
    rw [mem_A, s_zero]
  | succ k ih =>
    calc A Q (k + 1 + 1) = F Q (A Q (k + 1)) := A_succ Q hQ (k + 1)
      _ ⊆ F Q (A Q k) := F_mono Q ih
      _ = A Q (k + 1) := (A_succ Q hQ k).symm

lemma A_stable (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ChenWhitt93.Reflection.IsTransientSubstochasticT Q) (k : ℕ)
    (hk : A Q (k + 1) = A Q k) : ∀ m, A Q (k + m) = A Q k := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, A_succ Q hQ, ih, ← A_succ Q hQ, hk]

lemma s_tendsto (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ChenWhitt93.Reflection.IsTransientSubstochasticT Q) (j : Fin n) :
    Tendsto (fun k => s Q k j) atTop (𝓝 0) := by
  have hij : ∀ i, Tendsto (fun k : ℕ => (Q ^ k) i j) atTop (𝓝 0) := by
    intro i
    have := ((continuous_id.matrix_elem i j).tendsto (0 : Matrix (Fin n) (Fin n) ℝ)).comp
      hQ.pow_tendsto_zero
    simpa [Function.comp_def] using this
  have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ => hij i)
  simpa [s] using this

lemma card_bound (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ChenWhitt93.Reflection.IsTransientSubstochasticT Q)
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
    (hQ : ChenWhitt93.Reflection.IsTransientSubstochasticT Q) : A Q n = ∅ := by
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

end ChenWhitt93GammaAux

open ChenWhitt93.Reflection in
theorem solution {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) :
    colNorm (Q ^ n) < 1 := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · simp [colNorm, Real.iSup_of_isEmpty]
  · obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j : Fin n => ∑ i, |(Q ^ n) i j|)
    unfold colNorm
    rw [← hj]
    have he : ∑ i, |(Q ^ n) i j| = ChenWhitt93GammaAux.s Q n j := by
      unfold ChenWhitt93GammaAux.s
      exact Finset.sum_congr rfl (fun i _ =>
        abs_of_nonneg (ChenWhitt93GammaAux.powNonneg Q hQ.nonneg n i j))
    rw [he]
    refine lt_of_le_of_ne (ChenWhitt93GammaAux.s_le_one Q hQ n j) (fun h1 => ?_)
    have hm : j ∈ ChenWhitt93GammaAux.A Q n := (ChenWhitt93GammaAux.mem_A Q n j).2 h1
    rw [ChenWhitt93GammaAux.A_n_empty Q hQ] at hm
    simp at hm
