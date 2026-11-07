-- Prove2me | solution 1 for DaiWeissFluid.LuKumar.scaled_cycles
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:03:11.666277+00:00
-- url     : https://prove2.me/submissions/a3828b9c-b870-4ae1-800c-8cc18b6da0ee

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace LKScaledAux

/-- `ramp p q u` = length of `[p, q] ∩ (-∞, u]` (for `p ≤ q`). -/
noncomputable def ramp (p q u : ℝ) : ℝ := min (max u p) q - p

lemma ramp_of_le {p q u : ℝ} (hpq : p ≤ q) (hu : u ≤ p) : ramp p q u = 0 := by
  unfold ramp; rw [max_eq_right hu, min_eq_left hpq]; ring

lemma ramp_of_ge {p q u : ℝ} (hpq : p ≤ q) (hu : q ≤ u) : ramp p q u = q - p := by
  unfold ramp; rw [max_eq_left (hpq.trans hu), min_eq_right hu]

lemma ramp_of_mem {p q u : ℝ} (hp : p ≤ u) (hq : u ≤ q) : ramp p q u = u - p := by
  unfold ramp; rw [max_eq_left hp, min_eq_left hq]

lemma ramp_mono (p q : ℝ) : Monotone (ramp p q) := by
  intro a b hab
  unfold ramp
  have := min_le_min_right q (max_le_max hab (le_refl p))
  linarith

lemma ramp_add {p q r u : ℝ} (hpq : p ≤ q) (hqr : q ≤ r) :
    ramp p q u + ramp q r u = ramp p r u := by
  rcases le_total u p with h | h
  · rw [ramp_of_le hpq h, ramp_of_le hqr (h.trans hpq), ramp_of_le (hpq.trans hqr) h]; ring
  rcases le_total u q with h' | h'
  · rw [ramp_of_mem h h', ramp_of_le hqr h', ramp_of_mem h (h'.trans hqr)]; ring
  rcases le_total u r with h'' | h''
  · rw [ramp_of_ge hpq h', ramp_of_mem h' h'', ramp_of_mem h h'']; ring
  · rw [ramp_of_ge hpq h', ramp_of_ge hqr h'', ramp_of_ge (hpq.trans hqr) h'']; ring

/-- cycle start times -/
noncomputable def sT (r τ : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, r ^ j * τ

/-- number of cycles to sum -/
noncomputable def NT (τ t : ℝ) : ℕ := ⌈t / τ⌉₊ + 1

/-- The self-similar concatenation of a one-cycle function `g`. -/
noncomputable def Φ (r τ : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (NT τ t), r ^ j * g ((t - sT r τ j) / r ^ j)

section
variable {r τ : ℝ} (hr : 1 ≤ r) (hτ : 0 < τ)
include hr hτ

lemma sT_succ (n : ℕ) : sT r τ (n + 1) = sT r τ n + r ^ n * τ := by
  simp [sT, Finset.sum_range_succ]

lemma sT_ge (n : ℕ) : n * τ ≤ sT r τ n := by
  induction n with
  | zero => simp [sT]
  | succ n ih =>
    rw [sT_succ hr hτ]
    have : τ ≤ r ^ n * τ := le_mul_of_one_le_left hτ.le (one_le_pow₀ hr)
    push_cast; linarith

lemma sT_mono : Monotone (sT r τ) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [sT_succ hr hτ]
  have : 0 < r ^ n * τ := mul_pos (pow_pos (by linarith) n) hτ
  linarith

lemma lt_sT_NT (t : ℝ) {j : ℕ} (hj : NT τ t ≤ j) : t < sT r τ j := by
  have h1 : (j : ℝ) * τ ≤ sT r τ j := sT_ge hr hτ j
  have h2 : t / τ < (j : ℝ) := by
    have := Nat.le_ceil (t / τ)
    have : ((NT τ t : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
    simp [NT] at this
    linarith
  rw [div_lt_iff₀ hτ] at h2
  linarith

lemma sum_eq_of_vanish (g : ℝ → ℝ) (hg0 : ∀ u, u ≤ 0 → g u = 0) (t : ℝ) (M M' : ℕ)
    (hM : M' ≤ M) (hvan : ∀ j, M' ≤ j → t ≤ sT r τ j) :
    ∑ j ∈ Finset.range M, r ^ j * g ((t - sT r τ j) / r ^ j) =
      ∑ j ∈ Finset.range M', r ^ j * g ((t - sT r τ j) / r ^ j) := by
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hM ih =>
    rw [Finset.sum_range_succ, ih]
    have : g ((t - sT r τ M) / r ^ M) = 0 := by
      apply hg0
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith [hvan M hM]
      · exact (pow_pos (by linarith) M).le
    rw [this]; ring

lemma Φ_eq_sum (g : ℝ → ℝ) (hg0 : ∀ u, u ≤ 0 → g u = 0) (t : ℝ) (M : ℕ)
    (hvan : ∀ j, M ≤ j → t ≤ sT r τ j) :
    Φ r τ g t = ∑ j ∈ Finset.range M, r ^ j * g ((t - sT r τ j) / r ^ j) := by
  unfold Φ
  rw [← sum_eq_of_vanish hr hτ g hg0 t (max (NT τ t) M) (NT τ t) (le_max_left _ _)
      (fun j hj => (lt_sT_NT hr hτ t hj).le),
    sum_eq_of_vanish hr hτ g hg0 t (max (NT τ t) M) M (le_max_right _ _) hvan]

lemma Φ_piece (g : ℝ → ℝ) (hg0 : ∀ u, u ≤ 0 → g u = 0) (hg1 : ∀ u, τ ≤ u → g u = g τ)
    (n : ℕ) (t : ℝ) (h1 : sT r τ n ≤ t) (h2 : t ≤ sT r τ (n + 1)) :
    Φ r τ g t = (∑ j ∈ Finset.range n, r ^ j) * g τ + r ^ n * g ((t - sT r τ n) / r ^ n) := by
  rw [Φ_eq_sum hr hτ g hg0 t (n + 1) (fun j hj => h2.trans (sT_mono hr hτ hj)),
    Finset.sum_range_succ, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [hg1]
  have hrj : 0 < r ^ j := pow_pos (by linarith) j
  rw [le_div_iff₀ hrj]
  have := sT_mono hr hτ (show j + 1 ≤ n by omega)
  rw [sT_succ hr hτ] at this
  linarith

lemma exists_piece (t : ℝ) (ht : 0 ≤ t) : ∃ n, sT r τ n ≤ t ∧ t ≤ sT r τ (n + 1) := by
  have hex : ∃ n, t < sT r τ (n + 1) := ⟨NT τ t, lt_sT_NT hr hτ t (by omega)⟩
  classical
  refine ⟨Nat.find hex, ?_, (Nat.find_spec hex).le⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; simpa [sT] using ht
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
    exact not_lt.1 this

lemma Φ_mono (g : ℝ → ℝ) (hg0 : ∀ u, u ≤ 0 → g u = 0) (hmono : Monotone g) :
    Monotone (Φ r τ g) := by
  intro a b hab
  let M := max (NT τ a) (NT τ b)
  rw [Φ_eq_sum hr hτ g hg0 a M (fun j hj => (lt_sT_NT hr hτ a (le_trans (le_max_left _ _) hj)).le),
    Φ_eq_sum hr hτ g hg0 b M (fun j hj => (lt_sT_NT hr hτ b (le_trans (le_max_right _ _) hj)).le)]
  apply Finset.sum_le_sum
  intro j _
  have hrj : 0 < r ^ j := pow_pos (by linarith) j
  apply mul_le_mul_of_nonneg_left _ hrj.le
  apply hmono
  apply div_le_div_of_nonneg_right _ hrj.le
  linarith

lemma Φ_const_ramp (c p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (a b : ℝ) (hab : a ≤ b)
    (havoid : ∀ j : ℕ, ∀ u ∈ Set.Icc a b,
      ¬ (sT r τ j + r ^ j * p ≤ u ∧ u ≤ sT r τ j + r ^ j * q)) :
    Φ r τ (fun u => c * ramp p q u) b = Φ r τ (fun u => c * ramp p q u) a := by
  have hg0 : ∀ u, u ≤ 0 → c * ramp p q u = 0 := fun u hu => by
    rw [ramp_of_le hpq (hu.trans hp)]; ring
  let M := max (NT τ a) (NT τ b)
  rw [Φ_eq_sum hr hτ _ hg0 a M (fun j hj => (lt_sT_NT hr hτ a (le_trans (le_max_left _ _) hj)).le),
    Φ_eq_sum hr hτ _ hg0 b M (fun j hj => (lt_sT_NT hr hτ b (le_trans (le_max_right _ _) hj)).le)]
  apply Finset.sum_congr rfl
  intro j _
  have hrj : 0 < r ^ j := pow_pos (by linarith) j
  by_cases h1 : b < sT r τ j + r ^ j * p
  · have hb : (b - sT r τ j) / r ^ j ≤ p := by rw [div_le_iff₀ hrj]; linarith
    have ha : (a - sT r τ j) / r ^ j ≤ p := by rw [div_le_iff₀ hrj]; linarith
    rw [ramp_of_le hpq hb, ramp_of_le hpq ha]
  · push Not at h1
    by_cases h2 : sT r τ j + r ^ j * q < a
    · have hb : q ≤ (b - sT r τ j) / r ^ j := by rw [le_div_iff₀ hrj]; linarith
      have ha : q ≤ (a - sT r τ j) / r ^ j := by rw [le_div_iff₀ hrj]; linarith
      rw [ramp_of_ge hpq hb, ramp_of_ge hpq ha]
    · push Not at h2
      exfalso
      refine havoid j (max a (sT r τ j + r ^ j * p)) ⟨le_max_left _ _, max_le hab h1⟩ ⟨le_max_right _ _, ?_⟩
      apply max_le h2
      have : r ^ j * p ≤ r ^ j * q := mul_le_mul_of_nonneg_left hpq hrj.le
      linarith

end

lemma Φ_comb {r τ : ℝ} (a b : ℝ) (f g h : ℝ → ℝ) (H : ∀ u, h u = a * f u + b * g u) (t : ℝ) :
    Φ r τ h t = a * Φ r τ f t + b * Φ r τ g t := by
  unfold Φ
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [H]; ring

lemma Φ_ramp_id {r τ : ℝ} (hr : 1 ≤ r) (hτ : 0 < τ) (t : ℝ) (ht : 0 ≤ t) :
    Φ r τ (ramp 0 τ) t = t := by
  obtain ⟨n, h1, h2⟩ := exists_piece hr hτ t ht
  have hrn : 0 < r ^ n := pow_pos (by linarith) n
  rw [Φ_piece hr hτ (ramp 0 τ) (fun u hu => ramp_of_le hτ.le hu)
    (fun u hu => by rw [ramp_of_ge hτ.le hu, ramp_of_ge hτ.le le_rfl]) n t h1 h2,
    ramp_of_ge hτ.le le_rfl, ramp_of_mem]
  · rw [sT_succ hr hτ] at h2
    unfold sT at *
    field_simp
    rw [Finset.sum_mul]; ring
  · rw [le_div_iff₀ hrn]; linarith
  · rw [div_le_iff₀ hrn, sT_succ hr hτ] at *; linarith [sT_succ hr hτ n]

section Cycle
variable (m : Fin 4 → ℝ)

noncomputable def t1 : ℝ := m 0 / (1 - m 0)
noncomputable def t2 : ℝ := m 1 / (1 - m 1)
noncomputable def t3 : ℝ := t2 m + m 2 / (1 - m 1)
noncomputable def τ0 : ℝ := (m 1 + m 3) / (1 - m 1)
noncomputable def rr : ℝ := m 3 / (1 - m 1)

noncomputable def T1 (k : Fin 4) (u : ℝ) : ℝ :=
  (![ramp 0 (t1 m) u + m 0 * ramp (t1 m) (t2 m) u, ramp 0 (t2 m) u,
    ramp (t2 m) (t3 m) u, ramp (t2 m) (τ0 m) u] : Fin 4 → ℝ) k

noncomputable def Q1 (k : Fin 4) (u : ℝ) : ℝ :=
  (![1 + ramp 0 (τ0 m) u - (m 0)⁻¹ * T1 m 0 u, (m 0)⁻¹ * T1 m 0 u - (m 1)⁻¹ * T1 m 1 u,
    (m 1)⁻¹ * T1 m 1 u - (m 2)⁻¹ * T1 m 2 u, (m 2)⁻¹ * T1 m 2 u - (m 3)⁻¹ * T1 m 3 u] :
    Fin 4 → ℝ) k

structure Hyp : Prop where
  hm : ∀ k, 0 < m k
  h1 : m 0 + m 3 < 1
  h2 : m 1 + m 2 < 1
  h3 : 1 ≤ m 1 + m 3

variable {m}

lemma Hyp.order (H : Hyp m) :
    0 < t1 m ∧ t1 m ≤ t2 m ∧ t2 m ≤ t3 m ∧ t3 m ≤ τ0 m ∧ 1 ≤ rr m ∧ 0 < τ0 m ∧
    rr m = τ0 m - t2 m := by
  have a0 := H.hm 0; have a1 := H.hm 1; have a2 := H.hm 2; have a3 := H.hm 3
  have b0 : 0 < 1 - m 0 := by linarith [H.h1]
  have b1 : 0 < 1 - m 1 := by linarith [H.h2]
  unfold t3 τ0 rr t1 t2
  refine ⟨by positivity, ?_, ?_, ?_, ?_, by positivity, ?_⟩
  · rw [div_le_div_iff₀ b0 b1]; nlinarith [H.h1, H.h3]
  · have : 0 ≤ m 2 / (1 - m 1) := by positivity
    linarith
  · have : m 2 / (1 - m 1) ≤ m 3 / (1 - m 1) :=
      div_le_div_of_nonneg_right (by linarith [H.h2, H.h3]) b1.le
    rw [add_div]; linarith
  · rw [le_div_iff₀ b1]; linarith [H.h3]
  · field_simp; ring

lemma Hyp.ident (H : Hyp m) :
    (m 0)⁻¹ * t1 m = t1 m + 1 ∧ (m 1)⁻¹ * t2 m = t2 m + 1 ∧
    (m 2)⁻¹ * (t3 m - t2 m) = t2 m + 1 ∧ (m 3)⁻¹ * (τ0 m - t2 m) = t2 m + 1 ∧
    (m 1)⁻¹ ≤ (m 0)⁻¹ ∧ (m 3)⁻¹ ≤ (m 2)⁻¹ ∧ 1 ≤ (m 0)⁻¹ ∧ 1 ≤ (m 1)⁻¹ ∧
    (m 0)⁻¹ * m 0 = 1 := by
  have a0 := H.hm 0; have a1 := H.hm 1; have a2 := H.hm 2; have a3 := H.hm 3
  have b0 : 1 - m 0 ≠ 0 := by linarith [H.h1]
  have b1 : 1 - m 1 ≠ 0 := by linarith [H.h2]
  unfold t3 τ0 t1 t2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring
  · exact inv_anti₀ a0 (by linarith [H.h1, H.h3])
  · exact inv_anti₀ a2 (by linarith [H.h2, H.h3])
  · exact one_le_inv₀ a0 |>.2 (by linarith [H.h1])
  · exact one_le_inv₀ a1 |>.2 (by linarith [H.h2])
  · field_simp

lemma T1_0 (u : ℝ) : T1 m 0 u = ramp 0 (t1 m) u + m 0 * ramp (t1 m) (t2 m) u := rfl
lemma T1_1 (u : ℝ) : T1 m 1 u = ramp 0 (t2 m) u := rfl
lemma T1_2 (u : ℝ) : T1 m 2 u = ramp (t2 m) (t3 m) u := rfl
lemma T1_3 (u : ℝ) : T1 m 3 u = ramp (t2 m) (τ0 m) u := rfl
lemma Q1_0 (u : ℝ) : Q1 m 0 u = 1 + ramp 0 (τ0 m) u - (m 0)⁻¹ * T1 m 0 u := rfl
lemma Q1_1 (u : ℝ) : Q1 m 1 u = (m 0)⁻¹ * T1 m 0 u - (m 1)⁻¹ * T1 m 1 u := rfl
lemma Q1_2 (u : ℝ) : Q1 m 2 u = (m 1)⁻¹ * T1 m 1 u - (m 2)⁻¹ * T1 m 2 u := rfl
lemma Q1_3 (u : ℝ) : Q1 m 3 u = (m 2)⁻¹ * T1 m 2 u - (m 3)⁻¹ * T1 m 3 u := rfl

lemma phaseA (H : Hyp m) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ t1 m) :
    Q1 m 0 u = 1 + u - (m 0)⁻¹ * u ∧ Q1 m 1 u = (m 0)⁻¹ * u - (m 1)⁻¹ * u ∧
    Q1 m 2 u = (m 1)⁻¹ * u ∧ Q1 m 3 u = 0 := by
  obtain ⟨o1, o2, o3, o4, -, -, -⟩ := H.order
  have hu2 : u ≤ t2 m := h1.trans o2
  rw [Q1_0, Q1_1, Q1_2, Q1_3, T1_0, T1_1, T1_2, T1_3, ramp_of_mem h0 h1,
    ramp_of_le o2 h1, ramp_of_mem h0 (hu2.trans (o3.trans o4)), ramp_of_mem h0 hu2,
    ramp_of_le o3 hu2, ramp_of_le (o3.trans o4) hu2]
  refine ⟨by ring, by ring, by ring, by ring⟩

lemma phaseB (H : Hyp m) (u : ℝ) (h0 : t1 m ≤ u) (h1 : u ≤ t2 m) :
    Q1 m 0 u = 0 ∧ Q1 m 1 u = 1 + u - (m 1)⁻¹ * u ∧
    Q1 m 2 u = (m 1)⁻¹ * u ∧ Q1 m 3 u = 0 := by
  obtain ⟨o1, o2, o3, o4, -, -, -⟩ := H.order
  obtain ⟨E1, E2, E3, E4, -, -, -, -, E9⟩ := H.ident
  have hu0 : 0 ≤ u := o1.le.trans h0
  rw [Q1_0, Q1_1, Q1_2, Q1_3, T1_0, T1_1, T1_2, T1_3, ramp_of_ge o1.le h0,
    ramp_of_mem h0 h1, ramp_of_mem hu0 (h1.trans (o3.trans o4)), ramp_of_mem hu0 h1,
    ramp_of_le o3 h1, ramp_of_le (o3.trans o4) h1]
  refine ⟨?_, ?_, by ring, by ring⟩
  · linear_combination -E1 - (u - t1 m) * E9
  · linear_combination E1 + (u - t1 m) * E9

lemma phaseC (H : Hyp m) (u : ℝ) (h0 : t2 m ≤ u) (h1 : u ≤ t3 m) :
    Q1 m 0 u = u - t2 m ∧ Q1 m 1 u = 0 ∧
    Q1 m 2 u = (m 2)⁻¹ * (t3 m - u) ∧ Q1 m 3 u = ((m 2)⁻¹ - (m 3)⁻¹) * (u - t2 m) := by
  obtain ⟨o1, o2, o3, o4, -, -, -⟩ := H.order
  obtain ⟨E1, E2, E3, E4, -, -, -, -, E9⟩ := H.ident
  have hu0 : 0 ≤ u := (o1.le.trans o2).trans h0
  rw [Q1_0, Q1_1, Q1_2, Q1_3, T1_0, T1_1, T1_2, T1_3, ramp_of_ge o1.le (o2.trans h0),
    ramp_of_ge o2 h0, ramp_of_mem hu0 (h1.trans o4), ramp_of_ge (o1.le.trans o2) h0,
    ramp_of_mem h0 h1, ramp_of_mem h0 (h1.trans o4)]
  refine ⟨?_, ?_, ?_, by ring⟩
  · linear_combination -E1 - (t2 m - t1 m) * E9
  · linear_combination E1 + (t2 m - t1 m) * E9 - E2
  · linear_combination E2 - E3

lemma phaseD (H : Hyp m) (u : ℝ) (h0 : t3 m ≤ u) (h1 : u ≤ τ0 m) :
    Q1 m 0 u = u - t2 m ∧ Q1 m 1 u = 0 ∧
    Q1 m 2 u = 0 ∧ Q1 m 3 u = (m 3)⁻¹ * (τ0 m - u) := by
  obtain ⟨o1, o2, o3, o4, -, -, -⟩ := H.order
  obtain ⟨E1, E2, E3, E4, -, -, -, -, E9⟩ := H.ident
  have hu2 : t2 m ≤ u := o3.trans h0
  have hu0 : 0 ≤ u := (o1.le.trans o2).trans hu2
  rw [Q1_0, Q1_1, Q1_2, Q1_3, T1_0, T1_1, T1_2, T1_3, ramp_of_ge o1.le (o2.trans hu2),
    ramp_of_ge o2 hu2, ramp_of_mem hu0 h1, ramp_of_ge (o1.le.trans o2) hu2,
    ramp_of_ge o3 h0, ramp_of_mem hu2 h1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -E1 - (t2 m - t1 m) * E9
  · linear_combination E1 + (t2 m - t1 m) * E9 - E2
  · linear_combination E2 - E3
  · linear_combination E3 - E4

lemma Q1_nonneg (H : Hyp m) (k : Fin 4) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ τ0 m) :
    0 ≤ Q1 m k u := by
  obtain ⟨o1, o2, o3, o4, -, -, -⟩ := H.order
  obtain ⟨E1, E2, E3, E4, I1, I2, I3, I4, E9⟩ := H.ident
  have a2 := H.hm 2; have a3 := H.hm 3
  have p2 : 0 < (m 2)⁻¹ := inv_pos.2 a2
  have p3 : 0 < (m 3)⁻¹ := inv_pos.2 a3
  rcases le_total u (t1 m) with hA | hA
  · obtain ⟨q0, q1, q2, q3⟩ := phaseA H u h0 hA
    fin_cases k
    · show 0 ≤ Q1 m 0 u
      rw [q0]; nlinarith [mul_le_mul_of_nonneg_left hA (show 0 ≤ (m 0)⁻¹ - 1 by linarith)]
    · show 0 ≤ Q1 m 1 u
      rw [q1]; nlinarith [mul_nonneg (show 0 ≤ (m 0)⁻¹ - (m 1)⁻¹ by linarith) h0]
    · show 0 ≤ Q1 m 2 u
      rw [q2]; positivity
    · show 0 ≤ Q1 m 3 u
      rw [q3]
  rcases le_total u (t2 m) with hB | hB
  · obtain ⟨q0, q1, q2, q3⟩ := phaseB H u hA hB
    fin_cases k
    · show 0 ≤ Q1 m 0 u
      rw [q0]
    · show 0 ≤ Q1 m 1 u
      rw [q1]; nlinarith [mul_le_mul_of_nonneg_left hB (show 0 ≤ (m 1)⁻¹ - 1 by linarith)]
    · show 0 ≤ Q1 m 2 u
      rw [q2]; positivity
    · show 0 ≤ Q1 m 3 u
      rw [q3]
  rcases le_total u (t3 m) with hC | hC
  · obtain ⟨q0, q1, q2, q3⟩ := phaseC H u hB hC
    fin_cases k
    · show 0 ≤ Q1 m 0 u
      rw [q0]; linarith
    · show 0 ≤ Q1 m 1 u
      rw [q1]
    · show 0 ≤ Q1 m 2 u
      rw [q2]; exact mul_nonneg p2.le (by linarith)
    · show 0 ≤ Q1 m 3 u
      rw [q3]; exact mul_nonneg (by linarith) (by linarith)
  · obtain ⟨q0, q1, q2, q3⟩ := phaseD H u hC h1
    fin_cases k
    · show 0 ≤ Q1 m 0 u
      rw [q0]; linarith
    · show 0 ≤ Q1 m 1 u
      rw [q1]
    · show 0 ≤ Q1 m 2 u
      rw [q2]
    · show 0 ≤ Q1 m 3 u
      rw [q3]; exact mul_nonneg p3.le (by linarith)

lemma Q1_balance (H : Hyp m) :
    Q1 m 0 (τ0 m) = rr m ∧ Q1 m 1 (τ0 m) = 0 ∧ Q1 m 2 (τ0 m) = 0 ∧ Q1 m 3 (τ0 m) = 0 := by
  obtain ⟨o1, o2, o3, o4, -, -, hr⟩ := H.order
  obtain ⟨q0, q1, q2, q3⟩ := phaseD H (τ0 m) o4 le_rfl
  refine ⟨by rw [q0, hr], q1, q2, by rw [q3]; ring⟩

lemma zero0 (H : Hyp m) (u : ℝ) (h0 : t1 m ≤ u) (h1 : u ≤ t2 m) :
    Q1 m 0 u = 0 ∧ Q1 m 3 u = 0 := by
  obtain ⟨q0, -, -, q3⟩ := phaseB H u h0 h1
  exact ⟨q0, q3⟩

lemma zero3 (H : Hyp m) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ t2 m) : Q1 m 3 u = 0 := by
  rcases le_total u (t1 m) with h | h
  · exact (phaseA H u h0 h).2.2.2
  · exact (phaseB H u h h1).2.2.2

lemma zero1 (H : Hyp m) (u : ℝ) (h0 : t2 m ≤ u) (h1 : u ≤ τ0 m) : Q1 m 1 u = 0 := by
  rcases le_total u (t3 m) with h | h
  · exact (phaseC H u h0 h).2.1
  · exact (phaseD H u h h1).2.1

lemma zero2 (H : Hyp m) (u : ℝ) (h0 : t3 m ≤ u) (h1 : u ≤ τ0 m) :
    Q1 m 1 u = 0 ∧ Q1 m 2 u = 0 :=
  ⟨(phaseD H u h0 h1).2.1, (phaseD H u h0 h1).2.2.1⟩

lemma T1_zero (H : Hyp m) (k : Fin 4) (u : ℝ) (hu : u ≤ 0) : T1 m k u = 0 := by
  obtain ⟨o1, o2, o3, o4, -, -, -⟩ := H.order
  fin_cases k
  · show T1 m 0 u = 0
    rw [T1_0, ramp_of_le o1.le hu, ramp_of_le o2 (hu.trans o1.le)]; ring
  · show T1 m 1 u = 0
    rw [T1_1, ramp_of_le (o1.le.trans o2) hu]
  · show T1 m 2 u = 0
    rw [T1_2, ramp_of_le o3 (hu.trans (o1.le.trans o2))]
  · show T1 m 3 u = 0
    rw [T1_3, ramp_of_le (o3.trans o4) (hu.trans (o1.le.trans o2))]

lemma T1_const (H : Hyp m) (k : Fin 4) (u : ℝ) (hu : τ0 m ≤ u) : T1 m k u = T1 m k (τ0 m) := by
  obtain ⟨o1, o2, o3, o4, -, -, -⟩ := H.order
  have h24 := o3.trans o4
  have h14 := o2.trans h24
  fin_cases k
  · show T1 m 0 u = T1 m 0 (τ0 m)
    rw [T1_0, T1_0, ramp_of_ge o1.le (h14.trans hu), ramp_of_ge o2 (h24.trans hu),
      ramp_of_ge o1.le h14, ramp_of_ge o2 h24]
  · show T1 m 1 u = T1 m 1 (τ0 m)
    rw [T1_1, T1_1, ramp_of_ge (o1.le.trans o2) (h24.trans hu), ramp_of_ge (o1.le.trans o2) h24]
  · show T1 m 2 u = T1 m 2 (τ0 m)
    rw [T1_2, T1_2, ramp_of_ge o3 (o4.trans hu), ramp_of_ge o3 o4]
  · show T1 m 3 u = T1 m 3 (τ0 m)
    rw [T1_3, T1_3, ramp_of_ge h24 hu, ramp_of_ge h24 le_rfl]

lemma T1_mono (H : Hyp m) (k : Fin 4) : Monotone (T1 m k) := by
  fin_cases k
  · intro a b hab
    show T1 m 0 a ≤ T1 m 0 b
    rw [T1_0, T1_0]
    have := ramp_mono 0 (t1 m) hab
    have := mul_le_mul_of_nonneg_left (ramp_mono (t1 m) (t2 m) hab) (H.hm 0).le
    linarith
  · exact ramp_mono _ _
  · exact ramp_mono _ _
  · exact ramp_mono _ _

lemma ramp_ids (H : Hyp m) (u : ℝ) :
    ramp 0 (τ0 m) u - T1 m 0 u - T1 m 3 u = (1 - m 0) * ramp (t1 m) (t2 m) u ∧
    ramp 0 (τ0 m) u - T1 m 3 u = ramp 0 (t2 m) u ∧
    ramp 0 (τ0 m) u - T1 m 1 u = ramp (t2 m) (τ0 m) u ∧
    ramp 0 (τ0 m) u - T1 m 1 u - T1 m 2 u = ramp (t3 m) (τ0 m) u := by
  obtain ⟨o1, o2, o3, o4, -, -, -⟩ := H.order
  have A1 := ramp_add (u := u) o1.le o2
  have A2 := ramp_add (u := u) (o1.le.trans o2) (o3.trans o4)
  have A3 := ramp_add (u := u) o3 o4
  rw [T1_0, T1_1, T1_2, T1_3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← A2, ← A1]; ring
  · rw [← A2]; ring
  · rw [← A2]; ring
  · rw [← A2, ← A3]; ring

end Cycle

lemma Φ_sub {r τ : ℝ} (f g h : ℝ → ℝ) (H : ∀ u, h u = f u - g u) (t : ℝ) :
    Φ r τ h t = Φ r τ f t - Φ r τ g t := by
  have := Φ_comb (r := r) (τ := τ) 1 (-1) f g h (fun u => by rw [H]; ring) t
  linarith

lemma Φ_sub3 {r τ : ℝ} (f g1 g2 h : ℝ → ℝ) (H : ∀ u, h u = f u - g1 u - g2 u) (t : ℝ) :
    Φ r τ h t = Φ r τ f t - Φ r τ g1 t - Φ r τ g2 t := by
  rw [Φ_sub (fun u => f u - g1 u) g2 h H, Φ_sub f g1 _ (fun u => rfl)]

lemma Φ_zero_at_zero {r τ : ℝ} (hr : 1 ≤ r) (hτ : 0 < τ) (g : ℝ → ℝ)
    (hg0 : ∀ u, u ≤ 0 → g u = 0) : Φ r τ g 0 = 0 := by
  rw [Φ_eq_sum hr hτ g hg0 0 0 (fun j _ => by
    have := sT_ge hr hτ j; have : (0:ℝ) ≤ j * τ := by positivity
    linarith)]
  simp

open DaiWeissFluid.LuKumar

noncomputable def Tg (m : Fin 4 → ℝ) (t : ℝ) (k : Fin 4) : ℝ := Φ (rr m) (τ0 m) (T1 m k) t

noncomputable def Qg (m : Fin 4 → ℝ) (t : ℝ) (k : Fin 4) : ℝ :=
  (![1, 0, 0, 0] : Fin 4 → ℝ) k + (luKumar m).inflow (Tg m) k t - (luKumar m).μ k * Tg m t k

lemma Qg_0 (m : Fin 4 → ℝ) (t : ℝ) : Qg m t 0 = 1 + t - (m 0)⁻¹ * Tg m t 0 := by
  simp [Qg, ReentrantLine.inflow, ReentrantLine.μ, luKumar]
lemma Qg_1 (m : Fin 4 → ℝ) (t : ℝ) : Qg m t 1 = (m 0)⁻¹ * Tg m t 0 - (m 1)⁻¹ * Tg m t 1 := by
  simp [Qg, ReentrantLine.inflow, ReentrantLine.μ, luKumar]
lemma Qg_2 (m : Fin 4 → ℝ) (t : ℝ) : Qg m t 2 = (m 1)⁻¹ * Tg m t 1 - (m 2)⁻¹ * Tg m t 2 := by
  simp [Qg, ReentrantLine.inflow, ReentrantLine.μ, luKumar]
lemma Qg_3 (m : Fin 4 → ℝ) (t : ℝ) : Qg m t 3 = (m 2)⁻¹ * Tg m t 2 - (m 3)⁻¹ * Tg m t 3 := by
  simp [Qg, ReentrantLine.inflow, ReentrantLine.μ, luKumar]

section Glob
variable {m : Fin 4 → ℝ}

lemma Tg_piece (H : Hyp m) (k : Fin 4) (n : ℕ) (t : ℝ) (h1 : sT (rr m) (τ0 m) n ≤ t)
    (h2 : t ≤ sT (rr m) (τ0 m) (n + 1)) :
    Tg m t k = (∑ j ∈ Finset.range n, rr m ^ j) * T1 m k (τ0 m) +
      rr m ^ n * T1 m k ((t - sT (rr m) (τ0 m) n) / rr m ^ n) := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  exact Φ_piece hr hτ (T1 m k) (T1_zero H k) (T1_const H k) n t h1 h2

lemma local_mem (H : Hyp m) (n : ℕ) (t : ℝ) (h1 : sT (rr m) (τ0 m) n ≤ t)
    (h2 : t ≤ sT (rr m) (τ0 m) (n + 1)) :
    0 ≤ (t - sT (rr m) (τ0 m) n) / rr m ^ n ∧ (t - sT (rr m) (τ0 m) n) / rr m ^ n ≤ τ0 m := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  have hrn : 0 < rr m ^ n := pow_pos (by linarith) n
  rw [sT_succ hr hτ] at h2
  constructor
  · apply div_nonneg _ hrn.le; linarith
  · rw [div_le_iff₀ hrn]; linarith

lemma Qg_piece (H : Hyp m) (k : Fin 4) (n : ℕ) (t : ℝ) (h1 : sT (rr m) (τ0 m) n ≤ t)
    (h2 : t ≤ sT (rr m) (τ0 m) (n + 1)) :
    Qg m t k = rr m ^ n * Q1 m k ((t - sT (rr m) (τ0 m) n) / rr m ^ n) := by
  obtain ⟨-, -, -, o4, hr, hτ, -⟩ := H.order
  obtain ⟨B0, B1, B2, B3⟩ := Q1_balance H
  obtain ⟨l0, l1⟩ := local_mem H n t h1 h2
  have hrn : 0 < rr m ^ n := pow_pos (by linarith) n
  set u := (t - sT (rr m) (τ0 m) n) / rr m ^ n with hu
  set G := ∑ j ∈ Finset.range n, rr m ^ j with hG
  have ht : t = G * τ0 m + rr m ^ n * u := by
    rw [hu, hG, Finset.sum_mul]; unfold sT; field_simp; ring
  have hgeom : G * (rr m - 1) = rr m ^ n - 1 := geom_sum_mul _ _
  have P := fun k => Tg_piece H k n t h1 h2
  rw [← hu, ← hG] at P
  fin_cases k
  · show Qg m t 0 = rr m ^ n * Q1 m 0 u
    rw [Qg_0, P 0, Q1_0, ramp_of_mem l0 l1]
    rw [Q1_0, ramp_of_ge hτ.le le_rfl] at B0
    rw [ht]
    linear_combination G * B0 + hgeom
  · show Qg m t 1 = rr m ^ n * Q1 m 1 u
    rw [Qg_1, P 0, P 1, Q1_1]
    rw [Q1_1] at B1
    linear_combination G * B1
  · show Qg m t 2 = rr m ^ n * Q1 m 2 u
    rw [Qg_2, P 1, P 2, Q1_2]
    rw [Q1_2] at B2
    linear_combination G * B2
  · show Qg m t 3 = rr m ^ n * Q1 m 3 u
    rw [Qg_3, P 2, P 3, Q1_3]
    rw [Q1_3] at B3
    linear_combination G * B3

lemma Tg_zero (H : Hyp m) (k : Fin 4) : Tg m 0 k = 0 := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  exact Φ_zero_at_zero hr hτ _ (T1_zero H k)

lemma Qg_zero (H : Hyp m) (k : Fin 4) : Qg m 0 k = (![1, 0, 0, 0] : Fin 4 → ℝ) k := by
  fin_cases k
  · show Qg m 0 0 = 1
    rw [Qg_0, Tg_zero H]; ring
  · show Qg m 0 1 = 0
    rw [Qg_1, Tg_zero H, Tg_zero H]; ring
  · show Qg m 0 2 = 0
    rw [Qg_2, Tg_zero H, Tg_zero H]; ring
  · show Qg m 0 3 = 0
    rw [Qg_3, Tg_zero H, Tg_zero H]; ring

lemma window (H : Hyp m) (j : ℕ) (u p q : ℝ) (hp : 0 ≤ p) (hq : q ≤ τ0 m)
    (hl : sT (rr m) (τ0 m) j + rr m ^ j * p ≤ u) (hu : u ≤ sT (rr m) (τ0 m) j + rr m ^ j * q) :
    sT (rr m) (τ0 m) j ≤ u ∧ u ≤ sT (rr m) (τ0 m) (j + 1) ∧
    p ≤ (u - sT (rr m) (τ0 m) j) / rr m ^ j ∧ (u - sT (rr m) (τ0 m) j) / rr m ^ j ≤ q := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  have hrj : 0 < rr m ^ j := pow_pos (by linarith) j
  have e1 : 0 ≤ rr m ^ j * p := mul_nonneg hrj.le hp
  have e2 : rr m ^ j * q ≤ rr m ^ j * τ0 m := mul_le_mul_of_nonneg_left hq hrj.le
  refine ⟨by linarith, by rw [sT_succ hr hτ]; linarith, ?_, ?_⟩
  · rw [le_div_iff₀ hrj]; linarith
  · rw [div_le_iff₀ hrj]; linarith

lemma constWhile_aux (H : Hyp m) (c p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
    (f W : ℝ → ℝ) (hf : ∀ t, 0 ≤ t → f t = Φ (rr m) (τ0 m) (fun u => c * ramp p q u) t)
    (hW : ∀ (j : ℕ) (u : ℝ), sT (rr m) (τ0 m) j + rr m ^ j * p ≤ u →
      u ≤ sT (rr m) (τ0 m) j + rr m ^ j * q → W u = 0) :
    DaiWeissFluid.LuKumar.ReentrantLine.ConstantWhile f (fun u => 0 < W u) := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  intro a b ha hab hpos
  rw [hf b (ha.trans hab), hf a ha]
  apply Φ_const_ramp hr hτ c p q hp hpq a b hab
  rintro j u hu ⟨h1, h2⟩
  have : 0 < W u := hpos u hu
  rw [hW j u h1 h2] at this
  exact lt_irrefl _ this

lemma mono_aux (H : Hyp m) (c p q : ℝ) (hc : 0 ≤ c) (hp : 0 ≤ p) (hpq : p ≤ q)
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ t → f t = Φ (rr m) (τ0 m) (fun u => c * ramp p q u) t) :
    MonotoneOn f (Set.Ici 0) := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  intro a ha b hb hab
  rw [hf a ha, hf b hb]
  apply Φ_mono hr hτ _ (fun u hu => by rw [ramp_of_le hpq (hu.trans hp)]; ring)
    (fun x y hxy => mul_le_mul_of_nonneg_left (ramp_mono p q hxy) hc) hab

lemma rep03 (H : Hyp m) (t : ℝ) (ht : 0 ≤ t) :
    t - (Tg m t 0 + Tg m t 3) = Φ (rr m) (τ0 m) (fun u => (1 - m 0) * ramp (t1 m) (t2 m) u) t := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  rw [Φ_sub3 (ramp 0 (τ0 m)) (T1 m 0) (T1 m 3) _ (fun u => ((ramp_ids H u).1).symm),
    Φ_ramp_id hr hτ t ht]
  unfold Tg; ring

lemma rep3 (H : Hyp m) (t : ℝ) (ht : 0 ≤ t) :
    t - Tg m t 3 = Φ (rr m) (τ0 m) (fun u => 1 * ramp 0 (t2 m) u) t := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  rw [Φ_sub (ramp 0 (τ0 m)) (T1 m 3) _ (fun u => by rw [one_mul]; exact ((ramp_ids H u).2.1).symm),
    Φ_ramp_id hr hτ t ht]
  rfl

lemma rep1 (H : Hyp m) (t : ℝ) (ht : 0 ≤ t) :
    t - Tg m t 1 = Φ (rr m) (τ0 m) (fun u => 1 * ramp (t2 m) (τ0 m) u) t := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  rw [Φ_sub (ramp 0 (τ0 m)) (T1 m 1) _ (fun u => by rw [one_mul]; exact ((ramp_ids H u).2.2.1).symm),
    Φ_ramp_id hr hτ t ht]
  rfl

lemma rep12 (H : Hyp m) (t : ℝ) (ht : 0 ≤ t) :
    t - (Tg m t 1 + Tg m t 2) = Φ (rr m) (τ0 m) (fun u => 1 * ramp (t3 m) (τ0 m) u) t := by
  obtain ⟨-, -, -, -, hr, hτ, -⟩ := H.order
  rw [Φ_sub3 (ramp 0 (τ0 m)) (T1 m 1) (T1 m 2) _
      (fun u => by rw [one_mul]; exact ((ramp_ids H u).2.2.2).symm),
    Φ_ramp_id hr hτ t ht]
  unfold Tg; ring

end Glob

end LKScaledAux

open LKScaledAux DaiWeissFluid.LuKumar in
theorem solution (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : 1 ≤ m 1 + m 3) :
    let r : ℝ := m 3 / (1 - m 1)
    let s : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n,
      r ^ j * ((m 1 + m 3) / (1 - m 1))
    ∃ Q T, (luKumar m).IsPrioritySolution piLK Q T ∧
      Q 0 = ![1, 0, 0, 0] ∧
      ∀ n : ℕ, Q (s n) = ![r ^ n, 0, 0, 0] := by
  intro r s
  have H : Hyp m := ⟨hm, h51₁, h51₂, h52⟩
  obtain ⟨o1, o2, o3, o4, hr, hτ, -⟩ := H.order
  have hs : ∀ n, s n = sT (rr m) (τ0 m) n := fun n => rfl
  have hC0 : (luKumar m).C 0 = {0, 3} := by
    show Finset.univ.filter (fun k : Fin 4 => (![0,1,1,0] : Fin 4 → Fin 2) k = 0) = {0,3}
    decide
  have hC1 : (luKumar m).C 1 = {1, 2} := by
    show Finset.univ.filter (fun k : Fin 4 => (![0,1,1,0] : Fin 4 → Fin 2) k = 1) = {1,2}
    decide
  have hH0 : (luKumar m).H piLK 0 = {0, 3} := by
    ext l; fin_cases l <;> simp [ReentrantLine.H, luKumar, piLK, Equiv.swap_apply_def]
  have hH1 : (luKumar m).H piLK 1 = {1} := by
    ext l; fin_cases l <;> simp [ReentrantLine.H, luKumar, piLK, Equiv.swap_apply_def]
  have hH2 : (luKumar m).H piLK 2 = {1, 2} := by
    ext l; fin_cases l <;> simp [ReentrantLine.H, luKumar, piLK, Equiv.swap_apply_def]
  have hH3 : (luKumar m).H piLK 3 = {3} := by
    ext l; fin_cases l <;> simp [ReentrantLine.H, luKumar, piLK, Equiv.swap_apply_def]
  -- local form of Q on a window
  have hloc : ∀ (j : ℕ) (u p q : ℝ), 0 ≤ p → q ≤ τ0 m →
      sT (rr m) (τ0 m) j + rr m ^ j * p ≤ u → u ≤ sT (rr m) (τ0 m) j + rr m ^ j * q →
      ∃ v, p ≤ v ∧ v ≤ q ∧ ∀ k, Qg m u k = rr m ^ j * Q1 m k v := by
    intro j u p q hp hq h1 h2
    obtain ⟨w1, w2, w3, w4⟩ := window H j u p q hp hq h1 h2
    exact ⟨_, w3, w4, fun k => Qg_piece H k j u w1 w2⟩
  refine ⟨Qg m, Tg m, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro t _ k
    rw [Qg_zero H k]; rfl
  · intro t ht k
    obtain ⟨n, h1, h2⟩ := exists_piece hr hτ t ht
    rw [Qg_piece H k n t h1 h2]
    obtain ⟨l0, l1⟩ := local_mem H n t h1 h2
    exact mul_nonneg (pow_nonneg (by linarith) n) (Q1_nonneg H k _ l0 l1)
  · exact Tg_zero H
  · intro k
    exact (Φ_mono hr hτ _ (T1_zero H k) (T1_mono H k)).monotoneOn _
  · intro i
    fin_cases i
    · apply mono_aux H (1 - m 0) (t1 m) (t2 m) (by linarith [hm 3]) o1.le o2
      intro t ht
      rw [← rep03 H t ht]
      simp only [ReentrantLine.idle, ReentrantLine.busy]
      rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, hC0,
        Finset.sum_pair (by decide)]
    · apply mono_aux H 1 (t3 m) (τ0 m) (by norm_num) (o1.le.trans (o2.trans o3)) o4
      intro t ht
      rw [← rep12 H t ht]
      simp only [ReentrantLine.idle, ReentrantLine.busy]
      rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, hC1,
        Finset.sum_pair (by decide)]
  · intro k
    fin_cases k
    · apply constWhile_aux H (1 - m 0) (t1 m) (t2 m) o1.le o2
      · intro t ht
        rw [← rep03 H t ht]
        simp only [ReentrantLine.Uplus, ReentrantLine.Tplus]
        rw [show ((⟨0, by norm_num⟩ : Fin 4)) = 0 from rfl, hH0, Finset.sum_pair (by decide)]
      · intro j u h1 h2
        obtain ⟨v, hv1, hv2, hQ⟩ := hloc j u _ _ o1.le (o3.trans o4) h1 h2
        obtain ⟨z0, z3⟩ := zero0 H v hv1 hv2
        simp only [ReentrantLine.Wplus]
        rw [show ((⟨0, by norm_num⟩ : Fin 4)) = 0 from rfl, hH0, Finset.sum_pair (by decide),
          hQ, hQ, z0, z3]
        ring
    · apply constWhile_aux H 1 (t2 m) (τ0 m) (o1.le.trans o2) (o3.trans o4)
      · intro t ht
        rw [← rep1 H t ht]
        simp only [ReentrantLine.Uplus, ReentrantLine.Tplus]
        rw [show ((⟨1, by norm_num⟩ : Fin 4)) = 1 from rfl, hH1, Finset.sum_singleton]
      · intro j u h1 h2
        obtain ⟨v, hv1, hv2, hQ⟩ := hloc j u _ _ (o1.le.trans o2) le_rfl h1 h2
        have z1 := zero1 H v hv1 hv2
        simp only [ReentrantLine.Wplus]
        rw [show ((⟨1, by norm_num⟩ : Fin 4)) = 1 from rfl, hH1, Finset.sum_singleton, hQ, z1]
        ring
    · apply constWhile_aux H 1 (t3 m) (τ0 m) (o1.le.trans (o2.trans o3)) o4
      · intro t ht
        rw [← rep12 H t ht]
        simp only [ReentrantLine.Uplus, ReentrantLine.Tplus]
        rw [show ((⟨2, by norm_num⟩ : Fin 4)) = 2 from rfl, hH2, Finset.sum_pair (by decide)]
      · intro j u h1 h2
        obtain ⟨v, hv1, hv2, hQ⟩ := hloc j u _ _ (o1.le.trans (o2.trans o3)) le_rfl h1 h2
        obtain ⟨z1, z2⟩ := zero2 H v hv1 hv2
        simp only [ReentrantLine.Wplus]
        rw [show ((⟨2, by norm_num⟩ : Fin 4)) = 2 from rfl, hH2, Finset.sum_pair (by decide),
          hQ, hQ, z1, z2]
        ring
    · apply constWhile_aux H 1 0 (t2 m) le_rfl (o1.le.trans o2)
      · intro t ht
        rw [← rep3 H t ht]
        simp only [ReentrantLine.Uplus, ReentrantLine.Tplus]
        rw [show ((⟨3, by norm_num⟩ : Fin 4)) = 3 from rfl, hH3, Finset.sum_singleton]
      · intro j u h1 h2
        obtain ⟨v, hv1, hv2, hQ⟩ := hloc j u _ _ le_rfl (o3.trans o4) h1 h2
        have z3 := zero3 H v hv1 hv2
        simp only [ReentrantLine.Wplus]
        rw [show ((⟨3, by norm_num⟩ : Fin 4)) = 3 from rfl, hH3, Finset.sum_singleton, hQ, z3]
        ring
  · funext k
    exact Qg_zero H k
  · intro n
    funext k
    have h1 : sT (rr m) (τ0 m) n ≤ s n := le_of_eq (hs n).symm
    have h2 : s n ≤ sT (rr m) (τ0 m) (n + 1) := by
      rw [hs]; exact sT_mono hr hτ (Nat.le_succ n)
    rw [Qg_piece H k n (s n) h1 h2, hs, sub_self, zero_div]
    obtain ⟨q0, q1, q2, q3⟩ := phaseA H 0 le_rfl o1.le
    fin_cases k
    · show rr m ^ n * Q1 m 0 0 = r ^ n
      rw [q0]; simp [r, rr]
    · show rr m ^ n * Q1 m 1 0 = 0
      rw [q1]; ring
    · show rr m ^ n * Q1 m 2 0 = 0
      rw [q2]; ring
    · show rr m ^ n * Q1 m 3 0 = 0
      rw [q3]; ring
