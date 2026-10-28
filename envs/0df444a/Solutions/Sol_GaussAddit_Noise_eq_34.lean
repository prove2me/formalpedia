-- Prove2me | solution 1 for GaussAddit.Noise.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:25:25.899459+00:00
-- url     : https://prove2.me/submissions/045fae70-7cf2-4d4c-aa79-60581ea5dd60

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open Matrix

open Fin.NatCast in
lemma key_det {R : Type*} [CommRing R] (c : R) (N : ℕ) (M : Matrix (Fin (N+2)) (Fin (N+2)) R)
    (hM : ∀ s t, M s t = (if s = t then c else 0) - if t = finRotate _ s then 1 else 0) :
    M.det = c ^ (N+2) - 1 := by
  have hrot : ∀ i : Fin (N+2), finRotate (N+2) i = i + 1 := fun i => finRotate_apply i
  have hne : ∀ i : Fin (N+2), i + 1 ≠ i := by
    intro i h
    have : (1 : Fin (N+2)) = 0 := by
      have := congrArg (· - i) h
      simpa using this
    exact absurd this (by simp)
  set ρ : Equiv.Perm (Fin (N+2)) := (finRotate (N+2))⁻¹ with hρ
  have hρi : ∀ i, ρ i + 1 = i := by
    intro i
    rw [← hrot]
    simp [hρ]
  have h1ρ : (1 : Equiv.Perm (Fin (N+2))) ≠ ρ := by
    intro h
    have := hρi 0
    rw [← h] at this
    exact hne 0 (by simpa using this)
  rw [det_apply']
  rw [Fintype.sum_eq_add 1 ρ h1ρ]
  · have e1 : ∏ i, M ((1 : Equiv.Perm (Fin (N+2))) i) i = c ^ (N+2) := by
      simp only [Equiv.Perm.one_apply, hM, if_true, hrot]
      rw [Finset.prod_congr rfl (g := fun _ => c)]
      · simp
      · intro i _
        have : ¬ (i = i + 1) := fun h => hne i h.symm
        simp [this]
    have e2 : ∏ i, M (ρ i) i = (-1) ^ (N+2) := by
      rw [Finset.prod_congr rfl (g := fun _ => (-1 : R))]
      · simp
      · intro i _
        have h2 : ¬ (ρ i = i) := by
          intro h; have := hρi i; rw [h] at this; exact hne i this
        have h3 : i = finRotate _ (ρ i) := by rw [hrot, hρi]
        simp only [hM]
        rw [if_neg h2, if_pos h3]
        simp
    rw [e1, e2]
    have hs : Equiv.Perm.sign ρ = (-1) ^ (N+1) := by
      rw [hρ, Equiv.Perm.sign_inv, sign_finRotate]
      rfl
    have hodd : ((-1:R))^(N+1) * (-1)^(N+2) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨N+1, by ring⟩
    simp only [Equiv.Perm.sign_one, hs]
    push_cast
    linear_combination hodd
  · intro σ ⟨hσ1, hσρ⟩
    apply mul_eq_zero_of_right
    suffices hex : ∃ i, M (σ i) i = 0 by
      obtain ⟨i, hi⟩ := hex
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    by_contra hprod
    push_neg at hprod
    have hopt : ∀ i, σ i = i ∨ σ i + 1 = i := by
      intro i
      have := hprod i
      by_contra hc
      push_neg at hc
      apply this
      simp only [hM, hrot]
      rw [if_neg hc.1, if_neg (fun h => hc.2 h.symm)]
      simp
    obtain ⟨i₀, hi₀⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      push_neg at h
      exact hσ1 (Equiv.ext h)
    have step : ∀ i, σ i ≠ i → σ (i - 1) ≠ i - 1 := by
      intro i hi
      have h1 : σ i = i - 1 := by
        rcases hopt i with h | h
        · exact absurd h hi
        · exact eq_sub_of_add_eq h
      intro h
      rw [← h1] at h
      exact hi (σ.injective h)
    have all : ∀ t : ℕ, σ (i₀ - (t : Fin (N+2))) ≠ i₀ - (t : Fin (N+2)) := by
      intro t
      induction t with
      | zero => simpa using hi₀
      | succ t ih =>
        have := step _ ih
        simpa [Nat.cast_succ, sub_sub] using this
    apply hσρ
    ext1 i
    have hi : σ i ≠ i := by
      have := all ((i₀ - i : Fin (N+2)) : ℕ)
      simpa [Fin.cast_val_eq_self] using this
    rcases hopt i with h | h
    · exact absurd h hi
    · have := hρi i
      exact congrArg Fin.val (add_right_cancel (h.trans this.symm)) |> Fin.ext

lemma key_det_all {R : Type*} [CommRing R] (c : R) (k : ℕ) (hk : 1 ≤ k)
    (M : Matrix (Fin k) (Fin k) R)
    (hM : ∀ s t, M s t = (if s = t then c else 0) - if t = finRotate _ s then 1 else 0) :
    M.det = c ^ k - 1 := by
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 1 := ⟨k - 1, by omega⟩
  rcases N with _ | N
  · rw [Matrix.det_fin_one, hM]
    simp
  · exact key_det c N M hM

theorem solution (n : ℝ) (hn : 0 < n) (k : ℕ) (hk : 1 ≤ k) :
    let P : Matrix (Fin k) (Fin k) ℝ := fun s t => if t = finRotate k s then 1 else 0
    let G : Matrix (Fin k) (Fin k) ℝ := P - 1
    let A : Matrix (Fin k) (Fin k) ℝ := Pᵀ - P
    let C : Matrix (Fin k) (Fin k) ℝ := (1 / n) • (1 : Matrix (Fin k) (Fin k) ℝ) + (1 / 2 : ℝ) • A
    (1 / n ^ k) / (C + (1 / 2 : ℝ) • (Gᵀ * G)).det = 1 / ((n + 1) ^ k - n ^ k) := by
  intro P G A C
  have hP : ∀ s t, P s t = if t = finRotate k s then 1 else 0 := fun _ _ => rfl
  have hPP : Pᵀ * P = 1 := by
    ext s t
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hP, Matrix.one_apply]
    rw [Equiv.sum_comp (finRotate k)
      (fun v => (if s = v then (1:ℝ) else 0) * (if t = v then 1 else 0))]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact if_congr eq_comm rfl rfl
  have hM : C + (1 / 2 : ℝ) • (Gᵀ * G) = (1 / n + 1) • (1 : Matrix (Fin k) (Fin k) ℝ) - P := by
    simp only [C, A, G, Matrix.transpose_sub, Matrix.transpose_one, sub_mul, mul_sub, mul_one,
      one_mul, hPP]
    module
  have hM2 : ∀ s t, ((1 / n + 1) • (1 : Matrix (Fin k) (Fin k) ℝ) - P) s t =
      (if s = t then (1 / n + 1) else 0) - if t = finRotate _ s then 1 else 0 := by
    intro s t
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    simp [P]
  rw [hM, key_det_all _ k hk _ hM2]
  have hn0 : n ≠ 0 := hn.ne'
  have hnk : n ^ k ≠ 0 := pow_ne_zero _ hn0
  have hlt : n ^ k < (n + 1) ^ k := by
    apply pow_lt_pow_left₀ (by linarith) hn.le (by omega)
  have hd : (n + 1) ^ k - n ^ k ≠ 0 := by linarith
  have h1 : (1 / n + 1) ^ k = (n + 1) ^ k / n ^ k := by
    rw [← div_pow, div_add_one hn0, add_comm]
  rw [h1]
  field_simp
