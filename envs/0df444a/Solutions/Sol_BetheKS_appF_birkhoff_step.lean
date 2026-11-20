-- Prove2me | solution 1 for BetheKS.appF_birkhoff_step
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-19T15:28:19.306392+00:00
-- url     : https://prove2.me/submissions/f371e095-d71f-4bde-b69a-9e39805a3fe4

import Mathlib

set_option maxHeartbeats 1600000
set_option autoImplicit false

open Finset
open scoped BigOperators

theorem solution {r : ℕ} (D : Matrix (Fin r) (Fin r) ℝ) (hD : D ≠ 0)
    (hrow : ∀ a, ∑ b, D a b = 0) (hcol : ∀ b, ∑ a, D a b = 0) :
    Real.sqrt (∑ a, ∑ b, D a b ^ 2) / r ≤
      Finset.univ.sup' Finset.univ_nonempty (fun τ : Equiv.Perm (Fin r) => ∑ b, D (τ b) b) := by
  rcases r with _ | _ | n
  · -- r = 0
    have h0 : (0 : ℝ) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun τ : Equiv.Perm (Fin 0) => ∑ b, D (τ b) b) := by
      have h := Finset.le_sup' (s := (Finset.univ : Finset (Equiv.Perm (Fin 0))))
        (f := fun τ : Equiv.Perm (Fin 0) => ∑ b, D (τ b) b)
        (Finset.mem_univ (Equiv.refl (Fin 0)))
      simpa using h
    simpa using h0
  · -- r = 1
    exfalso
    apply hD
    ext a b
    simp only [Matrix.zero_apply]
    have h : D 0 0 = 0 := by simpa using hrow 0
    have ha : a = 0 := Fin.ext (by omega)
    have hb : b = 0 := Fin.ext (by omega)
    rw [ha, hb]
    exact h
  · -- r = n + 2
    classical
    have hR : (0 : ℝ) < ((n : ℝ) + 2) := by positivity
    have hRne : ((n : ℝ) + 2) ≠ 0 := ne_of_gt hR
    -- S and N
    set S : ℝ := ∑ a : Fin (n + 2), ∑ b : Fin (n + 2), D a b ^ 2 with hS
    have hS_nonneg : 0 ≤ S := by
      rw [hS]
      exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
    have hex : ∃ a b, D a b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hD (funext fun a => funext fun b => h a b)
    obtain ⟨a0, b0, hab0⟩ := hex
    have hS_pos : 0 < S := by
      rw [hS]
      have h1 : 0 < ∑ b : Fin (n + 2), D a0 b ^ 2 :=
        Finset.sum_pos' (fun b _ => sq_nonneg _) ⟨b0, Finset.mem_univ _, by positivity⟩
      exact Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
        ⟨a0, Finset.mem_univ _, h1⟩
    set N : ℝ := Real.sqrt S with hN
    have hNpos : 0 < N := by rw [hN]; exact Real.sqrt_pos.2 hS_pos
    have hNne : N ≠ 0 := ne_of_gt hNpos
    have hN2 : N ^ 2 = S := by rw [hN]; exact Real.sq_sqrt hS_nonneg
    -- P
    set P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      (fun a b => (1 : ℝ) / ((n : ℝ) + 2) + D a b / (((n : ℝ) + 2) * N)) with hP
    -- P is doubly stochastic
    have hPmem : P ∈ doublyStochastic ℝ (Fin (n + 2)) := by
      rw [mem_doublyStochastic_iff_sum]
      have hconst : ∑ _b : Fin (n + 2), (1 : ℝ) / ((n : ℝ) + 2) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp
      refine ⟨?_, ?_, ?_⟩
      · intro a b
        show (0 : ℝ) ≤ (1 : ℝ) / ((n : ℝ) + 2) + D a b / (((n : ℝ) + 2) * N)
        have hb : |D a b| ≤ N := by
          have h2 : D a b ^ 2 ≤ ∑ b : Fin (n + 2), D a b ^ 2 :=
            Finset.single_le_sum (fun b _ => sq_nonneg (D a b)) (Finset.mem_univ b)
          have h3 : ∑ b : Fin (n + 2), D a b ^ 2 ≤ S := by
            rw [hS]
            exact Finset.single_le_sum
              (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ a)
          have h4 : D a b ^ 2 ≤ N ^ 2 := by rw [hN2]; exact h2.trans h3
          exact abs_le_of_sq_le_sq h4 (le_of_lt hNpos)
        have hge : -N ≤ D a b := by
          have h := neg_abs_le (D a b)
          linarith
        have hden : (0 : ℝ) < ((n : ℝ) + 2) * N := mul_pos hR hNpos
        have hkey : (1 : ℝ) / ((n : ℝ) + 2) + D a b / (((n : ℝ) + 2) * N) =
            (N + D a b) / (((n : ℝ) + 2) * N) := by
          field_simp
        rw [hkey]
        exact div_nonneg (by linarith) (le_of_lt hden)
      · intro a
        have h2 : ∑ b : Fin (n + 2), D a b / (((n : ℝ) + 2) * N) = 0 := by
          rw [← Finset.sum_div, hrow a, zero_div]
        show ∑ b : Fin (n + 2),
            ((1 : ℝ) / ((n : ℝ) + 2) + D a b / (((n : ℝ) + 2) * N)) = 1
        rw [Finset.sum_add_distrib, hconst, h2, add_zero]
      · intro b
        have h2 : ∑ a : Fin (n + 2), D a b / (((n : ℝ) + 2) * N) = 0 := by
          rw [← Finset.sum_div, hcol b, zero_div]
        show ∑ a : Fin (n + 2),
            ((1 : ℝ) / ((n : ℝ) + 2) + D a b / (((n : ℝ) + 2) * N)) = 1
        rw [Finset.sum_add_distrib, hconst, h2, add_zero]
    obtain ⟨w, hw_nonneg, hw_sum, hwP⟩ :=
      exists_eq_sum_perm_of_mem_doublyStochastic hPmem
    -- value of the pairing
    have hPmul : ∀ a b : Fin (n + 2), P a b * D a b =
        D a b / ((n : ℝ) + 2) + D a b ^ 2 / (((n : ℝ) + 2) * N) := by
      intro a b
      show ((1 : ℝ) / ((n : ℝ) + 2) + D a b / (((n : ℝ) + 2) * N)) * D a b =
        D a b / ((n : ℝ) + 2) + D a b ^ 2 / (((n : ℝ) + 2) * N)
      field_simp
    have hval : ∑ a : Fin (n + 2), ∑ b : Fin (n + 2), P a b * D a b = N / ((n : ℝ) + 2) := by
      simp only [hPmul]
      simp only [Finset.sum_add_distrib]
      have hA : ∀ a : Fin (n + 2), ∑ b : Fin (n + 2), D a b / ((n : ℝ) + 2) = 0 := by
        intro a
        rw [← Finset.sum_div, hrow a, zero_div]
      simp only [hA, Finset.sum_const_zero, zero_add]
      have hB : ∀ a : Fin (n + 2), ∑ b : Fin (n + 2),
          D a b ^ 2 / (((n : ℝ) + 2) * N) =
          (∑ b : Fin (n + 2), D a b ^ 2) / (((n : ℝ) + 2) * N) := by
        intro a
        rw [Finset.sum_div]
      simp only [hB]
      rw [← Finset.sum_div, ← hS, ← hN2]
      field_simp
    -- flattening lemma
    have hflatten : ∀ f : Fin (n + 2) × Fin (n + 2) → ℝ,
        ∑ p : Fin (n + 2) × Fin (n + 2), f p = ∑ a, ∑ b, f (a, b) := by
      intro f
      rw [← Finset.sum_product]
      simp
    -- permutation sum identity
    have hperm : ∀ σ : Equiv.Perm (Fin (n + 2)),
        ∑ a : Fin (n + 2), ∑ b : Fin (n + 2), σ.permMatrix ℝ a b * D a b =
          ∑ b, D (σ⁻¹ b) b := by
      intro σ
      have hA : ∀ a : Fin (n + 2),
          ∑ b : Fin (n + 2), σ.permMatrix ℝ a b * D a b = D a (σ a) := by
        intro a
        have hrow_eq : σ.permMatrix ℝ a = Pi.single (σ a) (1 : ℝ) :=
          PEquiv.toMatrix_toPEquiv_apply σ a
        rw [hrow_eq]
        simp [Pi.single_apply]
      simp only [hA]
      rw [← Equiv.sum_comp σ (fun x => D (σ⁻¹ x) x)]
      simp
    have hkey : ∑ a : Fin (n + 2), ∑ b : Fin (n + 2), P a b * D a b =
        ∑ σ : Equiv.Perm (Fin (n + 2)), w σ * ∑ b, D (σ⁻¹ b) b := by
      have hPab : ∀ a b : Fin (n + 2), P a b =
          ∑ σ : Equiv.Perm (Fin (n + 2)), w σ * σ.permMatrix ℝ a b := by
        intro a b
        rw [← hwP]
        simp [Matrix.sum_apply]
      have h2 : ∑ p : Fin (n + 2) × Fin (n + 2),
            (∑ σ : Equiv.Perm (Fin (n + 2)), w σ * σ.permMatrix ℝ p.1 p.2) * D p.1 p.2 =
          ∑ σ : Equiv.Perm (Fin (n + 2)), w σ *
            ∑ p : Fin (n + 2) × Fin (n + 2), σ.permMatrix ℝ p.1 p.2 * D p.1 p.2 := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
      rw [← hflatten (fun p : Fin (n + 2) × Fin (n + 2) => P p.1 p.2 * D p.1 p.2)]
      simp only [hPab]
      rw [h2]
      refine Finset.sum_congr rfl fun σ _ => ?_
      congr 1
      rw [hflatten (fun p : Fin (n + 2) × Fin (n + 2) =>
        σ.permMatrix ℝ p.1 p.2 * D p.1 p.2)]
      exact hperm σ
    -- bound by the sup
    have hsup : ∑ σ : Equiv.Perm (Fin (n + 2)), w σ * ∑ b, D (σ⁻¹ b) b ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun τ : Equiv.Perm (Fin (n + 2)) => ∑ b, D (τ b) b) := by
      have hle : ∀ τ : Equiv.Perm (Fin (n + 2)), ∑ b, D (τ b) b ≤
          Finset.univ.sup' Finset.univ_nonempty
            (fun τ : Equiv.Perm (Fin (n + 2)) => ∑ b, D (τ b) b) :=
        fun τ => Finset.le_sup' (fun τ : Equiv.Perm (Fin (n + 2)) => ∑ b, D (τ b) b)
          (Finset.mem_univ τ)
      calc ∑ σ : Equiv.Perm (Fin (n + 2)), w σ * ∑ b, D (σ⁻¹ b) b
          ≤ ∑ σ : Equiv.Perm (Fin (n + 2)), w σ *
              Finset.univ.sup' Finset.univ_nonempty
                (fun τ : Equiv.Perm (Fin (n + 2)) => ∑ b, D (τ b) b) := by
            refine Finset.sum_le_sum fun σ _ => ?_
            exact mul_le_mul_of_nonneg_left (hle σ⁻¹) (hw_nonneg σ)
        _ = (∑ σ : Equiv.Perm (Fin (n + 2)), w σ) *
              Finset.univ.sup' Finset.univ_nonempty
                (fun τ : Equiv.Perm (Fin (n + 2)) => ∑ b, D (τ b) b) := by
            rw [Finset.sum_mul]
        _ = Finset.univ.sup' Finset.univ_nonempty
              (fun τ : Equiv.Perm (Fin (n + 2)) => ∑ b, D (τ b) b) := by
            rw [hw_sum, one_mul]
    -- final assembly
    have hNval : Real.sqrt (∑ a : Fin (n + 2), ∑ b : Fin (n + 2), D a b ^ 2) /
        ↑(n + 2) = N / ((n : ℝ) + 2) := by
      have h1 : Real.sqrt (∑ a : Fin (n + 2), ∑ b : Fin (n + 2), D a b ^ 2) = N := by
        rw [hN, ← hS]
      rw [h1]
      push_cast
      ring
    rw [hNval]
    calc N / ((n : ℝ) + 2) = ∑ a : Fin (n + 2), ∑ b : Fin (n + 2), P a b * D a b := hval.symm
      _ = ∑ σ : Equiv.Perm (Fin (n + 2)), w σ * ∑ b, D (σ⁻¹ b) b := hkey
      _ ≤ Finset.univ.sup' Finset.univ_nonempty
            (fun τ : Equiv.Perm (Fin (n + 2)) => ∑ b, D (τ b) b) := hsup
