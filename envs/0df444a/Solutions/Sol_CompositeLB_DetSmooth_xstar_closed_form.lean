-- Prove2me | solution 1 for CompositeLB.DetSmooth.xstar_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:52:16.533118+00:00
-- url     : https://prove2.me/submissions/732ecd16-28d2-4ce3-9098-5da0a7b9ee3d

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Construction

set_option autoImplicit false

open CompositeLB.DetSmooth

lemma clb_inner_v {d k : ℕ} (v : ℕ → CompositeLB.DetLip.E d)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ))) (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) :
    inner ℝ (v i) (v j) = if i = j then (1 : ℝ) else 0 := by
  have := orthonormal_iff_ite.1 hv ⟨i, by omega⟩ ⟨j, by omega⟩
  simpa [Fin.ext_iff] using this

lemma clb_coord {d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ))) (t : ℕ) (htk : t ≤ k + 1)
    (j : ℕ) (hj : j < t) :
    inner ℝ (xstarT a v t) (v j) = a * (1 - ((j : ℝ) + 1) / ((t : ℝ) + 1)) := by
  unfold xstarT
  rw [real_inner_smul_left, sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.sum_eq_single j]
  · rw [clb_inner_v v hv j j (by omega) (by omega)]; simp
  · intro r hr hrj
    rw [clb_inner_v v hv r j (by have := Finset.mem_range.1 hr; omega) (by omega)]
    simp [hrj]
  · intro h; exact absurd (Finset.mem_range.2 hj) h

lemma clb_sumsq (T : ℝ) (n : ℕ) :
    ∑ r ∈ Finset.range n, (T - (r : ℝ)) ^ 2
      = (n : ℝ) * T ^ 2 - T * n * ((n : ℝ) - 1) + ((n : ℝ) - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring


lemma clb_tele (f : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    ∑ r ∈ Finset.Ico 1 t, (f (r - 1) - f r) = f 0 - f (t - 1) := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [Finset.sum_Ico_succ_top ht, ih]
    simp

/-- the quadratic form `Q` of `F^t` in the coordinates `u j = ⟨x, v_j⟩`. -/
noncomputable def clbQ (a : ℝ) (t : ℕ) (u : ℕ → ℝ) : ℝ :=
  u 0 ^ 2 - 2 * a * u 0 + ∑ r ∈ Finset.Ico 1 t, (u (r - 1) - u r) ^ 2 + u (t - 1) ^ 2

lemma clb_Qid (a : ℝ) (t : ℕ) (ht : 1 ≤ t) (u : ℕ → ℝ) :
    clbQ a t u = -(a ^ 2 * t / ((t : ℝ) + 1)) +
      ((u 0 - a * (1 - 1 / ((t : ℝ) + 1))) ^ 2 +
        ∑ r ∈ Finset.Ico 1 t,
          ((u (r - 1) - a * (1 - (((r - 1 : ℕ) : ℝ) + 1) / ((t : ℝ) + 1))) -
            (u r - a * (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)))) ^ 2 +
        (u (t - 1) - a * (1 - (((t - 1 : ℕ) : ℝ) + 1) / ((t : ℝ) + 1))) ^ 2) := by
  set us : ℕ → ℝ := fun j => a * (1 - ((j : ℝ) + 1) / ((t : ℝ) + 1)) with hus
  set h : ℕ → ℝ := fun j => u j - us j with hh
  have hT : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  set D : ℝ := a / ((t : ℝ) + 1) with hD
  have hDr : ∀ r ∈ Finset.Ico 1 t, u (r - 1) - u r = D + (h (r - 1) - h r) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Ico.1 hr).1
    have hc : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub hr1]; simp
    simp only [hh, hus, hD, hc]
    field_simp
    ring
  have hsq : ∑ r ∈ Finset.Ico 1 t, (u (r - 1) - u r) ^ 2
      = ((t : ℝ) - 1) * D ^ 2 + 2 * D * (h 0 - h (t - 1)) +
        ∑ r ∈ Finset.Ico 1 t, (h (r - 1) - h r) ^ 2 := by
    rw [Finset.sum_congr rfl (fun r hr => by rw [hDr r hr])]
    have : ∀ r ∈ Finset.Ico 1 t, (D + (h (r - 1) - h r)) ^ 2
        = D ^ 2 + 2 * D * (h (r - 1) - h r) + (h (r - 1) - h r) ^ 2 := by
      intro r _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, clb_tele h t ht]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
      rw [Nat.cast_sub ht]; simp
    rw [this]
  have hc1 : (((t - 1 : ℕ) : ℝ)) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub ht]; simp
  unfold clbQ
  rw [hsq]
  simp only [hh, hus, hD, hc1]
  field_simp
  ring

lemma clb_Q_ge (a : ℝ) (t : ℕ) (ht : 1 ≤ t) (u : ℕ → ℝ) :
    -(a ^ 2 * t / ((t : ℝ) + 1)) ≤ clbQ a t u := by
  rw [clb_Qid a t ht u]
  have : 0 ≤ ∑ r ∈ Finset.Ico 1 t,
      ((u (r - 1) - a * (1 - (((r - 1 : ℕ) : ℝ) + 1) / ((t : ℝ) + 1))) -
            (u r - a * (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)))) ^ 2 :=
    Finset.sum_nonneg (fun r _ => sq_nonneg _)
  nlinarith [sq_nonneg (u 0 - a * (1 - 1 / ((t : ℝ) + 1))),
    sq_nonneg (u (t - 1) - a * (1 - (((t - 1 : ℕ) : ℝ) + 1) / ((t : ℝ) + 1)))]

lemma clb_Q_eq (a : ℝ) (t : ℕ) (ht : 1 ≤ t) (u : ℕ → ℝ)
    (hu : ∀ j, j < t → u j = a * (1 - ((j : ℝ) + 1) / ((t : ℝ) + 1))) :
    clbQ a t u = -(a ^ 2 * t / ((t : ℝ) + 1)) := by
  rw [clb_Qid a t ht u]
  have h0 : u 0 - a * (1 - 1 / ((t : ℝ) + 1)) = 0 := by
    rw [hu 0 (by omega)]; simp
  have h1 : u (t - 1) - a * (1 - (((t - 1 : ℕ) : ℝ) + 1) / ((t : ℝ) + 1)) = 0 := by
    rw [hu (t - 1) (by omega)]; ring
  have h2 : ∀ r ∈ Finset.Ico 1 t,
      ((u (r - 1) - a * (1 - (((r - 1 : ℕ) : ℝ) + 1) / ((t : ℝ) + 1))) -
            (u r - a * (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)))) ^ 2 = 0 := by
    intro r hr
    have hr' := Finset.mem_Ico.1 hr
    rw [hu (r - 1) (by omega), hu r hr'.2]
    ring
  rw [h0, h1, Finset.sum_congr rfl h2]
  simp

theorem solution {m d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d)
    (t : ℕ) (hm : 2 ≤ m) (ht : 1 ≤ t) (htk : t ≤ k + 1)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ))) :
    (∀ y : CompositeLB.DetLip.E d, Fsum m a v t (xstarT a v t) ≤ Fsum m a v t y) ∧
    Fsum m a v t (xstarT a v t) =
      -(a ^ 2 * ((m / 2 : ℕ) : ℝ) / (8 * (m : ℝ))) *
        (1 - 1 / ((t : ℝ) + 1)) := by
  have hK : (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) / (8 * (m : ℝ)) := by positivity
  have hF : ∀ y : CompositeLB.DetLip.E d, Fsum m a v t y =
      ((m / 2 : ℕ) : ℝ) / (8 * (m : ℝ)) * clbQ a t (fun j => inner ℝ y (v j)) := fun y => rfl
  have hstar : clbQ a t (fun j => inner ℝ (xstarT a v t) (v j)) = -(a ^ 2 * t / ((t : ℝ) + 1)) :=
    clb_Q_eq a t ht _ (fun j hj => clb_coord a v hv t htk j hj)
  constructor
  · intro y
    rw [hF, hF, hstar]
    exact mul_le_mul_of_nonneg_left (clb_Q_ge a t ht _) hK
  · rw [hF, hstar]
    have hT : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      exact this.ne'
    field_simp
    ring
