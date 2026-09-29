-- Prove2me | solution 1 for FirstOrderOpt.OperatorSliding.ps_procedure_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:23:03.375526+00:00
-- url     : https://prove2.me/submissions/6d2e950e-3f52-4ba0-a970-07f1e0b43ef9

import Mathlib

namespace FirstOrderOpt.OperatorSliding

open scoped RealInnerProductSpace

/-- `P t = (1/2)^t`. -/
noncomputable def aux_psb_P (t : ℕ) : ℝ := ((1 : ℝ) / 2) ^ t

/-- `θ t` given by (8.1.20). -/
noncomputable def aux_psb_θ (t : ℕ) : ℝ :=
  (aux_psb_P (t - 1) - aux_psb_P t) / ((1 - aux_psb_P t) * aux_psb_P (t - 1))

/-- The prox iterates `u t = 2 - 2 (1/2)^t`. -/
noncomputable def aux_psb_u (t : ℕ) : ℝ := 2 - 2 * ((1 : ℝ) / 2) ^ t

/-- The averaged iterates. -/
noncomputable def aux_psb_ut : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - aux_psb_θ (n + 1)) • aux_psb_ut n + aux_psb_θ (n + 1) • aux_psb_u (n + 1)

/-- The nonconvex function `g`, linear except for a spike at `4/3`. -/
noncomputable def aux_psb_g (w : ℝ) : ℝ := -2 * w + if w = 4 / 3 then 10 else 0

theorem aux_psb_Prec (t : ℕ) (ht : 1 ≤ t) :
    aux_psb_P t = (fun _ : ℕ => (1 : ℝ)) t * (1 + (fun _ : ℕ => (1 : ℝ)) t)⁻¹ *
      aux_psb_P (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [aux_psb_P, Nat.add_sub_cancel, pow_succ]
  ring

theorem aux_psb_u_ne (t : ℕ) : aux_psb_u t ≠ 4 / 3 := by
  intro h
  unfold aux_psb_u at h
  rcases t with _ | _ | s
  · norm_num at h
  · norm_num at h
  · have h1 : ((1 : ℝ) / 2) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : ((1 : ℝ) / 2) ^ (s + 2) = ((1 : ℝ) / 2) ^ s * (1 / 4) := by
      rw [pow_add]; norm_num
    rw [h2] at h
    nlinarith

theorem aux_psb_g_ge (w : ℝ) : -2 * w ≤ aux_psb_g w := by
  unfold aux_psb_g
  split_ifs <;> linarith

theorem aux_psb_g_u (t : ℕ) : aux_psb_g (aux_psb_u t) = -2 * aux_psb_u t := by
  unfold aux_psb_g
  rw [if_neg (aux_psb_u_ne t)]
  ring

theorem aux_psb_three (t : ℕ) (ht : 1 ≤ t) (w : ℝ) :
    aux_psb_g (aux_psb_u t) + (fun _ _ => (0 : ℝ)) (aux_psb_u (t - 1)) (aux_psb_u t)
        + 1 * ((fun a b : ℝ => (1 / 2) * (b - a) ^ 2) 0 (aux_psb_u t))
        + (fun _ => (0 : ℝ)) (aux_psb_u t)
        + 1 * (fun _ : ℕ => (1 : ℝ)) t *
          ((fun a b : ℝ => (1 / 2) * (b - a) ^ 2) (aux_psb_u (t - 1)) (aux_psb_u t)) ≤
      aux_psb_g w + (fun _ _ => (0 : ℝ)) (aux_psb_u (t - 1)) w
        + 1 * ((fun a b : ℝ => (1 / 2) * (b - a) ^ 2) 0 w) + (fun _ => (0 : ℝ)) w
        + 1 * (fun _ : ℕ => (1 : ℝ)) t *
          ((fun a b : ℝ => (1 / 2) * (b - a) ^ 2) (aux_psb_u (t - 1)) w)
        - 1 * (1 + (fun _ : ℕ => (1 : ℝ)) t) *
          ((fun a b : ℝ => (1 / 2) * (b - a) ^ 2) (aux_psb_u t) w) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hg := aux_psb_g_ge w
  rw [aux_psb_g_u]
  simp only [Nat.add_sub_cancel]
  have hu1 : aux_psb_u (s + 1) = 2 - ((1 : ℝ) / 2) ^ s := by
    unfold aux_psb_u; rw [pow_succ]; ring
  have hu0 : aux_psb_u s = 2 - 2 * ((1 : ℝ) / 2) ^ s := rfl
  rw [hu1, hu0]
  nlinarith [hg]

end FirstOrderOpt.OperatorSliding

open FirstOrderOpt.OperatorSliding

open scoped RealInnerProductSpace

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (g h chi : E → ℝ) (lh : E → E → ℝ) (V : E → E → ℝ)
    (x : E) (β M : ℝ) (hβ : 0 < β) (hM : 0 < M)
    (hVnonneg : ∀ a b, 0 ≤ V a b)
    (hVstrong : ∀ a b, (1 / 2) * ‖b - a‖ ^ 2 ≤ V a b)
    (hMLip : ∀ y ∈ X, ∀ z ∈ X, h z ≤ lh y z + M * ‖z - y‖)
    (Φ : E → ℝ) (hΦ : ∀ u, Φ u = g u + h u + β * V x u + chi u)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t)
    (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (u ũ : ℕ → E) (hu0 : u 0 = x) (hũ0 : ũ 0 = x) (hmem : ∀ t, u t ∈ X)
    (huThreePoint : ∀ t : ℕ, 1 ≤ t → ∀ w ∈ X,
      g (u t) + lh (u (t - 1)) (u t) + β * V x (u t) + chi (u t)
          + β * p t * V (u (t - 1)) (u t) ≤
        g w + lh (u (t - 1)) w + β * V x w + chi w + β * p t * V (u (t - 1)) w
          - β * (1 + p t) * V (u t) w)
    (hũrec : ∀ t : ℕ, 1 ≤ t → ũ t = (1 - θ t) • ũ (t - 1) + θ t • u t)
    (t : ℕ) (ht : 1 ≤ t) (w : E) (hw : w ∈ X),
    β * (1 - P t)⁻¹ * V (u t) w + (Φ (ũ t) - Φ w) ≤
      P t * (1 - P t)⁻¹ *
        (β * V x w + (M ^ 2 / (2 * β)) * ∑ i ∈ Finset.Icc 1 t, (p i ^ 2 * P (i - 1))⁻¹)) := by
  intro H
  have key := H (E := ℝ) Set.univ aux_psb_g (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
    (fun a b => (1 / 2) * (b - a) ^ 2) 0 1 1 one_pos one_pos
    (fun a b => by positivity)
    (fun a b => by rw [Real.norm_eq_abs, sq_abs])
    (fun y _ z _ => by positivity)
    (fun u => aux_psb_g u + 0 + 1 * ((1 / 2) * (u - 0) ^ 2) + 0) (fun _ => rfl)
    (fun _ => 1) aux_psb_θ aux_psb_P (fun _ => one_pos) (by simp [aux_psb_P])
    aux_psb_Prec (fun _ _ => rfl)
    aux_psb_u aux_psb_ut (by simp [aux_psb_u]) rfl (fun _ => Set.mem_univ _)
    (fun t ht w _ => aux_psb_three t ht w)
    (fun t ht => by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rfl)
    2 (by norm_num) 0 (Set.mem_univ _)
  have hθ1 : aux_psb_θ 1 = 1 := by norm_num [aux_psb_θ, aux_psb_P]
  have hθ2 : aux_psb_θ 2 = 2 / 3 := by norm_num [aux_psb_θ, aux_psb_P]
  have hut2 : aux_psb_ut 2 = 4 / 3 := by
    simp only [aux_psb_ut, hθ1, hθ2, aux_psb_u, smul_eq_mul]
    norm_num
  have hg43 : aux_psb_g (4 / 3) = -8 / 3 + 10 := by
    unfold aux_psb_g; rw [if_pos rfl]; ring
  have hg0 : aux_psb_g 0 = 0 := by
    unfold aux_psb_g; rw [if_neg (by norm_num)]; ring
  rw [hut2, hg43, hg0] at key
  have hs : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [hs] at key
  norm_num [aux_psb_P, aux_psb_u] at key
