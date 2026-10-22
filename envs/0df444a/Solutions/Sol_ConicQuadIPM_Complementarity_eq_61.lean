-- Prove2me | solution 1 for ConicQuadIPM.Complementarity.eq_61
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:04:46.558031+00:00
-- url     : https://prove2.me/submissions/bebccfcd-3f3f-48dd-84e9-13e183d442c0

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting
set_option autoImplicit false
open Matrix ConicQuadIPM.Complementarity

lemma cq_arrow_e1 {d : ℕ} (b : Fin d → ℝ) : arrow b *ᵥ e1 = b := by
  ext j
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single (⟨0, j.pos⟩ : Fin d)]
  · simp only [arrow, e1, mul_one]
    by_cases hj : j.val = 0
    · have : j = ⟨0, j.pos⟩ := Fin.ext hj
      simp [hj, ← this]
    · simp [hj]
  · intro k _ hk
    have : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp [e1, this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma cq_e1_arrow {d : ℕ} (a b : Fin d → ℝ) : e1 ⬝ᵥ ((arrow a * arrow b) *ᵥ e1) = a ⬝ᵥ b := by
  rw [← mulVec_mulVec, cq_arrow_e1]
  by_cases hd : d = 0
  · subst hd; simp [dotProduct]
  · have hd' : 0 < d := Nat.pos_of_ne_zero hd
    simp only [dotProduct, mulVec]
    rw [Finset.sum_eq_single (⟨0, hd'⟩ : Fin d)]
    · simp only [e1, if_true, one_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp [arrow]
    · intro k _ hk
      have : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [e1, this]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma cq_sum_two {d : ℕ} (h2 : 2 ≤ d) (f : Fin d → ℝ) (hf : ∀ c : Fin d, 2 ≤ c.val → f c = 0) :
    ∑ c, f c = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  apply Finset.sum_eq_add (⟨0, by omega⟩ : Fin d) (⟨1, by omega⟩ : Fin d)
  · intro h; have := congrArg Fin.val h; simp at this
  · intro c _ hc
    apply hf
    have h0 : c.val ≠ 0 := fun h => hc.1 (Fin.ext h)
    have h1 : c.val ≠ 1 := fun h => hc.2 (Fin.ext h)
    omega
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

lemma cq_rot_apply {d : ℕ} (h2 : 2 ≤ d) (x : Fin d → ℝ) (c : Fin d) :
    (Tmat ConeKind.rot d *ᵥ x) c =
      if c.val = 0 then (1 / Real.sqrt 2) * x ⟨0, by omega⟩ + (1 / Real.sqrt 2) * x ⟨1, by omega⟩
      else if c.val = 1 then (1 / Real.sqrt 2) * x ⟨0, by omega⟩ - (1 / Real.sqrt 2) * x ⟨1, by omega⟩
      else x c := by
  simp only [mulVec, dotProduct]
  by_cases hc2 : 2 ≤ c.val
  · have h0 : c.val ≠ 0 := by omega
    have h1 : c.val ≠ 1 := by omega
    simp only [h0, h1, if_false]
    have : ∀ b : Fin d, Tmat ConeKind.rot d c b * x b = if c = b then x b else 0 := by
      intro b
      simp only [Tmat]
      have : ¬ (c.val < 2) := by omega
      simp [this]
    simp_rw [this]
    simp
  · push_neg at hc2
    rw [cq_sum_two h2]
    · rcases (by omega : c.val = 0 ∨ c.val = 1) with hc | hc
      · simp [Tmat, hc]
      · simp [Tmat, hc]
        ring
    · intro b hb
      simp only [Tmat]
      have : ¬ (b.val < 2) := by omega
      have hne : c ≠ b := fun h => by rw [h] at hc2; omega
      simp [this, hne]

lemma cq_T_dot (kind : ConeKind) (d : ℕ) (hwf : BlockWF kind d) (x s : Fin d → ℝ) :
    (Tmat kind d *ᵥ x) ⬝ᵥ (Tmat kind d *ᵥ s) = x ⬝ᵥ s := by
  cases kind
  · simp [Tmat]
  · simp [Tmat]
  · have h2 : 2 ≤ d := hwf.2.2 rfl
    have hr : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
    have hdiff : ∑ c, ((Tmat ConeKind.rot d *ᵥ x) c * (Tmat ConeKind.rot d *ᵥ s) c - x c * s c) = 0 := by
      rw [cq_sum_two h2]
      · rw [cq_rot_apply h2 x, cq_rot_apply h2 x, cq_rot_apply h2 s, cq_rot_apply h2 s]
        simp only [if_true, one_ne_zero, if_false]
        linear_combination (2 * (x ⟨0, by omega⟩ * s ⟨0, by omega⟩ + x ⟨1, by omega⟩ * s ⟨1, by omega⟩)) * hr
      · intro c hc
        rw [cq_rot_apply h2 x, cq_rot_apply h2 s]
        have h0 : c.val ≠ 0 := by omega
        have h1 : c.val ≠ 1 := by omega
        simp [h0, h1]
    rw [Finset.sum_sub_distrib] at hdiff
    unfold dotProduct
    linarith

theorem solution {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x s : (i : Fin k) → Fin (n i) → ℝ) :
    (∀ i,
      e1 ⬝ᵥ ((arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1)
        = (Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Tmat (kind i) (n i) *ᵥ s i) ∧
      (Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Tmat (kind i) (n i) *ᵥ s i) = x i ⬝ᵥ s i) ∧
    ∑ i, e1 ⬝ᵥ ((arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1)
      = ∑ i, x i ⬝ᵥ s i := by
  have h1 : ∀ i, e1 ⬝ᵥ ((arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1)
        = (Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Tmat (kind i) (n i) *ᵥ s i) := fun i => cq_e1_arrow _ _
  have h2 : ∀ i, (Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Tmat (kind i) (n i) *ᵥ s i) = x i ⬝ᵥ s i :=
    fun i => cq_T_dot (kind i) (n i) (hwf i) (x i) (s i)
  refine ⟨fun i => ⟨h1 i, h2 i⟩, ?_⟩
  exact Finset.sum_congr rfl (fun i _ => (h1 i).trans (h2 i))
