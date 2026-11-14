-- Prove2me | solution 1 for FullForesight.Randomized.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:55:03.619883+00:00
-- url     : https://prove2.me/submissions/5d110ab9-8f3c-4e21-a131-34ef7a9531fc

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants
import Definitions.Def_FullForesight_Randomized_IntervalSelection
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_consecutiveIntervalGap

namespace FullForesight.Randomized.Bridge

/-- The two encodings of `Ψ` agree. -/
theorem Psi_eq_psi (ξ : ℝ) : Psi ξ = ConsistentSubmodular.psi ξ := rfl

/-- The two encodings of `ξ⋆` agree: `Ψ` has no root at the endpoints `1/2` and `1`,
so the root set on `[1/2, 1]` is the root set on `(1/2, 1)`. -/
theorem xiStar_eq : xiStar = ConsistentSubmodular.xiStar := by
  unfold xiStar ConsistentSubmodular.xiStar
  congr 1
  ext ξ
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Psi_eq_psi]
  constructor
  · rintro ⟨⟨h1, h2⟩, h0⟩
    refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, h0⟩
    · rintro rfl
      norm_num [ConsistentSubmodular.psi] at h0
    · rintro rfl
      norm_num [ConsistentSubmodular.psi] at h0
  · rintro ⟨h1, h2, h0⟩
    exact ⟨⟨h1.le, h2.le⟩, h0⟩

end FullForesight.Randomized.Bridge

namespace FullForesight.Randomized.Bridge

open ConsistentSubmodular

/-- An interval-selection instance of the mission, as an `IntervalInstance` of the source
development. -/
def toInterval {N : ℕ} {ℓ r p : Fin (N + 1) → ℝ} (h : IsIntervalInstance ℓ r p) :
    IntervalInstance N where
  left := ℓ
  right := r
  prob := p
  left_nonneg i := (h.1 i).1
  left_le_right i := (h.1 i).2
  prob_nonneg := h.2.1
  prob_sum := h.2.2

theorem isIntervalInstance {N : ℕ} (I : IntervalInstance N) :
    IsIntervalInstance I.left I.right I.prob :=
  ⟨fun i => ⟨I.left_nonneg i, I.left_le_right i⟩, I.prob_nonneg, I.prob_sum⟩

theorem gap_eq {N : ℕ} (I : IntervalInstance N) :
    gap I.left I.right I.prob = I.adaptivityGap := rfl

theorem equalizing_iff {N : ℕ} (I : IntervalInstance N) :
    IsEqualizing I.left I.right I.prob ↔ I.IsEqualizing := Iff.rfl

theorem noninc_iff {N : ℕ} (I : IntervalInstance N) :
    IsNonincConsecutive I.left I.right ↔ I.IsNonincreasingConsecutive := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨h0, h1, fun i => h2 (Fin.castSucc_lt_succ).le, h3 _⟩
  · rintro ⟨h0, h1, h2, h3⟩
    have hanti : Antitone (fun i => I.right i - I.left i) := Fin.antitone_iff_succ_le.2 h2
    exact ⟨h0, h1, hanti, fun i => lt_of_lt_of_le h3 (hanti (Fin.le_last i))⟩

end FullForesight.Randomized.Bridge

namespace FullForesight.Randomized.Bridge

open ConsistentSubmodular

/-- The two encodings of `u₁` agree: `Φ(0) = 2` and `Φ(1) = -1` are nonzero, so the root set of
`Φ` on `[0, 1]` is the single root in `(0, 1)`. -/
theorem u1_eq {u : ℝ} (h0 : 0 < u) (h1 : u < 1) (hphi : phi u = 0)
    (huniq : ∀ x : ℝ, 0 < x → x < 1 → phi x = 0 → x = u) : u1 = u := by
  have hset : {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ Phi x = 0} = {u} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, hx⟩
      have hx' : phi x = 0 := hx
      refine huniq x (lt_of_le_of_ne hx0 ?_) (lt_of_le_of_ne hx1 ?_) hx'
      · rintro rfl
        norm_num [phi] at hx'
      · rintro rfl
        norm_num [phi] at hx'
    · rintro rfl
      exact ⟨⟨h0.le, h1.le⟩, hphi⟩
  unfold u1
  rw [hset, csSup_singleton]

/-- The equalizing distribution of the three intervals `[0,1]`, `[1,1+u]`, `[1+u,1+u+w]` is
unique. -/
theorem equalizing_unique {u w : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hw : 0 < w)
    (p q : Fin (2 + 1) → ℝ)
    (hp : IsIntervalInstance ![0, 1, 1 + u] ![1, 1 + u, 1 + u + w] p)
    (hpe : IsEqualizing ![0, 1, 1 + u] ![1, 1 + u, 1 + u + w] p)
    (hq : IsIntervalInstance ![0, 1, 1 + u] ![1, 1 + u, 1 + u + w] q)
    (hqe : IsEqualizing ![0, 1, 1 + u] ![1, 1 + u, 1 + u + w] q) : p = q := by
  have key : ∀ p : Fin (2 + 1) → ℝ,
      IsIntervalInstance ![0, 1, 1 + u] ![1, 1 + u, 1 + u + w] p →
      IsEqualizing ![0, 1, 1 + u] ![1, 1 + u, 1 + u + w] p →
      p 0 = w ∧ p 1 = w / u - w ∧ p 2 = 1 - w / u := by
    intro p hp hpe
    have hsum := hp.2.2
    have e01 := hpe 0 1
    have e12 := hpe 1 2
    simp only [fixedValue, val] at e01 e12
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at e01 e12
    rw [Fin.sum_univ_three] at hsum
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e01 e12
    have m1 : max (0 : ℝ) (1 - max 0 0) = 1 := by norm_num
    have m2 : max (0 : ℝ) (1 - max 0 1) = 0 := by norm_num
    have m3 : max (0 : ℝ) (1 - max 0 (1 + u)) = 0 := by
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 + u), max_eq_left (by linarith)]
    have m4 : max (0 : ℝ) (1 + u - max 1 0) = u := by
      rw [max_eq_left (by norm_num : (0 : ℝ) ≤ 1), max_eq_right (by linarith)]; ring
    have m5 : max (0 : ℝ) (1 + u - max 1 1) = u := by
      rw [max_self, max_eq_right (by linarith)]; ring
    have m6 : max (0 : ℝ) (1 + u - max 1 (1 + u)) = 0 := by
      rw [max_eq_right (by linarith : (1 : ℝ) ≤ 1 + u), sub_self, max_self]
    have m7 : max (0 : ℝ) (1 + u + w - max (1 + u) 0) = w := by
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 + u), max_eq_right (by linarith)]; ring
    have m8 : max (0 : ℝ) (1 + u + w - max (1 + u) 1) = w := by
      rw [max_eq_left (by linarith : (1 : ℝ) ≤ 1 + u), max_eq_right (by linarith)]; ring
    have m9 : max (0 : ℝ) (1 + u + w - max (1 + u) (1 + u)) = w := by
      rw [max_self, max_eq_right (by linarith)]; ring
    rw [m1, m2, m3, m4, m5, m6] at e01
    rw [m4, m5, m6, m7, m8, m9] at e12
    have hu : u ≠ 0 := hu0.ne'
    have hw' : w ≠ 0 := hw.ne'
    have a1 : (1 - u) * p 0 = u * p 1 := by linarith
    have a2 : (u - w) * (p 0 + p 1) = w * p 2 := by linarith
    have a3 : (p 0 + p 1) * u = w := by nlinarith
    have a4 : p 0 = w := by nlinarith
    have a5 : p 1 = w / u - w := by
      field_simp
      nlinarith
    refine ⟨a4, a5, ?_⟩
    linarith
  obtain ⟨p0, p1, p2⟩ := key p hp hpe
  obtain ⟨q0, q1, q2⟩ := key q hq hqe
  funext i
  fin_cases i
  · exact p0.trans q0.symm
  · exact p1.trans q1.symm
  · exact p2.trans q2.symm

end FullForesight.Randomized.Bridge

open FullForesight.Randomized FullForesight.Randomized.Bridge in
theorem solution :
    (∀ (N : ℕ) (ℓ r p : Fin (N + 1) → ℝ), IsIntervalInstance ℓ r p →
        IsNonincConsecutive ℓ r → IsEqualizing ℓ r p → xiStar ≤ gap ℓ r p) ∧
      (0 < u1 ∧ u1 < 1 ∧ Phi u1 = 0 ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1, Phi x = 0 → x = u1) ∧
      (∃ p : Fin (2 + 1) → ℝ,
        IsIntervalInstance ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p ∧
          IsEqualizing ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p) ∧
      (∀ p : Fin (2 + 1) → ℝ,
        IsIntervalInstance ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p →
          IsEqualizing ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p →
            gap ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p = xiStar) := by
  obtain ⟨hgap, u, w, hu0, hu1, hphi, huniq, hw, I, hI, hE, hIgap, hl, hr, -⟩ :=
    ConsistentSubmodular.consecutiveIntervalGap
  have hu : u1 = u := u1_eq hu0 hu1 hphi huniq
  have hw2 : u2 = w := by unfold u2; rw [hu, hw]
  have hwpos : 0 < w := by rw [hw]; positivity
  have hinst := isIntervalInstance I
  have heq := (equalizing_iff I).2 hE
  rw [hl, hr] at hinst heq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N ℓ r p hp hnc he
    rw [xiStar_eq]
    exact hgap N (toInterval hp) ((noninc_iff (toInterval hp)).1 hnc) he
  · rw [hu]
    exact ⟨hu0, hu1, hphi, fun x hx h => huniq x hx.1 hx.2 h⟩
  · rw [hu, hw2]
    exact ⟨I.prob, hinst, heq⟩
  · rw [hu, hw2]
    intro p hp hpe
    have hpI : p = I.prob := equalizing_unique hu0 hu1 hwpos p I.prob hp hpe hinst heq
    rw [hpI, xiStar_eq, ← hIgap, ← gap_eq I, hl, hr]
