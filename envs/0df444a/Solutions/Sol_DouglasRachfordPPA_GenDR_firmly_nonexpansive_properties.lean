-- Prove2me | solution 1 for DouglasRachfordPPA.GenDR.firmly_nonexpansive_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:28:01.562778+00:00
-- url     : https://prove2.me/submissions/43d26687-5cb2-447c-81ff-d941bac14143

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

set_option autoImplicit false

open InnerProductSpace ThreeOpSplitting.Convergence

namespace FNE4613

open DouglasRachfordPPA.GenDR

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma key (a b : H) : ‖(2:ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 ↔ ‖b‖ ^ 2 ≤ ⟪a, b⟫_ℝ := by
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_comm]
  simp only [Real.norm_eq_abs, abs_two]
  constructor <;> intro h <;> nlinarith

lemma key2 (a b : H) : ‖b‖ ^ 2 ≤ ⟪a, b⟫_ℝ ↔ ‖a - b‖ ^ 2 ≤ ⟪a, a - b⟫_ℝ := by
  rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq]
  constructor <;> intro h <;> linarith

lemma mem_refl (J : H → Set H) (x w : H) :
    w ∈ opAdd (opSmul 2 J) (opSmul (-1) opId) x ↔ ∃ y ∈ J x, w = (2:ℝ) • y - x := by
  simp only [opAdd, opSmul, opId, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ⟨y, hy, rfl⟩, b, ⟨z, rfl, rfl⟩, rfl⟩
    exact ⟨y, hy, by simp [sub_eq_add_neg]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, _, ⟨x, rfl, rfl⟩, by simp [sub_eq_add_neg]⟩

lemma mem_compl (J : H → Set H) (x w : H) :
    w ∈ opAdd opId (opSmul (-1) J) x ↔ ∃ y ∈ J x, w = x - y := by
  simp only [opAdd, opSmul, opId, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl, b, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by simp [sub_eq_add_neg]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨x, rfl, _, ⟨y, hy, rfl⟩, by simp [sub_eq_add_neg]⟩

lemma mem_half (C : H → Set H) (x w : H) :
    w ∈ opSmul (1 / 2) (opAdd C opId) x ↔ ∃ c ∈ C x, w = (1 / 2 : ℝ) • (c + x) := by
  simp only [opAdd, opSmul, opId, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, ⟨c, hc, z, rfl, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, x, rfl, rfl⟩, rfl⟩

lemma part1 (J : H → Set H) (hJ : IsFirmlyNonexpansiveOp J) : IsNonexpansiveOp J := by
  intro x x' y y' hy hy'
  have h := hJ x x' y y' hy hy'
  have hcs := real_inner_le_norm (x' - x) (y' - y)
  have h0 := norm_nonneg (y' - y)
  have h1 := norm_nonneg (x' - x)
  nlinarith

lemma part2 (J : H → Set H) :
    IsFirmlyNonexpansiveOp J ↔ IsNonexpansiveOp (opAdd (opSmul 2 J) (opSmul (-1) opId)) := by
  constructor
  · intro hJ x x' w w' hw hw'
    obtain ⟨y, hy, rfl⟩ := (mem_refl J x w).1 hw
    obtain ⟨y', hy', rfl⟩ := (mem_refl J x' w').1 hw'
    have h := (key (x' - x) (y' - y)).2 (hJ x x' y y' hy hy')
    have e : (2:ℝ) • y' - x' - ((2:ℝ) • y - x) = (2:ℝ) • (y' - y) - (x' - x) := by
      rw [smul_sub]; abel
    rw [e]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
  · intro hC x x' y y' hy hy'
    have h := hC x x' _ _ ((mem_refl J x _).2 ⟨y, hy, rfl⟩) ((mem_refl J x' _).2 ⟨y', hy', rfl⟩)
    have e : (2:ℝ) • y' - x' - ((2:ℝ) • y - x) = (2:ℝ) • (y' - y) - (x' - x) := by
      rw [smul_sub]; abel
    rw [e] at h
    exact (key (x' - x) (y' - y)).1 (pow_le_pow_left₀ (norm_nonneg _) h 2)

lemma part3 (J : H → Set H) :
    IsFirmlyNonexpansiveOp J ↔
      ∃ C : H → Set H, IsNonexpansiveOp C ∧ J = opSmul (1 / 2) (opAdd C opId) := by
  constructor
  · intro hJ
    refine ⟨_, (part2 J).1 hJ, ?_⟩
    funext x
    ext w
    rw [mem_half]
    constructor
    · intro hw
      refine ⟨_, (mem_refl J x _).2 ⟨w, hw, rfl⟩, ?_⟩
      rw [sub_add_cancel, smul_smul]; norm_num
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨y, hy, rfl⟩ := (mem_refl J x c).1 hc
      rw [sub_add_cancel, smul_smul]; norm_num; exact hy
  · rintro ⟨C, hC, rfl⟩
    rw [part2]
    intro x x' w w' hw hw'
    obtain ⟨y, hy, rfl⟩ := (mem_refl _ x w).1 hw
    obtain ⟨y', hy', rfl⟩ := (mem_refl _ x' w').1 hw'
    obtain ⟨c, hc, rfl⟩ := (mem_half C x y).1 hy
    obtain ⟨c', hc', rfl⟩ := (mem_half C x' y').1 hy'
    have e1 : (2:ℝ) • ((1 / 2 : ℝ) • (c + x)) - x = c := by
      rw [smul_smul]; norm_num
    have e2 : (2:ℝ) • ((1 / 2 : ℝ) • (c' + x')) - x' = c' := by
      rw [smul_smul]; norm_num
    rw [e1, e2]
    exact hC x x' c c' hc hc'

lemma part4 (J : H → Set H) :
    IsFirmlyNonexpansiveOp J ↔ IsFirmlyNonexpansiveOp (opAdd opId (opSmul (-1) J)) := by
  constructor
  · intro hJ x x' w w' hw hw'
    obtain ⟨y, hy, rfl⟩ := (mem_compl J x w).1 hw
    obtain ⟨y', hy', rfl⟩ := (mem_compl J x' w').1 hw'
    have h := (key2 (x' - x) (y' - y)).1 (hJ x x' y y' hy hy')
    have e : x' - y' - (x - y) = (x' - x) - (y' - y) := by abel
    rw [e]; exact h
  · intro hK x x' y y' hy hy'
    have h := hK x x' _ _ ((mem_compl J x _).2 ⟨y, hy, rfl⟩) ((mem_compl J x' _).2 ⟨y', hy', rfl⟩)
    have e : x' - y' - (x - y) = (x' - x) - (y' - y) := by abel
    rw [e] at h
    exact (key2 (x' - x) (y' - y)).2 h

end FNE4613

open DouglasRachfordPPA.GenDR in
theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    (∀ J : H → Set H, IsFirmlyNonexpansiveOp J → IsNonexpansiveOp J) ∧
    (∀ J : H → Set H, IsFirmlyNonexpansiveOp J ↔
      IsNonexpansiveOp (opAdd (opSmul 2 J) (opSmul (-1) opId))) ∧
    (∀ J : H → Set H, IsFirmlyNonexpansiveOp J ↔
      ∃ C : H → Set H, IsNonexpansiveOp C ∧ J = opSmul (1 / 2) (opAdd C opId)) ∧
    (∀ J : H → Set H, IsFirmlyNonexpansiveOp J ↔
      IsFirmlyNonexpansiveOp (opAdd opId (opSmul (-1) J))) := by
  exact ⟨FNE4613.part1, FNE4613.part2, FNE4613.part3, FNE4613.part4⟩
