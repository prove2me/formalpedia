-- Prove2me | solution 1 for CalibratedCE.Generic.ae_Mb_strict_interior
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:54:05.484423+00:00
-- url     : https://prove2.me/submissions/5b4126a0-44ab-4700-8ca5-07ea900ddb09

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game

namespace CalibratedCE.Generic

open MeasureTheory Set

/-- Strict-interior property for action `a`. -/
def aux_msi_S {m n : ℕ} (u : Fin m → Fin n → ℝ) (a : Fin m) : Prop :=
  ∃ p : Fin n → ℝ, (∀ b, 0 < p b) ∧ ∑ b, p b = 1 ∧
    ∀ a', a' ≠ a → ∑ b, p b * u a' b < ∑ b, p b * u a b

theorem aux_msi_key {m n : ℕ} (u : Fin m → Fin n → ℝ) (a : Fin m) (hN : (Mb u a).Nonempty)
    (ε : ℝ) (hε : 0 < ε) (w : Fin m → Fin n → ℝ)
    (hw : ∀ a' b, w a' b = u a' b + if a' = a then ε else 0) : aux_msi_S w a := by
  obtain ⟨p, ⟨hp0, hp1⟩, hpa⟩ := hN
  set K : ℝ := ∑ a', ∑ b, |u a b - u a' b| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set δ : ℝ := ε / (K + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hδK : δ * K < ε := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  set D : ℝ := 1 + (n : ℝ) * δ with hD
  have hD0 : 0 < D := by
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  refine ⟨fun b => (p b + δ) / D, fun b => div_pos (by linarith [hp0 b]) hD0, ?_, ?_⟩
  · rw [← Finset.sum_div, Finset.sum_add_distrib, hp1, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, div_self hD0.ne']
  · intro a' ha'
    have hsum : ∀ c : Fin n → ℝ, ∑ b, (p b + δ) / D * c b
        = (∑ b, p b * c b + δ * ∑ b, c b) / D := by
      intro c
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hwa' : ∀ b, w a' b = u a' b := fun b => by rw [hw, if_neg ha', add_zero]
    have hwa : ∀ b, w a b = u a b + ε := fun b => by rw [hw, if_pos rfl]
    simp only [hwa', hwa]
    rw [hsum, hsum, div_lt_div_iff_of_pos_right hD0]
    have h1 := hpa a'
    have h2 : ∑ b, p b * (u a b + ε) = ∑ b, p b * u a b + ε := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
    have h3 : ∑ b, (u a b + ε) = ∑ b, u a b + n * ε := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have h4 : ∑ b, u a' b - ∑ b, u a b ≤ K := by
      calc ∑ b, u a' b - ∑ b, u a b = ∑ b, (u a' b - u a b) := by
            rw [Finset.sum_sub_distrib]
        _ ≤ ∑ b, |u a b - u a' b| := Finset.sum_le_sum fun b _ => by
            rw [abs_sub_comm]; exact le_abs_self _
        _ ≤ K := Finset.single_le_sum (f := fun a' => ∑ b, |u a b - u a' b|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a')
    have h5 : δ * (∑ b, u a' b - ∑ b, u a b) ≤ δ * K := mul_le_mul_of_nonneg_left h4 hδ0.le
    have h6 : 0 ≤ δ * (n * ε) := by positivity
    rw [h2, h3]
    nlinarith

theorem aux_msi_open {m n : ℕ} (a : Fin m) : IsOpen {u : Fin m → Fin n → ℝ | aux_msi_S u a} := by
  have : {u : Fin m → Fin n → ℝ | aux_msi_S u a} =
      ⋃ p : {p : Fin n → ℝ // (∀ b, 0 < p b) ∧ ∑ b, p b = 1}, ⋂ a' : Fin m, ⋂ (_ : a' ≠ a),
        {u : Fin m → Fin n → ℝ | ∑ b, p.1 b * u a' b < ∑ b, p.1 b * u a b} := by
    ext u
    simp only [aux_msi_S, mem_setOf_eq, mem_iUnion, mem_iInter, Subtype.exists, exists_prop]
    constructor
    · rintro ⟨p, h1, h2, h3⟩; exact ⟨p, ⟨h1, h2⟩, h3⟩
    · rintro ⟨p, ⟨h1, h2⟩, h3⟩; exact ⟨p, h1, h2, h3⟩
  rw [this]
  refine isOpen_iUnion fun p => isOpen_iInter_of_finite fun a' => isOpen_iInter_of_finite
    fun _ => isOpen_lt (by fun_prop) (by fun_prop)

theorem aux_msi_closed {m n : ℕ} (a : Fin m) :
    IsClosed {u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} := by
  have : {u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} =
      Prod.fst '' {x : (Fin m → Fin n → ℝ) × stdSimplex ℝ (Fin n) |
        ∀ a', ∑ b, (x.2 : Fin n → ℝ) b * x.1 a' b ≤ ∑ b, (x.2 : Fin n → ℝ) b * x.1 a b} := by
    ext u
    simp only [mem_setOf_eq, mem_image, Prod.exists, exists_and_right, exists_eq_right,
      Subtype.exists]
    constructor
    · rintro ⟨p, hp, hpa⟩; exact ⟨p, hp, hpa⟩
    · rintro ⟨p, hp, hpa⟩; exact ⟨p, hp, hpa⟩
  rw [this]
  refine isClosedMap_fst_of_compactSpace _ ?_
  simp only [setOf_forall]
  refine isClosed_iInter fun a' => isClosed_le ?_ ?_
  · exact continuous_finset_sum _ fun b _ =>
      ((continuous_apply b).comp (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_apply b).comp ((continuous_apply a').comp continuous_fst))
  · exact continuous_finset_sum _ fun b _ =>
      ((continuous_apply b).comp (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_apply b).comp ((continuous_apply a).comp continuous_fst))

theorem aux_msi_null {m n : ℕ} (a : Fin m) :
    volume ({u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} \ {u | aux_msi_S u a}) = 0 := by
  set V : Fin m → Fin n → ℝ := fun a' _ => if a' = a then 1 else 0 with hV
  set c : ℕ → Fin m → Fin n → ℝ := fun j => ((1 : ℝ) / (j + 1)) • V with hc
  refine Measure.addHaar_eq_zero_of_disjoint_translates volume c ?_ ?_
    ((aux_msi_closed a).measurableSet.diff (aux_msi_open a).measurableSet)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨‖V‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    rw [hc, norm_smul]
    have : ‖(1 : ℝ) / (j + 1)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [div_le_one (by positivity)]
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    calc ‖(1 : ℝ) / (j + 1)‖ * ‖V‖ ≤ 1 * ‖V‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖V‖ := one_mul _
  · -- key step: two translates in direction `V` of a bad point cannot both be bad
    have step : ∀ (y₁ y₂ : Fin m → Fin n → ℝ) (ε : ℝ), 0 < ε →
        (∀ a' b, y₁ a' b = y₂ a' b + if a' = a then ε else 0) →
        y₂ ∈ {u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} \ {u | aux_msi_S u a} →
        y₁ ∈ {u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} \ {u | aux_msi_S u a} → False := by
      intro y₁ y₂ ε hε h h₂ h₁
      exact h₁.2 (aux_msi_key y₂ a h₂.1 ε hε y₁ h)
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro x hx₁ hx₂
    rw [Set.singleton_add] at hx₁ hx₂
    obtain ⟨y₁, hy₁, rfl⟩ := hx₁
    obtain ⟨y₂, hy₂, hxy⟩ := hx₂
    have hcoord : ∀ a' b, c j a' b + y₂ a' b = c i a' b + y₁ a' b := fun a' b => by
      have := congrFun (congrFun hxy a') b
      simpa using this
    have hti : ((1 : ℝ) / (i + 1)) ≠ 1 / (j + 1) := by
      intro h
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul, one_mul] at h
      exact hij (by exact_mod_cast (add_right_cancel h).symm)
    rcases lt_or_gt_of_ne hti with hlt | hlt
    · refine step y₁ y₂ (1 / (j + 1) - 1 / (i + 1)) (by linarith) (fun a' b => ?_) hy₂ hy₁
      have := hcoord a' b
      simp only [hc, hV, Pi.smul_apply, smul_eq_mul] at this
      split_ifs at this ⊢ <;> linarith
    · refine step y₂ y₁ (1 / (i + 1) - 1 / (j + 1)) (by linarith) (fun a' b => ?_) hy₁ hy₂
      have := hcoord a' b
      simp only [hc, hV, Pi.smul_apply, smul_eq_mul] at this
      split_ifs at this ⊢ <;> linarith

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem solution (m n : ℕ) :
    ∀ᵐ u₁ : Fin m → Fin n → ℝ ∂MeasureTheory.volume, ∀ a, (Mb u₁ a).Nonempty →
      ∃ p : Fin n → ℝ, (∀ b, 0 < p b) ∧ ∑ b, p b = 1 ∧
        ∀ a', a' ≠ a → ∑ b, p b * u₁ a' b < ∑ b, p b * u₁ a b := by
  refine MeasureTheory.ae_all_iff.2 fun a => ?_
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (fun u hu => ?_) (aux_msi_null (n := n) a)
  simp only [Set.mem_setOf_eq, _root_.not_imp] at hu
  exact ⟨hu.1, hu.2⟩
