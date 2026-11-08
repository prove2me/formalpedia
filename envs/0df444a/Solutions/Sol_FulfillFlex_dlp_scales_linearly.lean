-- Prove2me | solution 1 for FulfillFlex.dlp_scales_linearly
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:03:22.483645+00:00
-- url     : https://prove2.me/submissions/85c3e89b-e52b-4e9e-9182-e12bf9875d5a

import Mathlib
import Definitions.Def_FulfillFlex_Assumption1
import Definitions.Def_FulfillFlex_dlpValue

open scoped Pointwise

namespace Aux_FulfillFlexScale
open FulfillFlex

lemma feas_scale {N : ℕ} (A : Set (DC N × DC N)) (α : DC N → unitInterval)
    (m r : DC N → ℝ) (f : DC N → DC N → ℝ) (l : DC N → ℝ) (t : ℝ) (ht : 0 < t)
    (H : DLPFeasible A α m r f l) : DLPFeasible A α (t • m) (t • r) (t • f) (t • l) := by
  constructor
  · intro j
    have h := H.demand j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← mul_add]
    exact mul_le_mul_of_nonneg_left h ht.le
  · intro j
    have h := H.spillover j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    have e : (1 - (α j : ℝ)) * (t * m j - t * f j j) = t * ((1 - (α j : ℝ)) * (m j - f j j)) := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h ht.le
  · intro j
    have h := H.capacity j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h ht.le
  · intro j j' hj
    simp only [Pi.smul_apply, smul_eq_mul, H.link j j' hj, mul_zero]
  · intro j j'
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg ht.le (H.flow_nonneg j j')
  · intro j
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg ht.le (H.lost_nonneg j)

lemma obj_scale {N : ℕ} (c : DC N → DC N → ℝ) (p : DC N → ℝ) (f : DC N → DC N → ℝ)
    (l : DC N → ℝ) (t : ℝ) : dlpObjective c p (t • f) (t • l) = t * dlpObjective c p f l := by
  unfold dlpObjective
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl (fun j' _ => by ring)

end Aux_FulfillFlexScale

open FulfillFlex Aux_FulfillFlexScale in
theorem solution {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ)
    (p : DC N → ℝ) (α : DC N → unitInterval) (m r : DC N → ℝ) (hA1 : Assumption1 A c p)
    (hm : ∀ j, 0 ≤ m j) (hr : ∀ j, 0 ≤ r j) :
    (∀ s : ℝ, 0 < s → dlpValue A c p α (s • m) (s • r) = s * dlpValue A c p α m r) ∧
      ((∃ j, 0 < m j) → 0 < dlpValue A c p α m r) := by
  refine ⟨fun s hs => ?_, fun ⟨j0, hj0⟩ => ?_⟩
  · unfold dlpValue
    have hset : {v | ∃ f l, DLPFeasible A α (s • m) (s • r) f l ∧ v = dlpObjective c p f l} =
        s • {v | ∃ f l, DLPFeasible A α m r f l ∧ v = dlpObjective c p f l} := by
      ext v
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨f, l, hF, rfl⟩
        refine ⟨s⁻¹ * dlpObjective c p f l, ⟨s⁻¹ • f, s⁻¹ • l, ?_, ?_⟩, ?_⟩
        · have := feas_scale A α _ _ f l s⁻¹ (inv_pos.mpr hs) hF
          rwa [smul_smul, smul_smul, inv_mul_cancel₀ hs.ne', one_smul, one_smul] at this
        · rw [obj_scale]
        · rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
      · rintro ⟨w, ⟨f, l, hF, rfl⟩, rfl⟩
        exact ⟨s • f, s • l, feas_scale A α m r f l s hs hF, by rw [obj_scale, smul_eq_mul]⟩
    rw [hset, Real.sInf_smul_of_nonneg hs.le, smul_eq_mul]
  · have hL : ∀ v ∈ {v | ∃ f l, DLPFeasible A α m r f l ∧ v = dlpObjective c p f l},
        ∑ j, c j j * m j ≤ v := by
      rintro v ⟨f, l, hF, rfl⟩
      unfold dlpObjective
      rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun j j' => c j j' * f j j')]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have h1 : c j j * l j ≤ p j * l j :=
        mul_le_mul_of_nonneg_right (hA1.local_le_lost j) (hF.lost_nonneg j)
      have h2 : ∀ j', c j j * f j' j ≤ c j' j * f j' j := by
        intro j'
        by_cases hj : (j', j) ∈ A
        · exact mul_le_mul_of_nonneg_right (hA1.local_le_link j' j hj) (hF.flow_nonneg j' j)
        · rw [hF.link j' j hj, mul_zero, mul_zero]
      have h3 : c j j * ∑ j', f j' j ≤ ∑ j', c j' j * f j' j := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun j' _ => h2 j')
      have h4 : c j j * m j ≤ c j j * (l j + ∑ j', f j' j) :=
        mul_le_mul_of_nonneg_left (hF.demand j) (hA1.local_pos j).le
      nlinarith
    have hne : {v | ∃ f l, DLPFeasible A α m r f l ∧ v = dlpObjective c p f l}.Nonempty := by
      refine ⟨_, 0, m, ?_, rfl⟩
      constructor
      · intro j; simp
      · intro j
        simp only [Pi.zero_apply, Finset.sum_const_zero, sub_zero]
        exact mul_nonneg (by linarith [(α j).2.2]) (hm j)
      · intro j; simpa using hr j
      · intro j j' _; rfl
      · intro j j'; exact le_refl _
      · exact hm
    have hpos : 0 < ∑ j, c j j * m j := by
      have hnn : ∀ j ∈ Finset.univ, 0 ≤ c j j * m j :=
        fun j _ => mul_nonneg (hA1.local_pos j).le (hm j)
      calc (0:ℝ) < c j0 j0 * m j0 := mul_pos (hA1.local_pos j0) hj0
        _ ≤ ∑ j, c j j * m j := Finset.single_le_sum hnn (Finset.mem_univ j0)
    unfold dlpValue
    exact lt_of_lt_of_le hpos (le_csInf hne hL)
