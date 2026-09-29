-- Prove2me | solution 1 for FoundationsML.MultiClass.kernel_rademacher_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:30:45.863976+00:00
-- url     : https://prove2.me/submissions/e446fb83-bd84-43f5-aa31-4eb03c2df21e

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_RademacherComplexity
import Definitions.Def_FoundationsML_MultiClass_EmpiricalRademacherComplexity
import Definitions.Def_FoundationsML_MultiClass_Proj1
import Definitions.Def_FoundationsML_MultiClass_IsPDS
import Definitions.Def_FoundationsML_MultiClass_KernelHypothesisClass

open MeasureTheory

namespace FoundationsML.MultiClass

/-- Sign flip at coordinate `i`. -/
def aux_krb_flip {m : ℕ} (i : Fin m) (σ : Fin m → Bool) : Fin m → Bool :=
  Function.update σ i (!σ i)

lemma aux_krb_flip_invol {m : ℕ} (i : Fin m) : Function.Involutive (aux_krb_flip i) := by
  intro σ
  funext l
  by_cases h : l = i
  · subst h; simp [aux_krb_flip]
  · simp [aux_krb_flip, Function.update_of_ne h]

lemma aux_krb_sign_sum (m : ℕ) (i j : Fin m) :
    ∑ σ : Fin m → Bool, (if σ i then (1:ℝ) else -1) * (if σ j then 1 else -1) =
      if i = j then (2:ℝ) ^ m else 0 := by
  by_cases hij : i = j
  · subst hij
    have : ∀ σ : Fin m → Bool, (if σ i then (1:ℝ) else -1) * (if σ i then 1 else -1) = 1 := by
      intro σ; split_ifs <;> norm_num
    simp only [this, if_true]
    simp [Fintype.card_bool]
  · rw [if_neg hij]
    set f : (Fin m → Bool) → ℝ :=
      fun σ => (if σ i then (1:ℝ) else -1) * (if σ j then 1 else -1) with hf
    have key : ∀ σ, f (aux_krb_flip i σ) = - f σ := by
      intro σ
      have h1 : aux_krb_flip i σ i = !σ i := by simp [aux_krb_flip]
      have h2 : aux_krb_flip i σ j = σ j := by
        simp [aux_krb_flip, Function.update_of_ne (Ne.symm hij)]
      simp only [hf, h1, h2]
      cases σ i <;> cases σ j <;> norm_num
    have hsum := Equiv.sum_comp (aux_krb_flip_invol i).toPerm f
    simp only [Function.Involutive.coe_toPerm, key, Finset.sum_neg_distrib] at hsum
    change ∑ σ, f σ = 0
    linarith

lemma aux_krb_norm_sq_sum {Hb : Type*} [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (m : ℕ) (u : Fin m → Hb) :
    ∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1:ℝ) else -1) • u i‖ ^ 2 =
      (2:ℝ) ^ m * ∑ i, ‖u i‖ ^ 2 := by
  have h1 : ∀ σ : Fin m → Bool, ‖∑ i, (if σ i then (1:ℝ) else -1) • u i‖ ^ 2 =
      ∑ i, ∑ j, (if σ i then (1:ℝ) else -1) * (if σ j then 1 else -1) *
        (inner (𝕜 := ℝ) (u i) (u j) : ℝ) := by
    intro σ
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, aux_krb_sign_sum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [real_inner_self_eq_norm_sq]

lemma aux_krb_norm_le {Hb : Type*} [NormedAddCommGroup Hb] {k : ℕ} (p Λ : ℝ) (hp : 1 ≤ p)
    (W : Fin k → Hb) (hW : GroupNormLp p W ≤ Λ) (y : Fin k) : ‖W y‖ ≤ Λ := by
  unfold GroupNormLp at hW
  have hp0 : 0 < p := by linarith
  have hsingle : ‖W y‖ ^ p ≤ ∑ l, ‖W l‖ ^ p :=
    Finset.single_le_sum (f := fun l => ‖W l‖ ^ p)
      (fun l _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ y)
  have h2 : (‖W y‖ ^ p) ^ (1 / p) ≤ (∑ l, ‖W l‖ ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hsingle (by positivity)
  rw [one_div, Real.rpow_rpow_inv (norm_nonneg _) hp0.ne'] at h2
  rw [one_div] at hW
  linarith

end FoundationsML.MultiClass

open FoundationsML.MultiClass

theorem solution
    {X Hb : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (K : X → X → ℝ) (Φ : X → Hb) (hK : IsPDS K) (hΦ : ∀ x y, K x y = (inner (𝕜 := ℝ) (Φ x) (Φ y) : ℝ))
    (r : ℝ) (hr : 0 < r) (hrK : ∀ x, K x x ≤ r ^ 2)
    (k : ℕ) (hk : 0 < k) (p Λ : ℝ) (hp : 1 ≤ p) (hΛ : 0 < Λ) (m : ℕ) (hm : 0 < m)
    (hInt : Integrable
      (fun S => EmpiricalRademacherComplexity (Proj1 (KernelHypothesisClass Φ k p Λ)) S)
      (Measure.pi fun _ : Fin m => D)) :
    RademacherComplexity D (Proj1 (KernelHypothesisClass Φ k p Λ)) m ≤
      Real.sqrt (r ^ 2 * Λ ^ 2 / m) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hpt : ∀ S : Fin m → X,
      EmpiricalRademacherComplexity (Proj1 (KernelHypothesisClass Φ k p Λ)) S ≤
        Real.sqrt (r ^ 2 * Λ ^ 2 / m) := by
    intro S
    set v : (Fin m → Bool) → Hb :=
      fun σ => ∑ i, (if σ i then (1:ℝ) else -1) • Φ (S i) with hv
    -- Step 1: bound each supremum
    have hsup : ∀ σ : Fin m → Bool,
        (⨆ g ∈ Proj1 (KernelHypothesisClass Φ k p Λ),
          (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * g (S i)) ≤
          Λ / m * ‖v σ‖ := by
      intro σ
      have hB : 0 ≤ Λ / m * ‖v σ‖ := by positivity
      refine Real.iSup_le (fun g => Real.iSup_le (fun hg => ?_) hB) hB
      obtain ⟨h, ⟨W, hW, rfl⟩, y, rfl⟩ := hg
      have hsum : ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) *
          (inner (𝕜 := ℝ) (W y) (Φ (S i)) : ℝ) = (inner (𝕜 := ℝ) (W y) (v σ) : ℝ) := by
        rw [hv, inner_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_smul_right]
      have hWy := aux_krb_norm_le p Λ hp W hW y
      have hin : (inner (𝕜 := ℝ) (W y) (v σ) : ℝ) ≤ Λ * ‖v σ‖ :=
        (real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right hWy (norm_nonneg _))
      simp only
      rw [hsum]
      calc 1 / (m:ℝ) * (inner (𝕜 := ℝ) (W y) (v σ) : ℝ) ≤ 1 / (m:ℝ) * (Λ * ‖v σ‖) :=
            mul_le_mul_of_nonneg_left hin (by positivity)
        _ = Λ / m * ‖v σ‖ := by ring
    -- Step 2
    have hstep2 : EmpiricalRademacherComplexity (Proj1 (KernelHypothesisClass Φ k p Λ)) S ≤
        (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool, Λ / m * ‖v σ‖ := by
      unfold EmpiricalRademacherComplexity
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hsup σ) (by positivity)
    refine hstep2.trans ?_
    -- Step 3
    set A := ∑ σ : Fin m → Bool, ‖v σ‖ with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun σ _ => norm_nonneg _
    have hnorm : ∑ i, ‖Φ (S i)‖ ^ 2 ≤ m * r ^ 2 := by
      have : ∀ i, ‖Φ (S i)‖ ^ 2 ≤ r ^ 2 := by
        intro i
        rw [← real_inner_self_eq_norm_sq, ← hΦ]
        exact hrK _
      calc ∑ i, ‖Φ (S i)‖ ^ 2 ≤ ∑ _i : Fin m, r ^ 2 := Finset.sum_le_sum fun i _ => this i
        _ = m * r ^ 2 := by simp
    have hAsq : A ^ 2 ≤ (2:ℝ) ^ m * ((2:ℝ) ^ m * (m * r ^ 2)) := by
      have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m → Bool)))
        (f := fun σ => ‖v σ‖)
      have hcard : ((Finset.univ : Finset (Fin m → Bool)).card : ℝ) = (2:ℝ) ^ m := by
        simp [Fintype.card_fun, Fintype.card_bool]
      rw [hcard] at hcs
      have heq := aux_krb_norm_sq_sum m (fun i => Φ (S i))
      rw [hA]
      refine hcs.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hv]
      rw [heq]
      exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    have hrw : (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool, Λ / m * ‖v σ‖ =
        Λ / (m * (2:ℝ) ^ m) * A := by
      rw [hA, ← Finset.mul_sum]
      field_simp
    rw [hrw]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    have h2m : (0:ℝ) < (2:ℝ) ^ m := by positivity
    rw [mul_pow, div_pow]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hmR]
    calc Λ ^ 2 * A ^ 2 * m ≤ Λ ^ 2 * ((2:ℝ) ^ m * ((2:ℝ) ^ m * (m * r ^ 2))) * m := by
          gcongr
      _ = r ^ 2 * Λ ^ 2 * (m * (2:ℝ) ^ m) ^ 2 := by ring
  unfold RademacherComplexity
  calc ∫ S, EmpiricalRademacherComplexity (Proj1 (KernelHypothesisClass Φ k p Λ)) S
        ∂(Measure.pi fun _ : Fin m => D)
      ≤ ∫ _S, Real.sqrt (r ^ 2 * Λ ^ 2 / m) ∂(Measure.pi fun _ : Fin m => D) :=
        integral_mono hInt (integrable_const _) hpt
    _ = Real.sqrt (r ^ 2 * Λ ^ 2 / m) := by simp
