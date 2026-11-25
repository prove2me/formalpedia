-- Prove2me | solution 1 for ConformalBeyondExchangeability.full_conformal_coverage_exchangeable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T09:16:14.016812+00:00
-- url     : https://prove2.me/submissions/6f147d42-6c06-487a-8313-b871179e951b

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory
set_option autoImplicit false
namespace ConformalBeyondExchangeability

theorem fc_strange_weight_le {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → ℝ) :
    ∑ i ∈ strangeSet (normWeights w) α r, normWeights w i ≤ α := by
  classical
  set p := normWeights w with hpdef
  have hD : 0 < ∑ j, w j + 1 := by
    have : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => (hw j).1
    linarith
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    simp only [hpdef, normWeights]
    apply div_nonneg _ hD.le
    split_ifs
    · exact (hw _).1
    · exact zero_le_one
  have hp1 : ∑ i, p i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hpdef, normWeights, Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl,
      dif_neg, not_false_eq_true]
    rw [← Finset.sum_div, ← add_div, div_self hD.ne']
  set S := strangeSet p α r with hS
  by_contra hcon
  push_neg at hcon
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hcon
    linarith
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image S r hne
  have hmemS : ∀ i, i ∈ S ↔ wQuantile p (fun j => (r j : EReal)) (1 - α) < (r i : EReal) := by
    intro i
    simp [hS, strangeSet]
  have hQ : (r i0 : EReal) ≤ wQuantile p (fun j => (r j : EReal)) (1 - α) := by
    unfold wQuantile
    refine le_sInf fun q hq => ?_
    simp only [Set.mem_setOf_eq] at hq
    by_contra hlt
    push_neg at hlt
    have hzero : ∑ i ∈ S, (if (r i : EReal) ≤ q then p i else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : (r i0 : EReal) ≤ r i := EReal.coe_le_coe_iff.mpr (hmin i hi)
      rw [if_neg]
      intro hle
      exact absurd (lt_of_le_of_lt (le_trans this hle) hlt) (lt_irrefl _)
    have hcomp : ∑ i ∈ Sᶜ, (if (r i : EReal) ≤ q then p i else 0) ≤ ∑ i ∈ Sᶜ, p i := by
      refine Finset.sum_le_sum fun i _ => ?_
      split_ifs
      · exact le_refl _
      · exact hp i
    have htot : ∑ i ∈ S, p i + ∑ i ∈ Sᶜ, p i = 1 := by rw [Finset.sum_add_sum_compl, hp1]
    rw [← Finset.sum_add_sum_compl S, hzero, zero_add] at hq
    linarith
  have := (hmemS i0).mp hi0
  exact absurd (lt_of_le_of_lt hQ this) (lt_irrefl _)



lemma fc_le_wQuantile_iff {m : ℕ} (p : Fin m → ℝ) (v : Fin m → EReal) (τ : ℝ) (hτ : 0 < τ)
    (hv : ∀ i, v i ≠ ⊥) (x : ℝ) :
    ((x : EReal) ≤ wQuantile p v τ) ↔
      ∀ q : ℝ, (q : EReal) < x → (∑ i, if v i ≤ (q : EReal) then p i else 0) < τ := by
  unfold wQuantile
  rw [le_sInf_iff]
  constructor
  · intro h q hq
    by_contra hc
    push_neg at hc
    exact absurd (h q hc) (not_le.mpr hq)
  · intro h b hb
    simp only [Set.mem_setOf_eq] at hb
    induction b using EReal.rec with
    | bot =>
      exfalso
      have h0 : (∑ i, if v i ≤ (⊥ : EReal) then p i else 0) = 0 :=
        Finset.sum_eq_zero fun i _ => by simp [hv i]
      linarith
    | top => exact le_top
    | coe q =>
      by_contra hc
      push_neg at hc
      exact absurd hb (not_le.mpr (h q hc))

lemma fc_meas_set {m : ℕ} (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) (τ : ℝ) (hτ : 0 < τ) (i : Fin m) :
    MeasurableSet {r : Fin m → ℝ | ((r i : ℝ) : EReal) ≤ wQuantile p (fun j => (r j : EReal)) τ} := by
  have heq : {r : Fin m → ℝ | ((r i : ℝ) : EReal) ≤ wQuantile p (fun j => (r j : EReal)) τ} =
      ⋂ q : ℚ, {r : Fin m → ℝ | (q : ℝ) < r i → (∑ j, if r j ≤ (q : ℝ) then p j else 0) < τ} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [fc_le_wQuantile_iff p _ τ hτ (fun j => EReal.coe_ne_bot _)]
    simp only [EReal.coe_le_coe_iff, EReal.coe_lt_coe_iff]
    constructor
    · intro h q hq; exact h q hq
    · intro h q hq
      obtain ⟨q', hq1, hq2⟩ := exists_rat_btwn hq
      refine lt_of_le_of_lt ?_ (h q' hq2)
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (h1.trans hq1.le) h2
      · exact hp j
      · exact le_rfl
  rw [heq]
  refine MeasurableSet.iInter fun q => ?_
  have hS : Measurable fun r : Fin m → ℝ => ∑ j, if r j ≤ (q : ℝ) then p j else 0 :=
    Finset.measurable_sum _ fun j _ =>
      Measurable.ite (measurableSet_le (measurable_pi_apply j) measurable_const)
        measurable_const measurable_const
  exact (measurableSet_lt measurable_const (measurable_pi_apply i)).imp
    (measurableSet_lt hS measurable_const)

lemma fc_cov {E : Type*} [MeasurableSpace E] {n : ℕ} (P : Measure (Fin (n + 1) → E))
    [IsProbabilityMeasure P] (hP : IsExchangeable P)
    (R : (Fin (n + 1) → E) → Fin (n + 1) → ℝ) (hR : Measurable R)
    (hRσ : ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ z i, R (fun j => z (σ j)) i = R z (σ i))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α ≤ P.real {z | ((R z (Fin.last n) : ℝ) : EReal) ≤
      wQuantile (normWeights (fun _ : Fin n => (1 : ℝ))) (fun j => (R z j : EReal)) (1 - α)} := by
  classical
  set p := normWeights (fun _ : Fin n => (1 : ℝ)) with hpdef
  have hpv : ∀ i, p i = ((n : ℝ) + 1)⁻¹ := by
    intro i
    simp only [hpdef, normWeights]
    split_ifs <;> simp [div_eq_inv_mul]
  have hp0 : ∀ i, 0 ≤ p i := fun i => by rw [hpv]; positivity
  have hpsum : ∑ i, p i = 1 := by
    simp only [hpv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hτ : (0 : ℝ) < 1 - α := by linarith
  let Q : (Fin (n + 1) → E) → EReal := fun z => wQuantile p (fun j => (R z j : EReal)) (1 - α)
  let Ev : Fin (n + 1) → Set (Fin (n + 1) → E) := fun i => {z | ((R z i : ℝ) : EReal) ≤ Q z}
  have hE : ∀ i, MeasurableSet (Ev i) := fun i => (fc_meas_set p hp0 (1 - α) hτ i).preimage hR
  have hQσ : ∀ (σ : Equiv.Perm (Fin (n + 1))) z, Q (fun j => z (σ j)) = Q z := by
    intro σ z
    simp only [Q, wQuantile, hRσ, hpv]
    congr 1
    ext q
    simp only [Set.mem_setOf_eq]
    rw [Equiv.sum_comp σ (fun j => if (R z j : EReal) ≤ q then ((n : ℝ) + 1)⁻¹ else 0)]
  have hEq : ∀ i, P (Ev i) = P (Ev (Fin.last n)) := by
    intro i
    let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i (Fin.last n)
    have hf : Measurable fun (z : Fin (n + 1) → E) (j : Fin (n + 1)) => z (σ j) :=
      measurable_pi_lambda _ fun j => measurable_pi_apply (σ j)
    have hpre : (fun (z : Fin (n + 1) → E) (j : Fin (n + 1)) => z (σ j)) ⁻¹' Ev (Fin.last n) =
        Ev i := by
      ext z
      simp only [Set.mem_preimage, Ev, Set.mem_setOf_eq, hQσ σ z, hRσ σ z]
      simp [σ]
    rw [← hpre, ← Measure.map_apply hf (hE _), hP σ]
  have hdet : ∀ z, 1 - α ≤ ∑ i, p i * (Ev i).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have hsw := fc_strange_weight_le (fun _ : Fin n => (1 : ℝ)) (fun _ => ⟨zero_le_one, le_rfl⟩)
      hα0 hα1 (R z)
    rw [← hpdef] at hsw
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => i ∈ strangeSet p α (R z)) p
    rw [hpsum, Finset.filter_mem_eq_inter, Finset.univ_inter] at hsplit
    have hrhs : ∑ i, p i * (Ev i).indicator (fun _ => (1 : ℝ)) z =
        ∑ i ∈ Finset.univ.filter (fun i => i ∉ strangeSet p α (R z)), p i := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : z ∈ Ev i
      · have : i ∉ strangeSet p α (R z) := by
          simp only [strangeSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
          exact h
        simp [h, this]
      · have : i ∈ strangeSet p α (R z) := by
          simp only [strangeSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact not_le.mp h
        simp [h, this]
    rw [hrhs]
    linarith
  have hint : ∀ i, Integrable (fun z => p i * (Ev i).indicator (fun _ => (1 : ℝ)) z) P :=
    fun i => ((integrable_const (1 : ℝ)).indicator (hE i)).const_mul (p i)
  calc 1 - α = ∫ _z, (1 - α) ∂P := by simp
    _ ≤ ∫ z, ∑ i, p i * (Ev i).indicator (fun _ => (1 : ℝ)) z ∂P :=
        integral_mono (integrable_const _) (integrable_finset_sum _ fun i _ => hint i) hdet
    _ = ∑ i, p i * P.real (Ev i) := by
        rw [integral_finset_sum _ fun i _ => hint i]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul]
        congr 1
        exact integral_indicator_one (hE i)
    _ = P.real (Ev (Fin.last n)) := by
        simp only [Measure.real, hEq, ← Finset.sum_mul, hpsum, one_mul]

theorem full_conformal_coverage_exchangeable {X : Type*} [MeasurableSpace X] {n : ℕ}
    (P : Measure (Fin (n + 1) → X × ℝ)) [IsProbabilityMeasure P] (hP : IsExchangeable P)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ alg : Alg X, IsSymmetric alg → Measurable (symResiduals (n := n) alg) →
      1 - α ≤ P.real {z | (z (Fin.last n)).2 ∈ symFullSet alg (fun _ => 1) α z}) ∧
    (∀ μ : X → ℝ, Measurable μ → 1 - α ≤ splitCoverage P μ (fun _ => 1) α) := by
  constructor
  · intro alg halg hmeas
    have hRσ : ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ z i,
        symResiduals alg (fun j => z (σ j)) i = symResiduals alg z (σ i) := by
      intro σ z i
      simp only [symResiduals]
      rw [show alg (List.ofFn fun j => z (σ j)) = alg (List.ofFn z) from
        halg _ _ (Equiv.Perm.ofFn_comp_perm σ z)]
    have h := fc_cov P hP (symResiduals alg) hmeas hRσ hα0 hα1
    refine le_of_le_of_eq h ?_
    congr 1
    ext z
    simp only [symFullSet, Set.mem_setOf_eq]
    have hw : withTest z (z (Fin.last n)).2 = z := by
      simp [withTest]
    rw [hw]
  · intro μ hμ
    have hmeas : Measurable (splitResiduals (n := n) μ) :=
      measurable_pi_lambda _ fun i => continuous_abs.measurable.comp
        ((measurable_snd.comp (measurable_pi_apply i)).sub
          (hμ.comp (measurable_fst.comp (measurable_pi_apply i))))
    have h := fc_cov P hP (splitResiduals μ) hmeas (fun σ z i => rfl) hα0 hα1
    unfold splitCoverage
    refine le_of_le_of_eq h ?_
    congr 1
    ext z
    simp only [splitSet, Set.mem_setOf_eq]
    have hτ : (0 : ℝ) < 1 - α := by linarith
    have hr : |(z (Fin.last n)).2 - μ (z (Fin.last n)).1| = splitResiduals μ z (Fin.last n) := rfl
    rw [hr, fc_le_wQuantile_iff (v := fun i => if i = Fin.last n then (⊤ : EReal)
        else (splitResiduals μ z i : EReal)) _ _ hτ
        (fun i => by by_cases hi : i = Fin.last n <;> simp [hi]),
      fc_le_wQuantile_iff (v := fun i => (splitResiduals μ z i : EReal)) _ _ hτ
        (fun i => EReal.coe_ne_bot _)]
    refine forall_congr' fun q => imp_congr_right fun hq => ?_
    have : ∀ i, (if (if i = Fin.last n then (⊤ : EReal) else (splitResiduals μ z i : EReal)) ≤
        (q : EReal) then normWeights (fun _ : Fin n => (1 : ℝ)) i else 0) =
        (if (splitResiduals μ z i : EReal) ≤ (q : EReal) then
          normWeights (fun _ : Fin n => (1 : ℝ)) i else 0) := by
      intro i
      by_cases hi : i = Fin.last n
      · subst hi
        simp only [if_true]
        rw [if_neg (by simp), if_neg (not_le.mpr hq)]
      · simp only [hi, if_false]
    simp only [this]

end ConformalBeyondExchangeability

open ConformalBeyondExchangeability in
theorem solution {X : Type*} [MeasurableSpace X] {n : ℕ}
    (P : Measure (Fin (n + 1) → X × ℝ)) [IsProbabilityMeasure P] (hP : IsExchangeable P)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ alg : Alg X, IsSymmetric alg → Measurable (symResiduals (n := n) alg) →
      1 - α ≤ P.real {z | (z (Fin.last n)).2 ∈ symFullSet alg (fun _ => 1) α z}) ∧
    (∀ μ : X → ℝ, Measurable μ → 1 - α ≤ splitCoverage P μ (fun _ => 1) α) :=
  ConformalBeyondExchangeability.full_conformal_coverage_exchangeable P hP hα0 hα1
