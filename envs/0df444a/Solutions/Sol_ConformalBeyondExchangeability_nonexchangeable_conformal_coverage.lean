-- Prove2me | solution 1 for ConformalBeyondExchangeability.nonexchangeable_conformal_coverage
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T09:21:21.301249+00:00
-- url     : https://prove2.me/submissions/01f81d5f-2036-4e09-9487-ed98f4d669bb

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

lemma ne_wq_swap {m : ℕ} (a b : Fin m) (p : Fin m → ℝ) (v : Fin m → EReal) (τ : ℝ) :
    wQuantile p (fun i => v (Equiv.swap a b i)) τ =
      wQuantile (fun i => p (Equiv.swap a b i)) v τ := by
  unfold wQuantile
  congr 1
  ext q
  simp only [Set.mem_setOf_eq]
  rw [← Equiv.sum_comp (Equiv.swap a b) (fun i => if v i ≤ q then p (Equiv.swap a b i) else 0)]
  simp only [Equiv.swap_apply_self]

lemma ne_top_iff {n : ℕ} (p : Fin (n + 1) → ℝ) (r : Fin (n + 1) → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    ((r (Fin.last n) : EReal) ≤
        wQuantile p (fun i => if i = Fin.last n then ⊤ else (r i : EReal)) τ) ↔
      ((r (Fin.last n) : EReal) ≤ wQuantile p (fun i => (r i : EReal)) τ) := by
  rw [fc_le_wQuantile_iff (v := fun i => if i = Fin.last n then (⊤ : EReal)
      else (r i : EReal)) _ _ hτ
      (fun i => by by_cases hi : i = Fin.last n <;> simp [hi]),
    fc_le_wQuantile_iff (v := fun i => (r i : EReal)) _ _ hτ (fun i => EReal.coe_ne_bot _)]
  refine forall_congr' fun q => imp_congr_right fun hq => ?_
  have : ∀ i, (if (if i = Fin.last n then (⊤ : EReal) else (r i : EReal)) ≤
      (q : EReal) then p i else 0) = (if (r i : EReal) ≤ (q : EReal) then p i else 0) := by
    intro i
    by_cases hi : i = Fin.last n
    · subst hi
      simp only [if_true]
      rw [if_neg (by simp), if_neg (not_le.mpr hq)]
    · simp only [hi, if_false]
  simp only [this]

lemma ne_weights {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    (∀ i, 0 ≤ normWeights w i) ∧ (∑ i, normWeights w i = 1) ∧
      (∀ i, normWeights w i ≤ normWeights w (Fin.last n)) := by
  have hD : 0 < ∑ j, w j + 1 := by
    have : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => (hw j).1
    linarith
  refine ⟨fun i => ?_, ?_, fun i => ?_⟩
  · simp only [normWeights]
    apply div_nonneg _ hD.le
    split_ifs
    · exact (hw _).1
    · exact zero_le_one
  · rw [Fin.sum_univ_castSucc]
    simp only [normWeights, Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl,
      dif_neg, not_false_eq_true]
    rw [← Finset.sum_div, ← add_div, div_self hD.ne']
  · simp only [normWeights, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true]
    apply div_le_div_of_nonneg_right _ hD.le
    split_ifs
    · exact (hw _).2
    · exact le_rfl

lemma ne_det {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → ℝ) :
    1 - α ≤ ∑ k, normWeights w k *
      {r' : Fin (n + 1) → ℝ | ((r' k : ℝ) : EReal) ≤
        wQuantile (fun i => normWeights w (swapIdx k i)) (fun i => (r' i : EReal)) (1 - α)}.indicator
        (fun _ => (1 : ℝ)) r := by
  classical
  obtain ⟨hp0, hp1, hplast⟩ := ne_weights w hw
  set p := normWeights w with hpdef
  have hτ : (0 : ℝ) < 1 - α := by linarith
  have hsw := fc_strange_weight_le w hw hα0 hα1 r
  rw [← hpdef] at hsw
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => i ∈ strangeSet p α r) p
  rw [hp1, Finset.filter_mem_eq_inter, Finset.univ_inter] at hsplit
  have hkey : ∀ k, k ∉ strangeSet p α r →
      ((r k : ℝ) : EReal) ≤ wQuantile (fun i => p (swapIdx k i)) (fun i => (r i : EReal)) (1 - α) := by
    intro k hk
    simp only [strangeSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
    rw [fc_le_wQuantile_iff _ _ _ hτ (fun i => EReal.coe_ne_bot _)] at hk ⊢
    intro q hq
    refine lt_of_le_of_lt ?_ (hk q hq)
    simp only [EReal.coe_le_coe_iff]
    have hqk : ¬ r k ≤ q := not_le.mpr (EReal.coe_lt_coe_iff.mp hq)
    by_cases hkl : k = Fin.last n
    · subst hkl
      simp [swapIdx]
    · rw [← sub_nonneg]
      rw [← Equiv.sum_comp (swapIdx k) (fun i => if r i ≤ q then p (swapIdx k i) else 0)]
      simp only [swapIdx, Equiv.swap_apply_self]
      rw [← Finset.sum_sub_distrib]
      rw [Fintype.sum_eq_add k (Fin.last n) hkl]
      · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, if_neg hqk]
        have := hplast k
        split_ifs <;> linarith
      · intro x ⟨hx1, hx2⟩
        rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2, sub_self]
  have hrhs : ∑ i ∈ Finset.univ.filter (fun i => i ∉ strangeSet p α r), p i ≤
      ∑ k, p k * {r' : Fin (n + 1) → ℝ | ((r' k : ℝ) : EReal) ≤
        wQuantile (fun i => p (swapIdx k i)) (fun i => (r' i : EReal)) (1 - α)}.indicator
        (fun _ => (1 : ℝ)) r := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases h : k ∈ strangeSet p α r
    · simp only [h, not_true_eq_false, if_false]
      exact mul_nonneg (hp0 k) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · simp only [h, not_false_eq_true, if_true]
      rw [Set.indicator_of_mem (show r ∈ _ from hkey k h), mul_one]
  linarith

lemma ne_tv {E : Type*} [MeasurableSpace E] {n : ℕ} (P : Measure (Fin (n + 1) → E))
    [IsProbabilityMeasure P] (R : (Fin (n + 1) → E) → Fin (n + 1) → ℝ) (hR : Measurable R)
    (k : Fin (n + 1)) (B : Set (Fin (n + 1) → ℝ)) (hB : MeasurableSet B) :
    P.real (R ⁻¹' B) ≤ P.real ((fun z => R (swapData k z)) ⁻¹' B) +
      tvDist (P.map R) (P.map fun z => R (swapData k z)) := by
  have hs : Measurable fun z : Fin (n + 1) → E => swapData k z :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hRk : Measurable fun z => R (swapData k z) := hR.comp hs
  haveI : IsProbabilityMeasure (P.map R) := Measure.isProbabilityMeasure_map hR.aemeasurable
  haveI : IsProbabilityMeasure (P.map fun z => R (swapData k z)) :=
    Measure.isProbabilityMeasure_map hRk.aemeasurable
  have h1 : (P.map R).real B = P.real (R ⁻¹' B) := by
    simp only [Measure.real, Measure.map_apply hR hB]
  have h2 : (P.map fun z => R (swapData k z)).real B = P.real ((fun z => R (swapData k z)) ⁻¹' B) := by
    simp only [Measure.real, Measure.map_apply hRk hB]
  have hbdd : BddAbove {r | ∃ A : Set (Fin (n + 1) → ℝ), MeasurableSet A ∧
      r = |(P.map R).real A - (P.map fun z => R (swapData k z)).real A|} := by
    refine ⟨1, ?_⟩
    rintro _ ⟨A, _, rfl⟩
    rw [abs_le]
    have a1 := measureReal_le_one (μ := P.map R) (s := A)
    have a2 := measureReal_le_one (μ := P.map fun z => R (swapData k z)) (s := A)
    have b1 := measureReal_nonneg (μ := P.map R) (s := A)
    have b2 := measureReal_nonneg (μ := P.map fun z => R (swapData k z)) (s := A)
    constructor <;> linarith
  have h3 := le_csSup hbdd ⟨B, hB, rfl⟩
  unfold tvDist
  rw [h1, h2] at h3
  have := le_abs_self (P.real (R ⁻¹' B) - P.real ((fun z => R (swapData k z)) ⁻¹' B))
  linarith

lemma ne_main {X : Type*} [MeasurableSpace X] {n : ℕ} (P : Measure (Fin (n + 1) → X × ℝ))
    [IsProbabilityMeasure P] (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (R : (Fin (n + 1) → X × ℝ) → Fin (n + 1) → ℝ) (hR : Measurable R) :
    1 - α - swapGap P w R ≤ ∑ k, normWeights w k *
      P.real {z | ((R (swapData k z) k : ℝ) : EReal) ≤
        wQuantile (fun i => normWeights w (swapIdx k i)) (fun i => (R (swapData k z) i : EReal))
          (1 - α)} := by
  classical
  obtain ⟨hp0, hp1, hplast⟩ := ne_weights w hw
  set p := normWeights w with hpdef
  have hτ : (0 : ℝ) < 1 - α := by linarith
  let G : Fin (n + 1) → Set (Fin (n + 1) → ℝ) := fun k =>
    {r' | ((r' k : ℝ) : EReal) ≤
        wQuantile (fun i => p (swapIdx k i)) (fun i => (r' i : EReal)) (1 - α)}
  have hG : ∀ k, MeasurableSet (G k) := fun k =>
    fc_meas_set (fun i => p (swapIdx k i)) (fun i => hp0 _) (1 - α) hτ k
  have hint : ∀ k, Integrable (fun z => p k * (G k).indicator (fun _ => (1 : ℝ)) (R z)) P :=
    fun k => (((integrable_const (1 : ℝ)).indicator (hG k)).comp_measurable hR).const_mul (p k)
  have hA : 1 - α ≤ ∑ k, p k * P.real (R ⁻¹' G k) := by
    calc 1 - α = ∫ _z, (1 - α) ∂P := by simp
      _ ≤ ∫ z, ∑ k, p k * (G k).indicator (fun _ => (1 : ℝ)) (R z) ∂P :=
          integral_mono (integrable_const _) (integrable_finset_sum _ fun k _ => hint k)
            (fun z => ne_det w hw hα0 hα1 (R z))
      _ = ∑ k, p k * P.real (R ⁻¹' G k) := by
          rw [integral_finset_sum _ fun k _ => hint k]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_const_mul]
          congr 1
          rw [show (fun z => (G k).indicator (fun _ => (1 : ℝ)) (R z)) =
            (R ⁻¹' G k).indicator (fun _ => (1 : ℝ)) from rfl]
          exact integral_indicator_one (hR (hG k))
  have hlast : ∀ z : Fin (n + 1) → X × ℝ, swapData (Fin.last n) z = z := by
    intro z; funext i; simp [swapData, swapIdx]
  have hB : ∑ k, p k * P.real (R ⁻¹' G k) ≤
      ∑ k, p k * P.real ((fun z => R (swapData k z)) ⁻¹' G k) + swapGap P w R := by
    unfold swapGap
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hlast]
    have : ∑ i : Fin n, p i.castSucc * P.real (R ⁻¹' G i.castSucc) ≤
        ∑ i : Fin n, p i.castSucc * P.real ((fun z => R (swapData i.castSucc z)) ⁻¹' G i.castSucc) +
        ∑ i : Fin n, p i.castSucc *
          tvDist (P.map R) (P.map fun z => R (swapData i.castSucc z)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (ne_tv P R hR _ _ (hG _)) (hp0 _)
    have e : (fun z => R z) ⁻¹' G (Fin.last n) = R ⁻¹' G (Fin.last n) := rfl
    rw [e]
    linarith
  have hC : ∑ k, p k * P.real ((fun z => R (swapData k z)) ⁻¹' G k) =
      ∑ k, p k * P.real {z | ((R (swapData k z) k : ℝ) : EReal) ≤
        wQuantile (fun i => p (swapIdx k i)) (fun i => (R (swapData k z) i : EReal))
          (1 - α)} := rfl
  linarith

theorem nonexchangeable_conformal_coverage {X T : Type*} [MeasurableSpace X] {n : ℕ}
    (P : Measure (Fin (n + 1) → X × ℝ)) [IsProbabilityMeasure P]
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ (alg : TaggedAlg X T) (t : Fin (n + 1) → T), Measurable (residuals alg t) →
      1 - α - swapGap P w (residuals alg t) ≤ fullCoverage P alg t w α) ∧
    (∀ μ : X → ℝ, Measurable μ →
      1 - α - swapGap P w (splitResiduals μ) ≤ splitCoverage P μ w α) := by
  obtain ⟨hp0, hp1, hplast⟩ := ne_weights w hw
  have hτ : (0 : ℝ) < 1 - α := by linarith
  constructor
  · intro alg t hR
    refine le_of_le_of_eq (ne_main P w hw hα0 hα1 _ hR) ?_
    unfold fullCoverage randIndexProb
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    ext z
    simp only [Set.mem_setOf_eq, fullSet]
    have hwt : withTest z (z (Fin.last n)).2 = z := by simp [withTest]
    have hsr : ∀ i, swapResiduals alg t z (z (Fin.last n)).2 k i =
        residuals alg t (swapData k z) (swapIdx k i) := by
      intro i
      simp only [swapResiduals, hwt, residuals, swapData, swapIdx, Equiv.swap_apply_self]
    simp only [hsr]
    rw [show (swapIdx k) (Fin.last n) = k from Equiv.swap_apply_right _ _]
    simp only [swapIdx]
    rw [← ne_wq_swap]
  · intro μ hμ
    have hR : Measurable (splitResiduals (n := n) μ) :=
      measurable_pi_lambda _ fun i => continuous_abs.measurable.comp
        ((measurable_snd.comp (measurable_pi_apply i)).sub
          (hμ.comp (measurable_fst.comp (measurable_pi_apply i))))
    refine le_of_le_of_eq (ne_main P w hw hα0 hα1 _ hR) ?_
    unfold splitCoverage
    rw [show P.real {z | (z (Fin.last n)).2 ∈ splitSet μ w α z} =
      ∑ k, normWeights w k * P.real {z | (z (Fin.last n)).2 ∈ splitSet μ w α z} by
        rw [← Finset.sum_mul, hp1, one_mul]]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    ext z
    simp only [Set.mem_setOf_eq, splitSet]
    have hr : |(z (Fin.last n)).2 - μ (z (Fin.last n)).1| = splitResiduals μ z (Fin.last n) := rfl
    rw [hr, ne_top_iff _ _ _ hτ]
    have hsw : ∀ i, splitResiduals μ z i = splitResiduals μ (swapData k z) (swapIdx k i) := by
      intro i
      simp only [splitResiduals, swapData, swapIdx, Equiv.swap_apply_self]
    simp only [hsw]
    rw [show (swapIdx k) (Fin.last n) = k from Equiv.swap_apply_right _ _]
    simp only [swapIdx]
    rw [← ne_wq_swap]

end ConformalBeyondExchangeability

open ConformalBeyondExchangeability in
theorem solution {X T : Type*} [MeasurableSpace X] {n : ℕ}
    (P : Measure (Fin (n + 1) → X × ℝ)) [IsProbabilityMeasure P]
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ (alg : TaggedAlg X T) (t : Fin (n + 1) → T), Measurable (residuals alg t) →
      1 - α - swapGap P w (residuals alg t) ≤ fullCoverage P alg t w α) ∧
    (∀ μ : X → ℝ, Measurable μ →
      1 - α - swapGap P w (splitResiduals μ) ≤ splitCoverage P μ w α) :=
  ConformalBeyondExchangeability.nonexchangeable_conformal_coverage P w hw hα0 hα1
