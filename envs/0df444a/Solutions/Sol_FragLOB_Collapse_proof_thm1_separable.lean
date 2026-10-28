-- Prove2me | solution 1 for FragLOB.Collapse.proof_thm1_separable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:17:00.545968+00:00
-- url     : https://prove2.me/submissions/f59d638a-190f-490c-a738-02344d50111a

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

/-- payoff coefficient vector -/
noncomputable def cvec {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) : Fin (N + 1) → ℝ :=
  Fin.cons (γ * M.r 0) (fun i => γ * M.r i.succ - d i)

lemma payoff_eq {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) (p : Fin (N + 1) → ℝ) :
    payoff M d γ p = ∑ k, p k * cvec M d γ k := by
  rw [Fin.sum_univ_succ]
  simp [payoff, cvec]

lemma cvec_meas {N : ℕ} (M : Market N) (d : Fin N → ℝ) (k : Fin (N + 1)) :
    Measurable fun γ => cvec M d γ k := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp only [cvec, Fin.cons_zero]; fun_prop
  · simp only [cvec, Fin.cons_succ]; fun_prop

lemma cvec_int {N : ℕ} (M : Market N) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hmean : Integrable (fun γ => γ) F) (d : Fin N → ℝ) (k : Fin (N + 1)) :
    Integrable (fun γ => cvec M d γ k) F := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp only [cvec, Fin.cons_zero]; exact hmean.mul_const _
  · simp only [cvec, Fin.cons_succ]; exact (hmean.mul_const _).sub (integrable_const _)

lemma payoff_integrable {N : ℕ} (M : Market N) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iio 0) = 0) (hmean : Integrable (fun γ => γ) F) (d : Fin N → ℝ)
    (pi : ℝ → Fin (N + 1) → ℝ) (hpi : IsRouting pi) :
    Integrable (fun γ => payoff M d γ (pi γ)) F := by
  have hnn : ∀ᵐ γ ∂F, 0 ≤ γ := by
    have := (measure_eq_zero_iff_ae_notMem).1 hF
    filter_upwards [this] with γ hγ
    simpa using hγ
  simp_rw [payoff_eq]
  refine integrable_finsetSum _ (fun k _ => ?_)
  refine (cvec_int M F hmean d k).bdd_mul (c := 1) (hpi.1 k).aestronglyMeasurable ?_
  filter_upwards [hnn] with γ hγ
  obtain ⟨h0, h1⟩ := hpi.2 γ hγ
  have : pi γ k ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ k)
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 k)]
  exact this

/-- the maximal coefficient -/
noncomputable def mx {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (cvec M d γ)

lemma mx_meas {N : ℕ} (M : Market N) (d : Fin N → ℝ) : Measurable (mx M d) := by
  unfold mx
  have : (fun γ => Finset.univ.sup' Finset.univ_nonempty (cvec M d γ)) =
      Finset.univ.sup' Finset.univ_nonempty (fun k => fun γ => cvec M d γ k) := by
    ext γ; simp
  show Measurable (fun γ => Finset.univ.sup' Finset.univ_nonempty (cvec M d γ))
  rw [this]
  exact Finset.measurable_sup' _ (fun k _ => cvec_meas M d k)

lemma le_mx {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) (k : Fin (N + 1)) :
    cvec M d γ k ≤ mx M d γ := Finset.le_sup' (cvec M d γ) (Finset.mem_univ k)

lemma payoff_le_mx {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) (p : Fin (N + 1) → ℝ)
    (hp : IsSimplexPoint p) : payoff M d γ p ≤ mx M d γ := by
  rw [payoff_eq]
  calc ∑ k, p k * cvec M d γ k ≤ ∑ k, p k * mx M d γ :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (le_mx M d γ k) (hp.1 k))
    _ = mx M d γ := by rw [← Finset.sum_mul, hp.2, one_mul]

lemma mx_attained {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) :
    ∃ k, cvec M d γ k = mx M d γ := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (cvec M d γ)
  exact ⟨k, hk.symm⟩

lemma isBR_iff {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) (p : Fin (N + 1) → ℝ) :
    IsBestResponse M d γ p ↔ IsSimplexPoint p ∧ payoff M d γ p = mx M d γ := by
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨hp, le_antisymm (payoff_le_mx M d γ p hp) ?_⟩
    obtain ⟨k, hk⟩ := mx_attained M d γ
    have hq : IsSimplexPoint (fun j => if j = k then (1:ℝ) else 0) := by
      refine ⟨fun j => by dsimp only; split_ifs <;> norm_num, by simp⟩
    have := hb _ hq
    rw [payoff_eq (p := fun j => if j = k then (1:ℝ) else 0)] at this
    simp at this
    rw [← hk]; exact this
  · rintro ⟨hp, he⟩
    refine ⟨hp, fun q hq => ?_⟩
    rw [he]; exact payoff_le_mx M d γ q hq

/-- first maximiser predicate -/
def firstMax {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) (k : Fin (N + 1)) : Prop :=
  cvec M d γ k = mx M d γ ∧ ∀ j : Fin (N + 1), j < k → cvec M d γ j < mx M d γ

lemma firstMax_exists_unique {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) :
    ∃ k, firstMax M d γ k ∧ ∀ k', firstMax M d γ k' → k' = k := by
  classical
  obtain ⟨k1, hk1⟩ := mx_attained M d γ
  have hne : (Finset.univ.filter (fun k => cvec M d γ k = mx M d γ)).Nonempty :=
    ⟨k1, by simp [hk1]⟩
  set k0 := (Finset.univ.filter (fun k => cvec M d γ k = mx M d γ)).min' hne with hk0
  have hmem : cvec M d γ k0 = mx M d γ := by
    have := Finset.min'_mem _ hne
    simpa using this
  refine ⟨k0, ⟨hmem, fun j hj => ?_⟩, fun k' hk' => ?_⟩
  · refine lt_of_le_of_ne (le_mx M d γ j) (fun h => ?_)
    have : k0 ≤ j := Finset.min'_le _ _ (by simp [h])
    exact absurd hj (not_lt.2 this)
  · have h2 : k0 ≤ k' := Finset.min'_le _ _ (by simp [hk'.1])
    by_contra hne'
    have hlt : k0 < k' := lt_of_le_of_ne h2 (fun h => hne' h.symm)
    exact absurd hmem (ne_of_lt (hk'.2 _ hlt))

/-- first-maximiser routing -/
noncomputable def pstar {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) : Fin (N + 1) → ℝ :=
  fun k => by classical exact if firstMax M d γ k then 1 else 0

lemma firstMax_meas {N : ℕ} (M : Market N) (d : Fin N → ℝ) (k : Fin (N + 1)) :
    MeasurableSet {γ | firstMax M d γ k} := by
  have : {γ | firstMax M d γ k} = {γ | cvec M d γ k = mx M d γ} ∩
      ⋂ j ∈ {j : Fin (N + 1) | j < k}, {γ | cvec M d γ j < mx M d γ} := by
    ext γ; simp [firstMax]
  rw [this]
  refine MeasurableSet.inter (measurableSet_eq_fun (cvec_meas M d k) (mx_meas M d)) ?_
  exact MeasurableSet.biInter (Set.to_countable _)
    (fun j _ => measurableSet_lt (cvec_meas M d j) (mx_meas M d))

lemma pstar_routing {N : ℕ} (M : Market N) (d : Fin N → ℝ) : IsRouting (pstar M d) := by
  classical
  refine ⟨fun k => ?_, fun γ _ => ?_⟩
  · unfold pstar
    exact Measurable.ite (firstMax_meas M d k) measurable_const measurable_const
  · obtain ⟨k0, hk0, hu⟩ := firstMax_exists_unique M d γ
    refine ⟨fun k => ?_, ?_⟩
    · unfold pstar; split_ifs <;> norm_num
    · unfold pstar
      rw [Finset.sum_eq_single k0]
      · simp [hk0]
      · intro b _ hb
        have : ¬ firstMax M d γ b := fun h => hb (hu b h)
        simp [this]
      · simp

lemma pstar_payoff {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) :
    payoff M d γ (pstar M d γ) = mx M d γ := by
  classical
  obtain ⟨k0, hk0, hu⟩ := firstMax_exists_unique M d γ
  rw [payoff_eq]
  unfold pstar
  rw [Finset.sum_eq_single k0]
  · simp [hk0, hk0.1]
  · intro b _ hb
    have : ¬ firstMax M d γ b := fun h => hb (hu b h)
    simp [this]
  · simp

theorem sep {N : ℕ} (M : Market N) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iio 0) = 0) (hmean : Integrable (fun γ => γ) F) (d : Fin N → ℝ)
    (pi : ℝ → Fin (N + 1) → ℝ) (hpi : IsRouting pi) :
    (∀ pi' : ℝ → Fin (N + 1) → ℝ, IsRouting pi' →
        ∫ γ, payoff M d γ (pi' γ) ∂F ≤ ∫ γ, payoff M d γ (pi γ) ∂F) ↔
      ∀ᵐ γ ∂F, IsBestResponse M d γ (pi γ) := by
  have hnn : ∀ᵐ γ ∂F, 0 ≤ γ := by
    have := (measure_eq_zero_iff_ae_notMem).1 hF
    filter_upwards [this] with γ hγ
    simpa using hγ
  have hint := payoff_integrable M F hF hmean d pi hpi
  constructor
  · intro H
    have hps := pstar_routing M d
    have h1 := H _ hps
    have hint' := payoff_integrable M F hF hmean d _ hps
    have hle : (fun γ => payoff M d γ (pi γ)) ≤ᵐ[F] (fun γ => payoff M d γ (pstar M d γ)) := by
      filter_upwards [hnn] with γ hγ
      rw [pstar_payoff]
      exact payoff_le_mx M d γ _ (hpi.2 γ hγ)
    have heq := (integral_eq_iff_of_ae_le hint hint' hle).1 (le_antisymm
      (integral_mono_ae hint hint' hle) h1)
    filter_upwards [hnn, heq] with γ hγ he
    rw [isBR_iff]
    refine ⟨hpi.2 γ hγ, ?_⟩
    rw [he, pstar_payoff]
  · intro H pi' hpi'
    have hint' := payoff_integrable M F hF hmean d pi' hpi'
    refine integral_mono_ae hint' hint ?_
    filter_upwards [hnn, H] with γ hγ hb
    exact hb.2 _ (hpi'.2 γ hγ)

end FragLOB.Collapse

open MeasureTheory FragLOB.Collapse

theorem solution {N : ℕ} (M : Market N) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iio 0) = 0) (hmean : Integrable (fun γ => γ) F) (d : Fin N → ℝ)
    (pi : ℝ → Fin (N + 1) → ℝ) (hpi : IsRouting pi) :
    (∀ pi' : ℝ → Fin (N + 1) → ℝ, IsRouting pi' →
        ∫ γ, payoff M d γ (pi' γ) ∂F ≤ ∫ γ, payoff M d γ (pi γ) ∂F) ↔
      ∀ᵐ γ ∂F, IsBestResponse M d γ (pi γ) :=
  sep M F hF hmean d pi hpi
