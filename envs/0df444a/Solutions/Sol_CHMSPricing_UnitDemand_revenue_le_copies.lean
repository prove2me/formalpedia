-- Prove2me | solution 1 for CHMSPricing.UnitDemand.revenue_le_copies
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:12:45.020629+00:00
-- url     : https://prove2.me/submissions/e39cf825-2b53-4682-a1d3-9f1d5e3fb65f

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism



namespace CHMSPricing.UnitDemand

theorem twm_core {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (A : MultiMechanism J m)
    (hA : IsTruthfulMulti D 𝒥 owner A) :
    WeaklyMonotone D owner A := by
  intro i v₁ h₁ v₂ h₂ hag
  have a := hA.dsic v₁ h₁ i v₂ h₂ (fun j hj => (hag j hj).symm)
  have b := hA.dsic v₂ h₂ i v₁ h₁ (fun j hj => hag j hj)
  unfold MultiMechanism.utility at a b
  linarith

theorem cam_core {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (A : MultiMechanism J m) (hA : IsTruthfulMulti D 𝒥 owner A)
    (v : J → ℝ) (hv : v ∈ typeSpace D) (j : J) (x y : ℝ)
    (hx : x ∈ Set.Icc (D j).lo (D j).hi) (hy : y ∈ Set.Icc (D j).lo (D j).hi) (hxy : x ≤ y)
    (hj : j ∈ A.alloc (Function.update v j x)) :
    j ∈ A.alloc (Function.update v j y) := by
  by_contra hn
  set i := owner j
  have mem : ∀ z ∈ Set.Icc (D j).lo (D j).hi, Function.update v j z ∈ typeSpace D := by
    intro z hz k _
    by_cases hk : k = j
    · subst hk; simpa using hz
    · simpa [Function.update_of_ne hk] using hv k (Set.mem_univ _)
  have h1 := mem x hx
  have h2 := mem y hy
  have W := twm_core D 𝒥 owner A hA i _ h1 _ h2 (by
    intro k hk
    have : k ≠ j := fun h => hk (h ▸ rfl)
    simp [Function.update_of_ne this])
  unfold MultiMechanism.valueOf at W
  have F1 : (A.alloc (Function.update v j x)).filter (fun k => owner k = i) = {j} := by
    have hc := h𝒥 _ (hA.feasible _ h1) i
    have hjm : j ∈ (A.alloc (Function.update v j x)).filter (fun k => owner k = i) :=
      Finset.mem_filter.2 ⟨hj, rfl⟩
    apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.2 hjm)
    intro k hk
    rw [Finset.mem_singleton]
    exact Finset.card_le_one.1 hc k hk j hjm
  rw [F1] at W
  have S : ∑ k ∈ (A.alloc (Function.update v j y)).filter (fun k => owner k = i),
      Function.update v j x k =
      ∑ k ∈ (A.alloc (Function.update v j y)).filter (fun k => owner k = i),
      Function.update v j y k := by
    apply Finset.sum_congr rfl
    intro k hk
    have : k ≠ j := by
      rintro rfl; exact hn (Finset.mem_filter.1 hk).1
    simp [Function.update_of_ne this]
  rw [S] at W
  simp at W
  have hxy' : x = y := le_antisymm hxy (by linarith)
  exact hn (hxy' ▸ hj)


set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open MeasureTheory

theorem law_finite (D : ValueDist) : IsFiniteMeasure D.law := by
  constructor
  unfold ValueDist.law
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h : IntegrableOn D.f (Set.Icc D.lo D.hi) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable
  exact h.lintegral_lt_top

theorem law_compl (D : ValueDist) : D.law (Set.Icc D.lo D.hi)ᶜ = 0 := by
  unfold ValueDist.law
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply measurableSet_Icc.compl]
  simp

theorem ae_typeSpace {ι : Type*} [Fintype ι] (D : ι → ValueDist) :
    ∀ᵐ v ∂(prior D), v ∈ typeSpace D := by
  haveI := fun i => law_finite (D i)
  have : ∀ i, ∀ᵐ v ∂(prior D), v i ∈ Set.Icc (D i).lo (D i).hi := by
    intro i
    rw [ae_iff]
    unfold prior
    exact Measure.pi_eval_preimage_null (μ := fun i => (D i).law) (law_compl (D i))
  filter_upwards [ae_all_iff.2 this] with v hv
  intro i _
  exact hv i

theorem measurable_update_pair {J : Type*} [DecidableEq J] (j : J) :
    Measurable (fun q : (J → ℝ) × ℝ => Function.update q.1 j q.2) := by
  apply measurable_pi_lambda
  intro k
  by_cases hk : k = j
  · subst hk
    have : (fun q : (J → ℝ) × ℝ => Function.update q.1 k q.2 k) = fun q => q.2 := by
      funext q; simp
    rw [this]; exact measurable_snd
  · have : (fun q : (J → ℝ) × ℝ => Function.update q.1 j q.2 k) = fun q => q.1 k := by
      funext q; simp [Function.update_of_ne hk]
    rw [this]; exact (measurable_pi_apply k).comp measurable_fst

section
variable {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}

def thrSet (D : J → ValueDist) (A : MultiMechanism J m) (j : J) (v : J → ℝ) : Set ℝ :=
  Set.Icc (D j).lo (D j).hi ∩ {x | j ∈ A.alloc (Function.update v j x)}

noncomputable def thr (D : J → ValueDist) (A : MultiMechanism J m) (j : J) (v : J → ℝ) : ℝ :=
  (D j).hi - (volume (thrSet D A j v)).toReal

theorem thrSet_update (D : J → ValueDist) (A : MultiMechanism J m) (j : J) (v : J → ℝ) (z : ℝ) :
    thrSet D A j (Function.update v j z) = thrSet D A j v := by
  simp [thrSet]

theorem thrSet_fin (D : J → ValueDist) (A : MultiMechanism J m) (j : J) (v : J → ℝ) :
    volume (thrSet D A j v) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.inter_subset_left)

theorem thr_bounds (D : J → ValueDist) (A : MultiMechanism J m) (j : J) (v : J → ℝ) :
    (D j).lo ≤ thr D A j v ∧ thr D A j v ≤ (D j).hi := by
  unfold thr
  constructor
  · have : (volume (thrSet D A j v)).toReal ≤ (D j).hi - (D j).lo := by
      apply ENNReal.toReal_le_of_le_ofReal (by linarith [(D j).lo_lt_hi])
      rw [← Real.volume_Icc]; exact measure_mono Set.inter_subset_left
    linarith
  · linarith [ENNReal.toReal_nonneg (a := volume (thrSet D A j v))]

theorem thr_measurable (D : J → ValueDist) (A : MultiMechanism J m) (hA : ∀ j, MeasurableSet {v | j ∈ A.alloc v})
    (j : J) : Measurable (thr D A j) := by
  unfold thr
  apply measurable_const.sub
  apply ENNReal.measurable_toReal.comp
  have hs : MeasurableSet {q : (J → ℝ) × ℝ | q.2 ∈ Set.Icc (D j).lo (D j).hi ∧
      j ∈ A.alloc (Function.update q.1 j q.2)} :=
    (measurable_snd measurableSet_Icc).inter ((measurable_update_pair j) (hA j))
  exact measurable_measure_prodMk_left hs

variable (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (A : MultiMechanism J m) (hA : IsTruthfulMulti D 𝒥 owner A)
include h𝒥 hA

theorem thr_le (w : J → ℝ) (hw : w ∈ typeSpace D) (j : J) (z : ℝ) (hz : z ∈ Set.Icc (D j).lo (D j).hi)
    (hj : j ∈ A.alloc (Function.update w j z)) : thr D A j w ≤ z := by
  have hsub : Set.Icc z (D j).hi ⊆ thrSet D A j w := by
    intro x hx
    refine ⟨⟨hz.1.trans hx.1, hx.2⟩, ?_⟩
    exact cam_core D 𝒥 owner h𝒥 A hA w hw j z x hz ⟨hz.1.trans hx.1, hx.2⟩ hx.1 hj
  have := ENNReal.toReal_mono (thrSet_fin D A j w) (measure_mono hsub)
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hz.2])] at this
  unfold thr; linarith

theorem thr_ge (w : J → ℝ) (hw : w ∈ typeSpace D) (j : J) (z : ℝ) (hz : z ∈ Set.Icc (D j).lo (D j).hi)
    (hj : j ∉ A.alloc (Function.update w j z)) : z ≤ thr D A j w := by
  have hsub : thrSet D A j w ⊆ Set.Ioc z (D j).hi := by
    intro x hx
    refine ⟨?_, hx.1.2⟩
    by_contra hxz
    push_neg at hxz
    exact hj (cam_core D 𝒥 owner h𝒥 A hA w hw j x z hx.1 hz hxz hx.2)
  have := ENNReal.toReal_le_of_le_ofReal (by linarith [hz.2])
    ((measure_mono hsub).trans (Real.volume_Ioc).le)
  unfold thr; linarith

theorem mem_tS (w : J → ℝ) (hw : w ∈ typeSpace D) (j : J) (z : ℝ) (hz : z ∈ Set.Icc (D j).lo (D j).hi) :
    Function.update w j z ∈ typeSpace D := by
  intro k _
  by_cases hk : k = j
  · subst hk; simpa using hz
  · simpa [Function.update_of_ne hk] using hw k (Set.mem_univ _)

theorem filter_single (w : J → ℝ) (hw : w ∈ typeSpace D) (j : J) (hj : j ∈ A.alloc w) :
    (A.alloc w).filter (fun k => owner k = owner j) = {j} := by
  have hc := h𝒥 _ (hA.feasible _ hw) (owner j)
  have hjm : j ∈ (A.alloc w).filter (fun k => owner k = owner j) :=
    Finset.mem_filter.2 ⟨hj, rfl⟩
  apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.2 hjm)
  intro k hk
  rw [Finset.mem_singleton]
  exact Finset.card_le_one.1 hc k hk j hjm

theorem pay_le_thr (w : J → ℝ) (hw : w ∈ typeSpace D) (j : J) (hj : j ∈ A.alloc w) :
    A.pay w (owner j) ≤ thr D A j w := by
  have key : ∀ x ∈ thrSet D A j w, A.pay w (owner j) ≤ x := by
    intro x hx
    have hb := mem_tS D 𝒥 owner h𝒥 A hA w hw j x hx.1
    have hd := hA.dsic w hw (owner j) _ hb (by
      intro k hk
      have : k ≠ j := fun h => hk (h ▸ rfl)
      simp [Function.update_of_ne this])
    unfold MultiMechanism.utility MultiMechanism.valueOf at hd
    rw [filter_single D 𝒥 owner h𝒥 A hA _ hb j hx.2, filter_single D 𝒥 owner h𝒥 A hA _ hw j hj] at hd
    simp at hd
    have hir := hA.ir_served _ hb (owner j) j hx.2 rfl
    simp at hir
    linarith
  have hpw : A.pay w (owner j) ≤ (D j).hi :=
    (hA.ir_served w hw (owner j) j hj rfl).trans (hw j (Set.mem_univ _)).2
  have hsub : thrSet D A j w ⊆ Set.Icc (max (D j).lo (A.pay w (owner j))) (D j).hi := by
    intro x hx
    exact ⟨max_le hx.1.1 (key x hx), hx.1.2⟩
  have := ENNReal.toReal_le_of_le_ofReal (by
      have := (D j).lo_lt_hi
      exact sub_nonneg.2 (max_le this.le hpw))
    ((measure_mono hsub).trans (Real.volume_Icc).le)
  unfold thr
  have := le_max_right (D j).lo (A.pay w (owner j))
  linarith

noncomputable def copyMech : Mechanism J where
  alloc := A.alloc
  pay v j := if j ∈ A.alloc v then thr D A j v else 0

theorem copyMech_truthful : IsTruthful D 𝒥 (copyMech D A) := by
  haveI := fun i => law_finite (D i)
  haveI : IsFiniteMeasure (prior D) := by unfold prior; infer_instance
  refine ⟨fun v hv => hA.feasible v hv, ?_, ?_, hA.alloc_measurable, ?_, ?_⟩
  · intro v hv j x' hx'
    have hvj : v j ∈ Set.Icc (D j).lo (D j).hi := hv j (Set.mem_univ _)
    have hthr : thr D A j (Function.update v j x') = thr D A j v := by
      unfold thr; rw [thrSet_update]
    unfold Mechanism.utility copyMech
    simp only
    rw [hthr]
    have e : Function.update v j (v j) = v := by simp
    by_cases h1 : j ∈ A.alloc (Function.update v j x') <;> by_cases h2 : j ∈ A.alloc v <;>
      simp only [h1, h2, if_true, if_false]
    all_goals first
      | (have := thr_ge D 𝒥 owner h𝒥 A hA v hv j (v j) hvj (by rw [e]; exact h2); linarith)
      | (have := thr_le D 𝒥 owner h𝒥 A hA v hv j (v j) hvj (by rw [e]; exact h2); linarith)
  · intro v hv j
    have hvj : v j ∈ Set.Icc (D j).lo (D j).hi := hv j (Set.mem_univ _)
    have e : Function.update v j (v j) = v := by simp
    unfold Mechanism.utility copyMech
    simp only
    by_cases h2 : j ∈ A.alloc v <;> simp only [h2, if_true, if_false]
    · have := thr_le D 𝒥 owner h𝒥 A hA v hv j (v j) hvj (by rw [e]; exact h2)
      linarith
    · simp
  · intro j
    exact Measurable.ite (hA.alloc_measurable j) (thr_measurable D A hA.alloc_measurable j)
      measurable_const
  · intro j
    refine Integrable.of_bound (C := |(D j).lo| + |(D j).hi|) ?_ ?_
    · exact (Measurable.ite (hA.alloc_measurable j) (thr_measurable D A hA.alloc_measurable j)
        measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun v => ?_)
      simp only [copyMech]
      split_ifs
      · have := thr_bounds D A j v
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> cases abs_cases (D j).lo <;> cases abs_cases (D j).hi <;> linarith
      · simp; positivity

theorem rlc_core : ∃ A' : Mechanism J, IsTruthful D 𝒥 A' ∧ revenueMulti D A ≤ revenue D A' := by
  haveI := fun i => law_finite (D i)
  refine ⟨copyMech D A, copyMech_truthful D 𝒥 owner h𝒥 A hA, ?_⟩
  have hT := copyMech_truthful D 𝒥 owner h𝒥 A hA
  unfold revenueMulti revenue
  apply integral_mono_ae
  · exact integrable_finsetSum _ (fun i _ => hA.pay_integrable i)
  · exact integrable_finsetSum _ (fun i _ => hT.pay_integrable i)
  filter_upwards [ae_typeSpace D] with v hv
  simp only [copyMech]
  rw [← Finset.sum_filter]
  calc ∑ i, A.pay v i
      = ∑ i, ∑ j ∈ (A.alloc v).filter (fun j => owner j = i), A.pay v (owner j) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases he : (A.alloc v).filter (fun j => owner j = i) = ∅
        · rw [he, hA.ir_unserved v hv i he]; simp
        · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 he
          have hj' := Finset.mem_filter.1 hj
          rw [← hj'.2, filter_single D 𝒥 owner h𝒥 A hA v hv j hj'.1]
          simp
    _ = ∑ j ∈ A.alloc v, A.pay v (owner j) :=
        Finset.sum_fiberwise (A.alloc v) owner (fun j => A.pay v (owner j))
    _ ≤ ∑ j ∈ A.alloc v, thr D A j v := by
        apply Finset.sum_le_sum
        intro j hj
        exact pay_le_thr D 𝒥 owner h𝒥 A hA v hv j hj
    _ = _ := by simp

end
end CHMSPricing.UnitDemand

open CHMSPricing.UnitDemand


theorem solution {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (A : MultiMechanism J m) (hA : IsTruthfulMulti D 𝒥 owner A) :
    ∃ A' : Mechanism J, IsTruthful D 𝒥 A' ∧ revenueMulti D A ≤ revenue D A' := by
  exact rlc_core D 𝒥 owner h𝒥 A hA
