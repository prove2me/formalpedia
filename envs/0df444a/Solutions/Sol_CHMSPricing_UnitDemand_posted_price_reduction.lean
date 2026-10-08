-- Prove2me | solution 1 for CHMSPricing.UnitDemand.posted_price_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:19:25.662093+00:00
-- url     : https://prove2.me/submissions/407a5a16-839a-443a-93f8-713cec5a79bb

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism
import Definitions.Def_CHMSPricing_UnitDemand_MenuMech



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
section
variable {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}

theorem mc_some {𝒥 : SetSystem J} {owner : J → Fin m} {p v : J → ℝ} {A : Finset J} {i : Fin m}
    {j : J} (h : menuChoice 𝒥 owner p v A i = some j) :
    owner j = i ∧ 𝒥.Feasible (insert j A) ∧ p j ≤ v j := by
  unfold menuChoice at h
  split_ifs at h with hne
  · simp only [Option.some.injEq] at h
    have hmem := Finset.min'_mem _ (hne.image (Fintype.equivFin J))
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 hmem
    have : j = a := by rw [← h, ← hae]; simp
    subst this
    unfold menuBest at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ha.1

theorem mc_none {𝒥 : SetSystem J} {owner : J → Fin m} {p v : J → ℝ} {A : Finset J} {i : Fin m}
    (h : menuChoice 𝒥 owner p v A i = none) (j : J) (hj : owner j = i) (hp : p j ≤ v j) :
    ¬ 𝒥.Feasible (insert j A) := by
  intro hf
  unfold menuChoice at h
  split_ifs at h with hne
  apply hne
  classical
  unfold menuBest
  set C := Finset.univ.filter (fun j => owner j = i ∧ 𝒥.Feasible (insert j A) ∧ p j ≤ v j)
  have hC : C.Nonempty := ⟨j, by simp [C, hj, hf, hp]⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image C (fun j => v j - p j) hC
  refine ⟨a, ?_⟩
  simp only [Finset.mem_filter]
  refine ⟨ha, ?_⟩
  convert hmax

theorem step_sub (𝒥 : SetSystem J) (owner : J → Fin m) (p v : J → ℝ) (A : Finset J) (i : Fin m) :
    A ⊆ menuStep 𝒥 owner p v A i := by
  unfold menuStep
  split
  · exact Finset.subset_insert _ _
  · exact le_rfl

theorem fold_sub (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m)) (p v : J → ℝ)
    (L : List (Fin m)) (A : Finset J) :
    A ⊆ L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A := by
  induction L generalizing A with
  | nil => exact le_rfl
  | cons k L ih =>
    simp only [List.foldl_cons]
    exact (step_sub _ _ _ _ _ _).trans (ih _)

theorem fold_inv (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m)) (p v : J → ℝ)
    (L : List (Fin m)) (A : Finset J) (h1 : A ⊆ desiring p v) (h2 : 𝒥.Feasible A) :
    L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A ⊆ desiring p v ∧
    𝒥.Feasible (L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A) := by
  induction L generalizing A with
  | nil => exact ⟨h1, h2⟩
  | cons k L ih =>
    simp only [List.foldl_cons]
    apply ih
    · unfold menuStep
      split
      · next j hj =>
        obtain ⟨_, _, hp⟩ := mc_some hj
        exact Finset.insert_subset (by simp [desiring, hp]) h1
      · exact h1
    · unfold menuStep
      split
      · next j hj => exact (mc_some hj).2.1
      · exact h2

theorem fold_max (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (σ : Equiv.Perm (Fin m)) (p v : J → ℝ)
    (L : List (Fin m)) (A : Finset J) (k : Fin m) (hk : k ∈ L) (i : J) (hi : i ∈ desiring p v)
    (hown : owner i = σ k)
    (hn : i ∉ L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A) :
    ¬ 𝒥.Feasible (insert i (L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A)) := by
  induction L generalizing A with
  | nil => simp at hk
  | cons k' L ih =>
    simp only [List.foldl_cons] at hn ⊢
    by_cases hkk : k = k'
    · subst hkk
      have hsub := fold_sub 𝒥 owner σ p v L (menuStep 𝒥 owner p v A (σ k))
      have hpi : p i ≤ v i := by simpa [desiring] using hi
      cases hc : menuChoice 𝒥 owner p v A (σ k) with
      | none =>
        have hnf := mc_none hc i hown hpi
        intro hf
        apply hnf
        refine 𝒥.feasible_mono ?_ hf
        apply Finset.insert_subset_insert
        refine le_trans ?_ hsub
        exact step_sub _ _ _ _ _ _
      | some j =>
        obtain ⟨hoj, _, _⟩ := mc_some hc
        have hjS : j ∈ menuStep 𝒥 owner p v A (σ k) := by
          unfold menuStep; rw [hc]; exact Finset.mem_insert_self _ _
        have hjR := hsub hjS
        have hij : i ≠ j := fun h => hn (h ▸ hjR)
        intro hf
        have := h𝒥 _ hf (σ k)
        have h2 : ({i, j} : Finset J) ⊆ (insert i (L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k))
            (menuStep 𝒥 owner p v A (σ k)))).filter (fun j => owner j = σ k) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · simp [hown]
          · simp [hoj, hjR]
        have := (Finset.card_le_card h2).trans this
        rw [Finset.card_pair hij] at this
        omega
    · have hk' : k ∈ L := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h hkk
        · exact h
      exact ih _ hk' hn

theorem mm_core {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (σ : Equiv.Perm (Fin m)) (p v : J → ℝ) :
    IsMaxFeasDesiring 𝒥 p v ((menuMech 𝒥 owner σ p).alloc v) := by
  have inv := fold_inv 𝒥 owner σ p v (List.finRange m) ∅ (Finset.empty_subset _) 𝒥.feasible_empty
  refine ⟨inv.1, inv.2, ?_⟩
  intro i hi hn
  exact fold_max 𝒥 owner h𝒥 σ p v (List.finRange m) ∅ (σ.symm (owner i)) (List.mem_finRange _)
    i hi (by simp) hn

end

section
variable {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}

theorem mc_best {𝒥 : SetSystem J} {owner : J → Fin m} {p v : J → ℝ} {A : Finset J} {i : Fin m}
    {j : J} (h : menuChoice 𝒥 owner p v A i = some j) :
    ∀ j', owner j' = i → 𝒥.Feasible (insert j' A) → p j' ≤ v j' → v j' - p j' ≤ v j - p j := by
  unfold menuChoice at h
  split_ifs at h with hne
  · simp only [Option.some.injEq] at h
    have hmem := Finset.min'_mem _ (hne.image (Fintype.equivFin J))
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 hmem
    have : j = a := by rw [← h, ← hae]; simp
    subst this
    unfold menuBest at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    intro j' h1 h2 h3
    exact ha.2 j' ⟨h1, h2, h3⟩

theorem best_congr (𝒥 : SetSystem J) (owner : J → Fin m) (p v b : J → ℝ) (A : Finset J) (i : Fin m)
    (h : ∀ j, owner j = i → v j = b j) :
    menuBest 𝒥 owner p v A i = menuBest 𝒥 owner p b A i := by
  ext j
  simp only [menuBest, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨⟨h1, h2, by rwa [← h j h1]⟩, fun j' ⟨h1', h2', h3'⟩ => ?_⟩
    have := h4 j' ⟨h1', h2', by rwa [h j' h1']⟩
    rwa [h j h1, h j' h1'] at this
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨⟨h1, h2, by rwa [h j h1]⟩, fun j' ⟨h1', h2', h3'⟩ => ?_⟩
    have := h4 j' ⟨h1', h2', by rwa [← h j' h1']⟩
    rwa [← h j h1, ← h j' h1'] at this

theorem step_congr (𝒥 : SetSystem J) (owner : J → Fin m) (p v b : J → ℝ) (A : Finset J) (i : Fin m)
    (h : ∀ j, owner j = i → v j = b j) :
    menuStep 𝒥 owner p v A i = menuStep 𝒥 owner p b A i := by
  simp only [menuStep, menuChoice, best_congr 𝒥 owner p v b A i h]

theorem step_some {𝒥 : SetSystem J} {owner : J → Fin m} {p v : J → ℝ} {A : Finset J} {i : Fin m}
    {j : J} (h : menuChoice 𝒥 owner p v A i = some j) : menuStep 𝒥 owner p v A i = insert j A := by
  unfold menuStep; rw [h]

theorem step_none {𝒥 : SetSystem J} {owner : J → Fin m} {p v : J → ℝ} {A : Finset J} {i : Fin m}
    (h : menuChoice 𝒥 owner p v A i = none) : menuStep 𝒥 owner p v A i = A := by
  unfold menuStep; rw [h]

theorem step_filter (𝒥 : SetSystem J) (owner : J → Fin m) (p v : J → ℝ) (A : Finset J) (i i' : Fin m)
    (hne : i' ≠ i) :
    (menuStep 𝒥 owner p v A i').filter (fun j => owner j = i) = A.filter (fun j => owner j = i) := by
  unfold menuStep
  split
  · next j hj =>
    have := (mc_some hj).1
    rw [Finset.filter_insert]
    simp [this, hne]
  · rfl

theorem fold_filter (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m)) (p v : J → ℝ)
    (i : Fin m) (L : List (Fin m)) (hL : ∀ k ∈ L, σ k ≠ i) (A : Finset J) :
    (L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A).filter (fun j => owner j = i) =
      A.filter (fun j => owner j = i) := by
  induction L generalizing A with
  | nil => rfl
  | cons k L ih =>
    simp only [List.foldl_cons]
    rw [ih (fun k' hk' => hL k' (List.mem_cons_of_mem _ hk'))]
    exact step_filter _ _ _ _ _ _ _ (hL k (List.mem_cons_self))

theorem fold_congr (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m)) (p v b : J → ℝ)
    (i : Fin m) (L : List (Fin m)) (hL : ∀ k ∈ L, σ k ≠ i) (hvb : ∀ j, owner j ≠ i → v j = b j)
    (A : Finset J) :
    L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A =
      L.foldl (fun A k => menuStep 𝒥 owner p b A (σ k)) A := by
  induction L generalizing A with
  | nil => rfl
  | cons k L ih =>
    simp only [List.foldl_cons]
    rw [step_congr 𝒥 owner p v b A (σ k) (fun j hj => hvb j (by rw [hj]; exact hL k List.mem_cons_self))]
    exact ih (fun k' hk' => hL k' (List.mem_cons_of_mem _ hk')) _

/-- The services of buyer `i` allocated by the menu mechanism. -/
theorem alloc_filter_eq (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m)) (p : J → ℝ)
    (i : Fin m) : ∃ s t : List (Fin m), (∀ k ∈ s, σ k ≠ i) ∧
      ∀ v : J → ℝ, (menuAlloc 𝒥 owner σ p v).filter (fun j => owner j = i) =
        (match menuChoice 𝒥 owner p v (s.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) ∅) i with
          | some j => {j}
          | none => ∅) ∧ t = t := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem (List.mem_finRange (σ.symm i))
  have hnd := List.nodup_finRange m
  rw [hst] at hnd
  have hs : ∀ k ∈ s, σ k ≠ i := by
    intro k hk he
    have : k = σ.symm i := by rw [← he]; simp
    subst this
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ hk _ List.mem_cons_self rfl
  have ht : ∀ k ∈ t, σ k ≠ i := by
    intro k hk he
    have : k = σ.symm i := by rw [← he]; simp
    subst this
    rw [List.nodup_append] at hnd
    exact (List.nodup_cons.1 hnd.2.1).1 hk
  refine ⟨s, t, hs, fun v => ⟨?_, rfl⟩⟩
  unfold menuAlloc
  rw [hst, List.foldl_append, List.foldl_cons, fold_filter 𝒥 owner σ p v i t ht]
  simp only [Equiv.apply_symm_apply]
  have h0 := fold_filter 𝒥 owner σ p v i s hs ∅
  cases hc : menuChoice 𝒥 owner p v (s.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) ∅) i with
  | some j =>
    rw [step_some hc, Finset.filter_insert, h0]
    simp [(mc_some hc).1]
  | none => rw [step_none hc, h0]; simp

end

section meas
variable {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}

local instance instMSFinset : MeasurableSpace (Finset J) := ⊤
local instance instDMSFinset : DiscreteMeasurableSpace (Finset J) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem meas_of_mem (F : (J → ℝ) → Finset J) (h : ∀ j, MeasurableSet {v | j ∈ F v}) :
    Measurable F := by
  apply measurable_to_countable'
  intro M
  have : F ⁻¹' {M} = ⋂ j, {v | j ∈ F v ↔ j ∈ M} := by
    ext v; simp [Finset.ext_iff]
  rw [this]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j ∈ M
  · simpa [hj] using h j
  · have := (h j).compl
    convert this using 1
    ext v; simp [hj]

theorem best_meas (𝒥 : SetSystem J) (owner : J → Fin m) (p : J → ℝ) (A : Finset J) (i : Fin m) :
    Measurable (fun v => menuBest 𝒥 owner p v A i) := by
  apply meas_of_mem
  intro j
  have hle : ∀ j, Measurable (fun v : J → ℝ => p j ≤ v j) := fun j =>
    measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_pi_apply j))
  have hle2 : ∀ j', Measurable (fun v : J → ℝ => v j' - p j' ≤ v j - p j) := fun j' =>
    measurableSet_setOfPred.1 (measurableSet_le ((measurable_pi_apply j').sub_const _)
      ((measurable_pi_apply j).sub_const _))
  have : {v : J → ℝ | j ∈ menuBest 𝒥 owner p v A i} =
      {v | (owner j = i ∧ 𝒥.Feasible (insert j A) ∧ p j ≤ v j) ∧
        ∀ j', (owner j' = i ∧ 𝒥.Feasible (insert j' A) ∧ p j' ≤ v j') →
          v j' - p j' ≤ v j - p j} := by
    ext v
    simp only [Set.mem_setOf_eq, menuBest, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [this]
  apply measurableSet_setOfPred.2
  refine Measurable.and (Measurable.and measurable_const (Measurable.and measurable_const (hle j))) ?_
  apply Measurable.forall; intro j'
  exact Measurable.imp (Measurable.and measurable_const (Measurable.and measurable_const (hle j')))
    (hle2 j')

theorem step_meas (𝒥 : SetSystem J) (owner : J → Fin m) (p : J → ℝ) (A : Finset J) (i : Fin m) :
    Measurable (fun v => menuStep 𝒥 owner p v A i) := by
  let H : Finset J → Finset J := fun M =>
    match (if h : M.Nonempty then
      some ((Fintype.equivFin J).symm ((M.image (Fintype.equivFin J)).min' (h.image _)))
      else none) with
    | some j => insert j A
    | none => A
  have e : (fun v => menuStep 𝒥 owner p v A i) = H ∘ (fun v => menuBest 𝒥 owner p v A i) := by
    funext v; rfl
  rw [e]
  exact (Measurable.of_discrete).comp (best_meas 𝒥 owner p A i)

theorem fold_meas (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m)) (p : J → ℝ)
    (L : List (Fin m)) : ∀ A : Finset J,
    Measurable (fun v => L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A) := by
  induction L with
  | nil => intro A; exact measurable_const
  | cons k L ih =>
    intro A
    simp only [List.foldl_cons]
    have hG : Measurable (fun q : Finset J × (J → ℝ) =>
        L.foldl (fun A k => menuStep 𝒥 owner p q.2 A (σ k)) q.1) :=
      measurable_from_prod_countable_right (fun B => ih B)
    have hc := hG.comp ((step_meas 𝒥 owner p A (σ k)).prodMk measurable_id)
    exact hc

theorem alloc_meas (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m)) (p : J → ℝ) :
    Measurable (fun v => menuAlloc 𝒥 owner σ p v) :=
  fold_meas 𝒥 owner σ p _ ∅

theorem desiring_meas (p : J → ℝ) : Measurable (fun v : J → ℝ => desiring p v) := by
  apply meas_of_mem
  intro j
  have : {v : J → ℝ | j ∈ desiring p v} = {v | p j ≤ v j} := by
    ext v; simp [desiring]
  rw [this]
  exact measurableSet_le measurable_const (measurable_pi_apply j)

theorem oblf_meas (𝒥 : SetSystem J) (p : J → ℝ) :
    Measurable (fun v => (maxFeasDesiringSets 𝒥 p v).inf' (maxFeasDesiringSets_nonempty 𝒥 p v)
      (fun S => ∑ i ∈ S, p i)) := by
  classical
  let f := fun v => (maxFeasDesiringSets 𝒥 p v).inf' (maxFeasDesiringSets_nonempty 𝒥 p v)
      (fun S => ∑ i ∈ S, p i)
  have hcong : ∀ v w, desiring p v = desiring p w → f v = f w := by
    intro v w h
    have hs : maxFeasDesiringSets 𝒥 p v = maxFeasDesiringSets 𝒥 p w := by
      unfold maxFeasDesiringSets IsMaxFeasDesiring
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, h]
    exact Finset.inf'_congr _ hs (fun _ _ => rfl)
  let g : Finset J → ℝ := fun D => if h : ∃ w, desiring p w = D then f h.choose else 0
  have e : f = g ∘ (fun v => desiring p v) := by
    funext v
    have h : ∃ w, desiring p w = desiring p v := ⟨v, rfl⟩
    simp only [Function.comp, g, dif_pos h]
    exact (hcong _ _ h.choose_spec).symm
  show Measurable f
  rw [e]
  exact (Measurable.of_discrete).comp (desiring_meas p)

variable (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m)

theorem menu_truthful (σ : Equiv.Perm (Fin m)) (p : J → ℝ) :
    IsTruthfulMulti D 𝒥 owner (menuMech 𝒥 owner σ p) := by
  haveI := fun i => law_finite (D i)
  haveI : IsFiniteMeasure (prior D) := by unfold prior; infer_instance
  have hmeas := alloc_meas 𝒥 owner σ p
  have hpm : ∀ i, Measurable (fun v => (menuMech 𝒥 owner σ p).pay v i) := by
    intro i
    show Measurable ((fun S : Finset J => ∑ j ∈ S.filter (fun j => owner j = i), p j) ∘
      (fun v => menuAlloc 𝒥 owner σ p v))
    exact (Measurable.of_discrete).comp hmeas
  refine ⟨?_, ?_, ?_, ?_, ?_, hpm, ?_⟩
  · intro v _
    exact (fold_inv 𝒥 owner σ p v (List.finRange m) ∅ (Finset.empty_subset _)
      𝒥.feasible_empty).2
  · intro v _ i b _ hvb
    obtain ⟨s, t, hs, hF⟩ := alloc_filter_eq 𝒥 owner σ p i
    have hpre := fold_congr 𝒥 owner σ p b v i s hs hvb ∅
    unfold MultiMechanism.utility MultiMechanism.valueOf menuMech
    simp only
    rw [(hF b).1, hpre, (hF v).1]
    cases hcb : menuChoice 𝒥 owner p b (List.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) ∅ s) i with
    | none =>
      cases hcv : menuChoice 𝒥 owner p v (List.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) ∅ s) i with
      | none => simp
      | some jv => simp only [Finset.sum_empty, Finset.sum_singleton]; linarith [(mc_some hcv).2.2]
    | some jb =>
      cases hcv : menuChoice 𝒥 owner p v (List.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) ∅ s) i with
      | none =>
        simp only [Finset.sum_empty, Finset.sum_singleton]
        by_contra hlt
        have hle : p jb ≤ v jb := by linarith
        exact mc_none hcv jb (mc_some hcb).1 hle (mc_some hcb).2.1
      | some jv =>
        simp only [Finset.sum_singleton]
        by_cases hle : p jb ≤ v jb
        · exact mc_best hcv jb (mc_some hcb).1 (mc_some hcb).2.1 hle
        · linarith [(mc_some hcv).2.2]
  · intro v _ i j hj hji
    obtain ⟨s, t, hs, hF⟩ := alloc_filter_eq 𝒥 owner σ p i
    have hjF : j ∈ (menuAlloc 𝒥 owner σ p v).filter (fun j => owner j = i) :=
      Finset.mem_filter.2 ⟨hj, hji⟩
    show ∑ j ∈ (menuAlloc 𝒥 owner σ p v).filter (fun j => owner j = i), p j ≤ v j
    rw [(hF v).1] at hjF ⊢
    cases hcv : menuChoice 𝒥 owner p v (List.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) ∅ s) i
    · rw [hcv] at hjF; simp at hjF
    · rename_i jv
      rw [hcv] at hjF
      simp only [Finset.mem_singleton] at hjF
      subst hjF
      simp only [Finset.sum_singleton]
      exact (mc_some hcv).2.2
  · intro v _ i h
    show ∑ j ∈ (menuAlloc 𝒥 owner σ p v).filter (fun j => owner j = i), p j = 0
    have : (menuAlloc 𝒥 owner σ p v).filter (fun j => owner j = i) = ∅ := h
    rw [this]; simp
  · intro j
    exact hmeas (MeasurableSet.of_discrete (s := {S : Finset J | j ∈ S}))
  · intro i
    refine Integrable.of_bound (C := ∑ j, |p j|) (hpm i).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun v => ?_)
    show ‖∑ j ∈ (menuAlloc 𝒥 owner σ p v).filter (fun j => owner j = i), p j‖ ≤ _
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)

theorem obl_le (h𝒥 : IsUnitDemand 𝒥 owner) (σ : Equiv.Perm (Fin m)) (p : J → ℝ) :
    oblRevenue D 𝒥 p ≤ revenueMulti D (menuMech 𝒥 owner σ p) := by
  haveI := fun i => law_finite (D i)
  haveI : IsFiniteMeasure (prior D) := by unfold prior; infer_instance
  have hT := menu_truthful D 𝒥 owner σ p
  unfold oblRevenue revenueMulti
  apply integral_mono
  · refine Integrable.of_bound (C := ∑ j, |p j|) (oblf_meas 𝒥 p).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun v => ?_)
    have hb : ∀ S : Finset J, |∑ i ∈ S, p i| ≤ ∑ j, |p j| := fun S =>
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _))
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨S0, hS0⟩ := maxFeasDesiringSets_nonempty 𝒥 p v
    constructor
    · apply Finset.le_inf'
      intro S _
      exact (abs_le.1 (hb S)).1
    · exact (Finset.inf'_le _ hS0).trans (abs_le.1 (hb S0)).2
  · exact integrable_finsetSum _ (fun i _ => hT.pay_integrable i)
  · intro v
    have hmax := mm_core 𝒥 owner h𝒥 σ p v
    have hmem : (menuMech 𝒥 owner σ p).alloc v ∈ maxFeasDesiringSets 𝒥 p v := by
      simp only [maxFeasDesiringSets, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hmax.1, hmax⟩
    refine (Finset.inf'_le _ hmem).trans (le_of_eq ?_)
    simp only [menuMech]
    exact (Finset.sum_fiberwise _ owner p).symm

theorem ppr_core (h𝒥 : IsUnitDemand 𝒥 owner)
    (p : J → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hopm : ∀ M' : Mechanism J, IsTruthful D 𝒥 M' → revenue D M' ≤ α * oblRevenue D 𝒥 p) :
    ∀ σ : Equiv.Perm (Fin m),
      IsTruthfulMulti D 𝒥 owner (menuMech 𝒥 owner σ p) ∧
      ∀ A : MultiMechanism J m, IsTruthfulMulti D 𝒥 owner A →
        revenueMulti D A ≤ α * revenueMulti D (menuMech 𝒥 owner σ p) := by
  intro σ
  refine ⟨menu_truthful D 𝒥 owner σ p, fun A hA => ?_⟩
  obtain ⟨A', hA', hle⟩ := rlc_core D 𝒥 owner h𝒥 A hA
  calc revenueMulti D A ≤ revenue D A' := hle
    _ ≤ α * oblRevenue D 𝒥 p := hopm A' hA'
    _ ≤ α * revenueMulti D (menuMech 𝒥 owner σ p) :=
        mul_le_mul_of_nonneg_left (obl_le D 𝒥 owner h𝒥 σ p) hα

end meas
end CHMSPricing.UnitDemand

open CHMSPricing.UnitDemand


theorem solution {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (p : J → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hopm : ∀ M' : Mechanism J, IsTruthful D 𝒥 M' → revenue D M' ≤ α * oblRevenue D 𝒥 p) :
    ∀ σ : Equiv.Perm (Fin m),
      IsTruthfulMulti D 𝒥 owner (menuMech 𝒥 owner σ p) ∧
      ∀ A : MultiMechanism J m, IsTruthfulMulti D 𝒥 owner A →
        revenueMulti D A ≤ α * revenueMulti D (menuMech 𝒥 owner σ p) := by
  exact ppr_core D 𝒥 owner h𝒥 p α hα hopm
