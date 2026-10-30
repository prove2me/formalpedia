-- Prove2me | solution 1 for BwSC.LowerBound.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:50:22.574327+00:00
-- url     : https://prove2.me/submissions/f721c975-515f-4a84-990e-63cb6ad169f5

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral
import Theorems.Thm_BanditAlgorithm_klDiv_gaussianReal_same_variance
import Theorems.Thm_BwSC_LowerBound_corollary_4

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.KLAux

variable {K : ℕ}

/-- Round `n + 1` can still be recorded faithfully. -/
def active (lo hi : ℕ) (k : Fin K) {n : ℕ} (r : BanditHistory K n) : Prop :=
  n + 1 < lo ∨ (n + 1 ≤ hi ∧ ∀ s, lo ≤ s → s ≤ n → act r s ≠ some k)

lemma act_snoc_le {n : ℕ} (h : BanditHistory K n) (ax : Fin K × ℝ) (s : ℕ) (hs : s ≤ n) :
    act (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1)) s = act h s := by
  simp only [act, actA, actions]
  by_cases h1 : 1 ≤ s ∧ s ≤ n
  · rw [dif_pos ⟨h1.1, by omega⟩, dif_pos h1]
    have : (⟨s - 1, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨s - 1, by omega⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · rw [dif_neg (by omega), dif_neg h1]

lemma actA_snoc_le {n : ℕ} (h : BanditHistory K n) (ax : Fin K × ℝ) (s : ℕ) (hs : s ≤ n) :
    actA (actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1))) s =
      actA (actions h) s :=
  act_snoc_le h ax s hs

/-- The recorded value of round `n + 1`. -/
noncomputable def stepRec (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n)
    (ax : Fin K × ℝ) : Fin K × ℝ := by
  classical
  exact if (n + 1 < lo ∨ (n + 1 ≤ hi ∧ ax.1 ≠ k ∧ ∀ s, lo ≤ s → s ≤ n → act h s ≠ some k))
    then ax else (k, 0)

lemma censor_snoc (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n) (ax : Fin K × ℝ) :
    stopCensor lo hi k (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1)) =
      Fin.snoc (α := fun _ => Fin K × ℝ) (stopCensor lo hi k h) (stepRec lo hi k h ax) := by
  classical
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, stopCensor, stepRec]
    have hiff : keepRound lo hi k (actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax :
        BanditHistory K (n + 1))) (Fin.last n) ↔
        (n + 1 < lo ∨ (n + 1 ≤ hi ∧ ax.1 ≠ k ∧ ∀ s, lo ≤ s → s ≤ n → act h s ≠ some k)) := by
      unfold keepRound
      simp only [Fin.val_last, Finset.mem_Ico]
      have ha : actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1))
          (Fin.last n) = ax.1 := by simp [actions]
      rw [ha]
      constructor
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨h1, h2, fun s hs1 hs2 => ?_⟩
          have := h3 s ⟨hs1, by omega⟩
          rwa [actA_snoc_le h ax s hs2] at this
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨h1, h2, fun s hs => ?_⟩
          rw [actA_snoc_le h ax s (by omega)]
          exact h3 s hs.1 (by omega)
    by_cases hk : keepRound lo hi k (actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax :
        BanditHistory K (n + 1))) (Fin.last n)
    · rw [if_pos hk, if_pos (hiff.mp hk)]
    · rw [if_neg hk, if_neg (fun hc => hk (hiff.mpr hc))]
  · simp only [Fin.snoc_castSucc, stopCensor]
    have hiff : keepRound lo hi k (actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax :
        BanditHistory K (n + 1))) (Fin.castSucc j) ↔ keepRound lo hi k (actions h) j := by
      unfold keepRound
      simp only [Fin.coe_castSucc, Finset.mem_Ico]
      have ha : actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1))
          (Fin.castSucc j) = actions h j := by simp [actions]
      rw [ha]
      constructor
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨h1, h2, fun s hs => ?_⟩
          have := h3 s hs
          rwa [actA_snoc_le h ax s (by omega)] at this
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨h1, h2, fun s hs => ?_⟩
          rw [actA_snoc_le h ax s (by omega)]
          exact h3 s hs
    by_cases hk : keepRound lo hi k (actions h) j
    · rw [if_pos (hiff.mpr hk), if_pos hk]
    · rw [if_neg (fun hc => hk (hiff.mp hc)), if_neg hk]

lemma act_of_out {T : ℕ} (h : BanditHistory K T) (t : ℕ) (ht : ¬ (1 ≤ t ∧ t ≤ T)) :
    act h t = none := by
  simp [act, actA, ht]

lemma act_of_in {T : ℕ} (h : BanditHistory K T) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ T) :
    act h t = some ((h ⟨t - 1, by omega⟩).1) := by
  simp [act, actA, ht, actions]

/-- The stopped record, read round by round. -/
lemma act_censor {T : ℕ} (lo hi : ℕ) (k : Fin K) (h : BanditHistory K T) (t : ℕ)
    (ht : 1 ≤ t ∧ t ≤ T) :
    act (stopCensor lo hi k h) t =
      if (t < lo ∨ (t ≤ hi ∧ act h t ≠ some k ∧ ∀ s, lo ≤ s → s < t → act h s ≠ some k))
      then act h t else some k := by
  rw [act_of_in _ t ht, act_of_in h t ht]
  have hidx : ((⟨t - 1, by omega⟩ : Fin T).val + 1) = t := by simp; omega
  have hiff : keepRound lo hi k (actions h) ⟨t - 1, by omega⟩ ↔
      (t < lo ∨ (t ≤ hi ∧ some ((h ⟨t - 1, by omega⟩).1) ≠ some k ∧
        ∀ s, lo ≤ s → s < t → act h s ≠ some k)) := by
    unfold keepRound
    rw [hidx]
    simp only [Finset.mem_Ico, ne_eq, Option.some.injEq]
    constructor
    · rintro (h1 | ⟨h1, h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2, fun s hs1 hs2 => h3 s ⟨hs1, hs2⟩⟩
    · rintro (h1 | ⟨h1, h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2, fun s hs => h3 s hs.1 hs.2⟩
  unfold stopCensor
  by_cases hk : keepRound lo hi k (actions h) ⟨t - 1, by omega⟩
  · rw [if_pos hk, if_pos (hiff.mp hk)]
  · rw [if_neg hk, if_neg (fun hc => hk (hiff.mpr hc))]


lemma active_censor_eq (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n)
    (ha : active lo hi k h) : stopCensor lo hi k h = h := by
  funext i
  unfold stopCensor
  rw [if_pos]
  unfold keepRound
  rcases ha with h1 | ⟨h1, h2⟩
  · left; omega
  · by_cases hlo : i.val + 1 < lo
    · exact Or.inl hlo
    · right
      refine ⟨by omega, ?_, fun s hs => ?_⟩
      · intro hk
        apply h2 (i.val + 1) (by omega) (by omega)
        rw [act_of_in h (i.val + 1) ⟨by omega, by omega⟩]
        simp only [Nat.add_sub_cancel]
        rw [show (⟨i.val, by omega⟩ : Fin n) = i from rfl]
        simp [actions] at hk; rw [hk]
      · rw [Finset.mem_Ico] at hs
        exact h2 s hs.1 (by omega)

lemma active_censor_iff (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n) :
    active lo hi k (stopCensor lo hi k h) ↔ active lo hi k h := by
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · exact Or.inl h1
    · right
      refine ⟨h1, fun s hs1 hs2 hc => ?_⟩
      have hv : 1 ≤ s ∧ s ≤ n := by
        by_contra hv
        rw [act_of_out h s hv] at hc; exact absurd hc (by simp)
      have := h2 s hs1 hs2
      rw [act_censor lo hi k h s hv] at this
      split_ifs at this with hcond
      · rcases hcond with hc1 | ⟨_, hc2, _⟩
        · omega
        · exact hc2 hc
      · exact this rfl
  · intro ha
    rw [active_censor_eq lo hi k h ha]; exact ha

lemma measurableSet_active (lo hi : ℕ) (k : Fin K) (n : ℕ) :
    MeasurableSet {r : BanditHistory K n | active lo hi k r} := by
  have : {r : BanditHistory K n | active lo hi k r} =
      actions ⁻¹' {a : Fin n → Fin K | n + 1 < lo ∨
        (n + 1 ≤ hi ∧ ∀ s, lo ≤ s → s ≤ n → actA a s ≠ some k)} := by
    ext r; rfl
  rw [this]; exact measurable_actions (Set.toFinite _).measurableSet

/-- The recording map of an active round. -/
noncomputable def stepMap (lo : ℕ) (k : Fin K) (n : ℕ) (ax : Fin K × ℝ) : Fin K × ℝ := by
  classical
  exact if n + 1 < lo ∨ ax.1 ≠ k then ax else (k, 0)

lemma measurable_stepMap (lo : ℕ) (k : Fin K) (n : ℕ) : Measurable (stepMap lo k n) := by
  classical
  unfold stepMap
  apply Measurable.ite _ measurable_id measurable_const
  have : {ax : Fin K × ℝ | n + 1 < lo ∨ ax.1 ≠ k} = Prod.fst ⁻¹' {a | n + 1 < lo ∨ a ≠ k} := rfl
  rw [this]; exact measurable_fst (Set.toFinite _).measurableSet

lemma stepRec_of_active (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n)
    (ha : active lo hi k h) : stepRec lo hi k h = stepMap lo k n := by
  classical
  funext ax
  unfold stepRec stepMap
  rcases ha with h1 | ⟨h1, h2⟩
  · rw [if_pos (Or.inl h1), if_pos (Or.inl h1)]
  · by_cases hk : ax.1 ≠ k
    · rw [if_pos (Or.inr ⟨h1, hk, h2⟩), if_pos (Or.inr hk)]
    · by_cases hlo : n + 1 < lo
      · rw [if_pos (Or.inl hlo), if_pos (Or.inl hlo)]
      · rw [if_neg (by tauto), if_neg (by tauto)]

lemma stepRec_of_not_active (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n)
    (ha : ¬ active lo hi k h) : stepRec lo hi k h = fun _ => (k, 0) := by
  classical
  funext ax
  unfold stepRec
  rw [if_neg]
  intro hc
  apply ha
  rcases hc with h1 | ⟨h1, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h3⟩

lemma measurable_stepRec (lo hi : ℕ) (k : Fin K) (n : ℕ) :
    Measurable (fun p : BanditHistory K n × (Fin K × ℝ) => stepRec lo hi k p.1 p.2) := by
  classical
  unfold stepRec
  apply Measurable.ite _ measurable_snd measurable_const
  have hA : MeasurableSet {p : BanditHistory K n × (Fin K × ℝ) |
      ∀ s, lo ≤ s → s ≤ n → act p.1 s ≠ some k} := by
    have : {p : BanditHistory K n × (Fin K × ℝ) | ∀ s, lo ≤ s → s ≤ n → act p.1 s ≠ some k} =
        (fun p : BanditHistory K n × (Fin K × ℝ) => actions p.1) ⁻¹'
          {a | ∀ s, lo ≤ s → s ≤ n → actA a s ≠ some k} := rfl
    rw [this]
    exact (measurable_actions.comp measurable_fst) (Set.toFinite _).measurableSet
  have hB : MeasurableSet {p : BanditHistory K n × (Fin K × ℝ) | p.2.1 ≠ k} := by
    have : {p : BanditHistory K n × (Fin K × ℝ) | p.2.1 ≠ k} =
        (fun p : BanditHistory K n × (Fin K × ℝ) => p.2.1) ⁻¹' {a | a ≠ k} := rfl
    rw [this]; exact (measurable_fst.comp measurable_snd) (Set.toFinite _).measurableSet
  have : {p : BanditHistory K n × (Fin K × ℝ) | n + 1 < lo ∨ (n + 1 ≤ hi ∧ p.2.1 ≠ k ∧
      ∀ s, lo ≤ s → s ≤ n → act p.1 s ≠ some k)} =
      {_p | n + 1 < lo} ∪ ({_p | n + 1 ≤ hi} ∩ ({p | p.2.1 ≠ k} ∩
        {p : BanditHistory K n × (Fin K × ℝ) | ∀ s, lo ≤ s → s ≤ n → act p.1 s ≠ some k})) := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
  rw [this]
  exact (MeasurableSet.const _).union ((MeasurableSet.const _).inter (hB.inter hA))

open Classical in
/-- The kernel generating the next recorded round from the record so far. -/
noncomputable def eta (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) : Kernel (BanditHistory K n) (Fin K × ℝ) :=
  Kernel.piecewise (measurableSet_active lo hi k n)
    ((banditStepKernel ν π n).map (stepMap lo k n)) (Kernel.const _ (Measure.dirac (k, 0)))

instance eta_markov (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) : IsMarkovKernel (eta ν π lo hi k n) := by
  haveI := Kernel.IsMarkovKernel.map (banditStepKernel ν π n) (measurable_stepMap lo k n)
  unfold eta; infer_instance

lemma eta_apply_active (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    {n : ℕ} (r : BanditHistory K n) (ha : active lo hi k r) :
    eta ν π lo hi k n r = (banditStepKernel ν π n r).map (stepMap lo k n) := by
  classical
  unfold eta
  rw [Kernel.piecewise_apply, if_pos (show r ∈ {r | active lo hi k r} from ha),
    Kernel.map_apply _ (measurable_stepMap lo k n)]

lemma eta_apply_not_active (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ)
    (k : Fin K) {n : ℕ} (r : BanditHistory K n) (ha : ¬ active lo hi k r) :
    eta ν π lo hi k n r = Measure.dirac (k, 0) := by
  classical
  unfold eta
  rw [Kernel.piecewise_apply, if_neg (show r ∉ {r | active lo hi k r} from ha), Kernel.const_apply]

/-- Push-forward of a composition product by a fibred map. -/
lemma compProd_map_pair {α β α' β' : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β'] (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → α') (hf : Measurable f) (g : α → β → β')
    (hg : Measurable (fun p : α × β => g p.1 p.2)) (η : Kernel α' β') [IsSFiniteKernel η]
    (hη : ∀ a, (κ a).map (g a) = η (f a)) :
    (μ ⊗ₘ κ).map (fun p => (f p.1, g p.1 p.2)) = (μ.map f) ⊗ₘ η := by
  have hm : Measurable (fun p : α × β => (f p.1, g p.1 p.2)) :=
    (hf.comp measurable_fst).prodMk hg
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left (κ := η) hs) hf]
  congr 1
  funext a
  rw [← hη a]
  have hga : Measurable (g a) := hg.comp measurable_prodMk_left
  rw [Measure.map_apply hga (measurable_prodMk_left hs)]
  rfl


/-- The law of the stopped record after `n` rounds. -/
noncomputable def recLaw (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) : Measure (BanditHistory K n) :=
  (banditMeasure ν π n).map (stopCensor lo hi k)

instance recLaw_prob (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) : IsProbabilityMeasure (recLaw ν π lo hi k n) :=
  Measure.isProbabilityMeasure_map (measurable_stopCensor lo hi k).aemeasurable

theorem rec_factor (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) :
    recLaw ν π lo hi k (n + 1) =
      ((recLaw ν π lo hi k n) ⊗ₘ eta ν π lo hi k n).map
        (fun p => (Fin.snoc (α := fun _ => Fin K × ℝ) p.1 p.2 : BanditHistory K (n + 1))) := by
  unfold recLaw
  rw [banditMeasure, Measure.map_map (measurable_stopCensor lo hi k) measurable_banditHistorySnoc]
  have hcomp : (stopCensor lo hi k) ∘ (fun p : BanditHistory K n × (Fin K × ℝ) =>
      (Fin.snoc (α := fun _ => Fin K × ℝ) p.1 p.2 : BanditHistory K (n + 1))) =
      (fun p : BanditHistory K n × (Fin K × ℝ) =>
        (Fin.snoc (α := fun _ => Fin K × ℝ) p.1 p.2 : BanditHistory K (n + 1))) ∘
      (fun p : BanditHistory K n × (Fin K × ℝ) => (stopCensor lo hi k p.1, stepRec lo hi k p.1 p.2)) := by
    funext p; exact censor_snoc lo hi k p.1 p.2
  have hpair : Measurable (fun p : BanditHistory K n × (Fin K × ℝ) =>
      (stopCensor lo hi k p.1, stepRec lo hi k p.1 p.2)) :=
    ((measurable_stopCensor lo hi k).comp measurable_fst).prodMk (measurable_stepRec lo hi k n)
  rw [hcomp, ← Measure.map_map measurable_banditHistorySnoc hpair]
  congr 1
  apply compProd_map_pair _ _ _ (measurable_stopCensor lo hi k) _ (measurable_stepRec lo hi k n)
  intro h
  by_cases ha : active lo hi k h
  · rw [eta_apply_active _ _ _ _ _ _ ((active_censor_iff lo hi k h).mpr ha),
      active_censor_eq lo hi k h ha, stepRec_of_active lo hi k h ha]
  · rw [eta_apply_not_active _ _ _ _ _ _ (fun hc => ha ((active_censor_iff lo hi k h).mp hc)),
      stepRec_of_not_active lo hi k h ha, Measure.map_const]
    simp

lemma rewardKernel_apply (ν : StochasticBandit K) (a : Fin K) :
    banditRewardKernel ν a = ν.P a := rfl

lemma step_eq (ν : StochasticBandit K) (π : BanditPolicy K) (n : ℕ) (r : BanditHistory K n) :
    banditStepKernel ν π n r = (π.select n r) ⊗ₘ banditRewardKernel ν := by
  rw [banditStepKernel, Kernel.compProd_apply_eq_compProd_sectR]
  congr 1

lemma step_ac (ν ν' : StochasticBandit K) (π : BanditPolicy K) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ)
    (r : BanditHistory K n) : banditStepKernel ν π n r ≪ banditStepKernel ν' π n r := by
  rw [step_eq, step_eq]
  apply Measure.AbsolutelyContinuous.compProd_right
  refine ae_of_all _ (fun a => ?_)
  rw [rewardKernel_apply, rewardKernel_apply]
  by_cases ha : a = k
  · subst ha; exact hac
  · rw [hdiff a ha]

lemma kl_step_kernel (ν ν' : StochasticBandit K) (π : BanditPolicy K) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ)
    (r : BanditHistory K n) :
    klDiv (banditStepKernel ν π n r) (banditStepKernel ν' π n r) =
      π.select n r {k} * klDiv (ν.P k) (ν'.P k) := by
  rw [step_eq, step_eq, klDiv_compProd_self_eq_lintegral]
  · rw [lintegral_fintype, Finset.sum_eq_single k]
    · rw [rewardKernel_apply, rewardKernel_apply, mul_comm]
    · intro b _ hb
      rw [rewardKernel_apply, rewardKernel_apply, hdiff b hb, klDiv_self]; simp
    · simp
  · intro a
    rw [rewardKernel_apply, rewardKernel_apply]
    by_cases ha : a = k
    · subst ha; exact hac
    · rw [hdiff a ha]

lemma step_map_eq (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (n : ℕ) (r : BanditHistory K n) (hlo : ¬ n + 1 < lo) :
    (banditStepKernel ν π n r).map (stepMap lo k n) =
      (banditStepKernel ν' π n r).map (stepMap lo k n) := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_stepMap lo k n) hs, Measure.map_apply (measurable_stepMap lo k n) hs,
    step_eq, step_eq, Measure.compProd_apply (measurable_stepMap lo k n hs),
    Measure.compProd_apply (measurable_stepMap lo k n hs)]
  apply lintegral_congr
  intro a
  rw [rewardKernel_apply, rewardKernel_apply]
  by_cases ha : a = k
  · subst ha
    have hset : Prod.mk a ⁻¹' (stepMap lo a n ⁻¹' s) = if (a, (0 : ℝ)) ∈ s then Set.univ else ∅ := by
      ext x
      simp only [Set.mem_preimage, stepMap, ne_eq, not_true_eq_false, or_false, if_neg hlo]
      split_ifs with h0 <;> simp [h0]
    rw [hset]
    split_ifs <;> simp
  · rw [hdiff a ha]

lemma eta_ac (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ)
    (r : BanditHistory K n) : eta ν π lo hi k n r ≪ eta ν' π lo hi k n r := by
  by_cases ha : active lo hi k r
  · rw [eta_apply_active _ _ _ _ _ r ha, eta_apply_active _ _ _ _ _ r ha]
    exact (step_ac ν ν' π k hdiff hac n r).map (measurable_stepMap lo k n)
  · rw [eta_apply_not_active _ _ _ _ _ r ha, eta_apply_not_active _ _ _ _ _ r ha]

lemma kl_eta_le (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ)
    (r : BanditHistory K n) :
    klDiv (eta ν π lo hi k n r) (eta ν' π lo hi k n r) ≤
      (if n + 1 < lo then π.select n r {k} * klDiv (ν.P k) (ν'.P k) else 0) := by
  classical
  by_cases ha : active lo hi k r
  · rw [eta_apply_active _ _ _ _ _ r ha, eta_apply_active _ _ _ _ _ r ha]
    by_cases hlo : n + 1 < lo
    · have hid : stepMap lo k n = id := by funext ax; simp [stepMap, hlo]
      rw [hid, Measure.map_id, Measure.map_id, if_pos hlo, kl_step_kernel ν ν' π k hdiff hac n r]
    · rw [step_map_eq ν ν' π lo k hdiff n r hlo, klDiv_self]; exact zero_le
  · rw [eta_apply_not_active _ _ _ _ _ r ha, eta_apply_not_active _ _ _ _ _ r ha, klDiv_self]
    exact zero_le

theorem kl_rec_step (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ) :
    klDiv (recLaw ν π lo hi k (n + 1)) (recLaw ν' π lo hi k (n + 1)) ≤
      klDiv (recLaw ν π lo hi k n) (recLaw ν' π lo hi k n) +
        (if n + 1 < lo then (∫⁻ h, π.select n h {k} ∂(banditMeasure ν π n)) *
          klDiv (ν.P k) (ν'.P k) else 0) := by
  classical
  rw [rec_factor ν, rec_factor ν']
  have h1 := klDiv_map_le (μ := recLaw ν π lo hi k n ⊗ₘ eta ν π lo hi k n)
    (ν := recLaw ν' π lo hi k n ⊗ₘ eta ν' π lo hi k n) measurable_banditHistorySnoc
  rw [klDiv_compProd_eq_add, klDiv_compProd_self_eq_lintegral _ _ _
    (eta_ac ν ν' π lo hi k hdiff hac n)] at h1
  refine h1.trans (add_le_add le_rfl ?_)
  calc ∫⁻ r, klDiv (eta ν π lo hi k n r) (eta ν' π lo hi k n r) ∂(recLaw ν π lo hi k n)
      ≤ ∫⁻ r, (if n + 1 < lo then π.select n r {k} * klDiv (ν.P k) (ν'.P k) else 0)
          ∂(recLaw ν π lo hi k n) := lintegral_mono (kl_eta_le ν ν' π lo hi k hdiff hac n)
    _ = _ := by
      by_cases hlo : n + 1 < lo
      · simp only [if_pos hlo]
        rw [lintegral_mul_const _ (Kernel.measurable_coe _ (measurableSet_singleton k))]
        have hid : stopCensor lo hi k = (id : BanditHistory K n → BanditHistory K n) := by
          funext h; exact active_censor_eq lo hi k h (Or.inl hlo)
        unfold recLaw; rw [hid, Measure.map_id]
      · simp only [if_neg hlo, lintegral_zero]

theorem kl_rec_le (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) :
    ∀ n, klDiv (recLaw ν π lo hi k n) (recLaw ν' π lo hi k n) ≤
      ∑ t ∈ Finset.range n, (if t + 1 < lo then (∫⁻ h, π.select t h {k} ∂(banditMeasure ν π t)) *
          klDiv (ν.P k) (ν'.P k) else 0) := by
  intro n
  induction n with
  | zero =>
    have : recLaw ν π lo hi k 0 = recLaw ν' π lo hi k 0 := by
      unfold recLaw; rfl
    rw [this, klDiv_self]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    refine (kl_rec_step ν ν' π lo hi k hdiff hac n).trans ?_
    gcongr


/-- Summed over the arm `k`, the divergence of the stopped records under `0` and `Δ e_k` is at
most `lo · Δ²/2`. -/
theorem sum_kl_gauss_le (π : BanditPolicy K) (T lo hi : ℕ) (Δ : ℝ) :
    ∑ k : Fin K, klDiv (recLaw (gaussianBandit (0 : Fin K → ℝ)) π lo hi k T)
        (recLaw (gaussianBandit (Function.update (0 : Fin K → ℝ) k Δ)) π lo hi k T) ≤
      ENNReal.ofReal ((lo : ℝ) * (Δ ^ 2 / 2)) := by
  classical
  set D : ℝ≥0∞ := ENNReal.ofReal (Δ ^ 2 / 2) with hD
  have hDk : ∀ k : Fin K, klDiv ((gaussianBandit (0 : Fin K → ℝ)).P k)
      ((gaussianBandit (Function.update (0 : Fin K → ℝ) k Δ)).P k) = D := by
    intro k
    simp only [gaussianBandit, Pi.zero_apply, Function.update_self]
    rw [BanditAlgorithm.klDiv_gaussianReal_same_variance one_ne_zero]
    rw [hD]; congr 1; push_cast; ring
  have hkl : ∀ k : Fin K, klDiv (recLaw (gaussianBandit (0 : Fin K → ℝ)) π lo hi k T)
      (recLaw (gaussianBandit (Function.update (0 : Fin K → ℝ) k Δ)) π lo hi k T) ≤
      ∑ t ∈ Finset.range T, (if t + 1 < lo then
        (∫⁻ h, π.select t h {k} ∂(banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π t)) * D
        else 0) := by
    intro k
    have := kl_rec_le (gaussianBandit (0 : Fin K → ℝ))
      (gaussianBandit (Function.update (0 : Fin K → ℝ) k Δ)) π lo hi k
      (fun i hi => by simp [gaussianBandit, Function.update_of_ne hi])
      (by
        simp only [gaussianBandit, Pi.zero_apply, Function.update_self]
        exact (gaussianReal_absolutelyContinuous 0 one_ne_zero).trans
          (gaussianReal_absolutelyContinuous' Δ one_ne_zero)) T
    rw [hDk] at this
    exact this
  calc ∑ k : Fin K, klDiv (recLaw (gaussianBandit (0 : Fin K → ℝ)) π lo hi k T)
        (recLaw (gaussianBandit (Function.update (0 : Fin K → ℝ) k Δ)) π lo hi k T)
      ≤ ∑ k : Fin K, ∑ t ∈ Finset.range T, (if t + 1 < lo then
        (∫⁻ h, π.select t h {k} ∂(banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π t)) * D
        else 0) := Finset.sum_le_sum (fun k _ => hkl k)
    _ = ∑ t ∈ Finset.range T, (if t + 1 < lo then D else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        split_ifs with ht
        · rw [← Finset.sum_mul, ← lintegral_finset_sum _
            (fun k _ => Kernel.measurable_coe _ (measurableSet_singleton k))]
          have : ∀ h, ∑ k : Fin K, π.select t h {k} = 1 := by
            intro h
            rw [sum_measure_singleton]; simp
          simp [this]
        · simp
    _ ≤ ∑ t ∈ Finset.range lo, D := by
        calc ∑ t ∈ Finset.range T, (if t + 1 < lo then D else 0)
            = ∑ t ∈ (Finset.range T).filter (fun t => t + 1 < lo), D := by
              rw [Finset.sum_filter]
          _ ≤ ∑ t ∈ Finset.range lo, D := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro t ht
                simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢; omega
              · intros; exact zero_le
    _ = ENNReal.ofReal ((lo : ℝ) * (Δ ^ 2 / 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hD,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end BwSC.LowerBound.KLAux

namespace BwSC.LowerBound.KLAux

lemma tsq_bound (m n t : ℝ) (hm : 0 ≤ m) (hn : 0 < n) (ht : 0 ≤ t) :
    t * ((1 / (2 * n) * Real.sqrt (m / t)) ^ 2 / 2) ≤ m / (8 * n ^ 2) := by
  rw [mul_pow, Real.sq_sqrt (div_nonneg hm ht)]
  rcases ht.lt_or_eq with htp | ht0
  · apply le_of_eq; field_simp; ring
  · rw [← ht0]; simp; positivity

end BwSC.LowerBound.KLAux

open BwSC.LowerBound BwSC.LowerBound.KLAux in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (hq : 1 ≤ qIdx S K) :
    ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K, klDiv (artQ1 π S T j k) (artP1 π S T j k) ≤
        ENNReal.ofReal (((K : ℝ) - (rIdx S K : ℝ)) / (8 * ((qIdx S K : ℝ) + 2))) ∧
    ENNReal.ofReal (1 / (((qIdx S K : ℝ) + 2) * K)) *
        ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
          klDiv (artQ1 π S T j k) (artP1 π S T j k) ≤
        ENNReal.ofReal (((K : ℝ) - (rIdx S K : ℝ)) / (8 * ((qIdx S K : ℝ) + 2) ^ 2 * K)) ∧
    ((K : ℝ) - (rIdx S K : ℝ)) / (8 * ((qIdx S K : ℝ) + 2) ^ 2 * K) ≤
      qbar1 π S T / 4 := by
  set q := qIdx S K with hqdef
  set n : ℝ := (q : ℝ) + 2 with hn
  set m : ℝ := (K : ℝ) - (rIdx S K : ℝ) with hm
  have hn0 : 0 < n := by positivity
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hm0 : 0 ≤ m := by
    have h1 : rIdx S K ≤ (K : ℤ) - 2 := by
      unfold rIdx qIdx
      by_cases hS : S = 0
      · subst hS; simp; omega
      · rw [if_neg hS]
        have hdm := Nat.div_add_mod (S - 1) (K - 1)
        have hlt := Nat.mod_lt (S - 1) (by omega : K - 1 > 0)
        have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
        have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
        have e : (S : ℤ) - 1 - (((S - 1) / (K - 1) : ℕ) : ℤ) * ((K : ℤ) - 1) =
            (((S - 1) % (K - 1) : ℕ) : ℤ) := by
          rw [← hS1, ← hK1]; push_cast; zify at hdm; linarith
        rw [e]
        zify at hlt; push_cast at hlt ⊢; omega
    have : (rIdx S K : ℝ) ≤ (K : ℝ) - 2 := by exact_mod_cast h1
    rw [hm]; linarith
  -- per-window bound
  have hj : ∀ j ∈ Finset.Icc 1 (q + 2),
      ∑ k : Fin K, klDiv (artQ1 π S T j k) (artP1 π S T j k) ≤ ENNReal.ofReal (m / (8 * n ^ 2)) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have h1 := sum_kl_gauss_le π T (lo1 S K T j) (hi1 S K T j) (Δ1 S K T j)
    refine le_trans ?_ (h1.trans (ENNReal.ofReal_le_ofReal ?_))
    · exact le_of_eq rfl
    · by_cases hj1' : j = 1
      · have : lo1 S K T j = 0 := by
          unfold lo1; rw [if_neg (by omega), hj1']; simp [t1]
        rw [this]; simp; positivity
      · by_cases hjq : q + 1 ≤ j
        · have hlo : lo1 S K T j = t1 S K T q := by unfold lo1; rw [if_pos hjq]
          have hΔsq : (Δ1 S K T j) ^ 2 = (1 / (2 * n) * Real.sqrt (m / (t1 S K T q : ℝ))) ^ 2 := by
            unfold Δ1
            rw [if_neg hj1']
            split_ifs with hjl
            · rw [neg_sq]
            · rw [show j - 1 = q by omega]
          rw [hlo, hΔsq]
          exact tsq_bound m n _ hm0 hn0 (Nat.cast_nonneg _)
        · have hlo : lo1 S K T j = t1 S K T (j - 1) := by unfold lo1; rw [if_neg hjq]
          have hΔsq : (Δ1 S K T j) ^ 2 =
              (1 / (2 * n) * Real.sqrt (m / (t1 S K T (j - 1) : ℝ))) ^ 2 := by
            unfold Δ1
            rw [if_neg hj1', if_neg (by omega)]
          rw [hlo, hΔsq]
          exact tsq_bound m n _ hm0 hn0 (Nat.cast_nonneg _)
  have hsum : ∑ j ∈ Finset.Icc 1 (q + 2), ∑ k : Fin K, klDiv (artQ1 π S T j k) (artP1 π S T j k) ≤
      ENNReal.ofReal (m / (8 * n)) := by
    calc ∑ j ∈ Finset.Icc 1 (q + 2), ∑ k : Fin K, klDiv (artQ1 π S T j k) (artP1 π S T j k)
        ≤ ∑ j ∈ Finset.Icc 1 (q + 2), ENNReal.ofReal (m / (8 * n ^ 2)) := Finset.sum_le_sum hj
      _ = ENNReal.ofReal (m / (8 * n)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        rw [show q + 2 + 1 - 1 = q + 2 by omega]; push_cast
        rw [← hn]; field_simp
  refine ⟨hsum, ?_, ?_⟩
  · calc ENNReal.ofReal (1 / (n * K)) * ∑ j ∈ Finset.Icc 1 (q + 2), ∑ k : Fin K,
          klDiv (artQ1 π S T j k) (artP1 π S T j k)
        ≤ ENNReal.ofReal (1 / (n * K)) * ENNReal.ofReal (m / (8 * n)) := by gcongr
      _ = ENNReal.ofReal (m / (8 * n ^ 2 * K)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
  · obtain ⟨C1, _⟩ := corollary_4 hK hT π hπ (0 : Fin K → ℝ)
    have : qbar1 π S T = 1 / (((qIdx S K : ℝ) + 2) * K) *
        ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
          ((banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E1 S K T j k)).toReal := rfl
    rw [this]
    have e : m / (8 * n ^ 2 * K) = (m / (2 * n ^ 2 * K)) / 4 := by field_simp; ring
    rw [e]
    linarith
