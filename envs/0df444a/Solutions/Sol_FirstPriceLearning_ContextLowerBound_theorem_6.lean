-- Prove2me | solution 1 for FirstPriceLearning.ContextLowerBound.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:04:39.044995+00:00
-- url     : https://prove2.me/submissions/d38f6314-79db-48aa-9036-a445ac11aeae

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction
import Theorems.Thm_FirstPriceLearning_ContextLowerBound_construction_is_pocb
import Theorems.Thm_FirstPriceLearning_ContextLowerBound_conclusion

open MeasureTheory
open FirstPriceLearning.ContextLowerBound

namespace CLBT6

variable {M α : ℕ}

/-- The relabelling of `Fin ((α+1)*M)` as the action set `Act M α`. -/
def eqv (M α : ℕ) : Fin ((α + 1) * M) ≃ Act M α :=
  (finCongr (Nat.mul_comm _ _)).trans finProdFinEquiv.symm

/-- reindex a reward vector. -/
def sig (M α : ℕ) (x : Fin M → Act M α → ℝ) : Fin M → Fin ((α + 1) * M) → ℝ :=
  fun c a => x c (eqv M α a)

def sigInv (M α : ℕ) (y : Fin M → Fin ((α + 1) * M) → ℝ) : Fin M → Act M α → ℝ :=
  fun c a => y c ((eqv M α).symm a)

lemma measurable_sig : Measurable (sig M α) := by
  unfold sig; fun_prop

lemma measurable_sigInv : Measurable (sigInv M α) := by
  unfold sigInv; fun_prop

def sigE (M α : ℕ) : (Fin M → Act M α → ℝ) ≃ᵐ (Fin M → Fin ((α + 1) * M) → ℝ) where
  toFun := sig M α
  invFun := sigInv M α
  left_inv x := by funext c a; simp [sig, sigInv]
  right_inv y := by funext c a; simp [sig, sigInv]
  measurable_toFun := measurable_sig
  measurable_invFun := measurable_sigInv

def obsMap (M α t : ℕ) (o : Fin t → Fin M → Act M α → ℝ) : Fin t → Fin M → Fin ((α + 1) * M) → ℝ :=
  fun i => sig M α (o i)

lemma measurable_obsMap (t : ℕ) : Measurable (obsMap M α t) := by
  unfold obsMap sig; fun_prop

def Epull (M α : ℕ) (a b : Fin ((α + 1) * M)) : Prop :=
  feedbackGraph M α (eqv M α a) (eqv M α b)

noncomputable def lawPull (M α T : ℕ) (u : Fin M → Fin (α + 1)) : Measure (Fin M → Fin ((α + 1) * M) → ℝ) :=
  (hardLaw M α T u).map (sig M α)

/-- The transported policy. -/
noncomputable def polPush {U : Type} [MeasurableSpace U] (π : Policy M (Fin ((α + 1) * M)) U) :
    Policy M (Act M α) U where
  act t u ctx obs := eqv M α (π.act t u ctx (obsMap M α t obs))
  measurable_act t := by
    have h1 := π.measurable_act t
    have h2 : Measurable (fun p : U × (Fin (t + 1) → Fin M) × (Fin t → Fin M → Act M α → ℝ) =>
        (p.1, p.2.1, obsMap M α t p.2.2)) := by
      refine Measurable.prodMk measurable_fst (Measurable.prodMk ?_ ?_)
      · exact measurable_fst.comp measurable_snd
      · exact (measurable_obsMap t).comp (measurable_snd.comp measurable_snd)
    have h3 : Measurable (eqv M α) := measurable_of_countable _
    exact h3.comp (h1.comp h2)

lemma reveal_sig (a : Fin ((α + 1) * M)) (x : Fin M → Act M α → ℝ) :
    reveal (Epull M α) a (sig M α x) = sig M α (reveal (feedbackGraph M α) (eqv M α a) x) := by
  funext c b
  simp only [reveal, sig, FirstPriceLearning.GraphFeedback.Revealed, Epull]
  congr 1
  apply propext
  simp [(eqv M α).injective.eq_iff]

lemma obs_transport {U : Type} [MeasurableSpace U] (π : Policy M (Fin ((α + 1) * M)) U)
    {T : ℕ} (c : Fin T → Fin M) (u : U) (r : Fin T → Fin M → Act M α → ℝ) :
    ∀ (t : ℕ) (h : t ≤ T),
      observations (Epull M α) π c u (fun s => sig M α (r s)) t h =
        obsMap M α t (observations (feedbackGraph M α) (polPush π) c u r t h) := by
  intro t
  induction t with
  | zero => intro h; funext i; exact i.elim0
  | succ t ih =>
    intro h
    simp only [observations]
    rw [ih (Nat.le_of_succ_le h)]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, obsMap]
      rw [reveal_sig]
      rfl
    · simp only [Fin.snoc_castSucc, obsMap]

lemma action_transport {U : Type} [MeasurableSpace U] (π : Policy M (Fin ((α + 1) * M)) U)
    {T : ℕ} (c : Fin T → Fin M) (u : U) (r : Fin T → Fin M → Act M α → ℝ) (t : Fin T) :
    eqv M α (action (Epull M α) π c u (fun s => sig M α (r s)) t) =
      action (feedbackGraph M α) (polPush π) c u r t := by
  simp only [action]
  rw [obs_transport]
  rfl

lemma meanReward_pull (T : ℕ) (u : Fin M → Fin (α + 1)) (c : Fin M) (a : Fin ((α + 1) * M)) :
    meanReward (lawPull M α T u) c a = meanReward (hardLaw M α T u) c (eqv M α a) := by
  unfold meanReward lawPull
  rw [show (hardLaw M α T u).map (sig M α) = (hardLaw M α T u).map (sigE M α) from rfl,
    integral_map_equiv]
  rfl

lemma optReward_pull (T : ℕ) (u : Fin M → Fin (α + 1)) (c : Fin M) :
    optReward (lawPull M α T u) c = optReward (hardLaw M α T u) c := by
  unfold optReward
  simp_rw [meanReward_pull]
  exact (eqv M α).iSup_comp (g := fun a => meanReward (hardLaw M α T u) c a)

lemma regret_pull (T : ℕ) (u : Fin M → Fin (α + 1)) (c : Fin T → Fin M)
    (a : Fin T → Fin ((α + 1) * M)) :
    regret (lawPull M α T u) c a = regret (hardLaw M α T u) c (fun t => eqv M α (a t)) := by
  unfold regret
  simp_rw [optReward_pull, meanReward_pull]

def bigE (M α T : ℕ) {U : Type} [MeasurableSpace U] :
    (U × (Fin T → Fin M → Act M α → ℝ)) ≃ᵐ (U × (Fin T → Fin M → Fin ((α + 1) * M) → ℝ)) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl U)
    (MeasurableEquiv.piCongrRight (fun _ => sigE M α))

lemma interactionLaw_pull (T : ℕ) {U : Type} [MeasurableSpace U] (μU : Measure U)
    [IsProbabilityMeasure μU] (u : Fin M → Fin (α + 1))
    [IsProbabilityMeasure (hardLaw M α T u)] :
    interactionLaw μU (lawPull M α T u) T =
      (interactionLaw μU (hardLaw M α T u) T).map (bigE M α T) := by
  unfold interactionLaw lawPull
  have h1 : (Measure.pi fun _ : Fin T => (hardLaw M α T u).map (sig M α)) =
      (Measure.pi fun _ : Fin T => hardLaw M α T u).map (fun x i => sig M α (x i)) :=
    (Measure.pi_map_pi (fun _ => measurable_sig.aemeasurable)).symm
  rw [h1]
  have h2 : μU = μU.map id := Measure.map_id.symm
  conv_lhs => rw [h2]
  have hm : Measurable (fun (x : Fin T → Fin M → Act M α → ℝ) (i : Fin T) => sig M α (x i)) :=
    measurable_pi_lambda _ (fun i => measurable_sig.comp (measurable_pi_apply i))
  rw [Measure.map_prod_map _ _ measurable_id hm]
  rfl

lemma expectedRegret_pull (T : ℕ) {U : Type} [MeasurableSpace U] (μU : Measure U)
    [IsProbabilityMeasure μU] (π : Policy M (Fin ((α + 1) * M)) U) (u : Fin M → Fin (α + 1))
    [IsProbabilityMeasure (hardLaw M α T u)] (c : Fin T → Fin M) :
    expectedRegret (Epull M α) (lawPull M α T u) μU π c =
      expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU (polPush π) c := by
  unfold expectedRegret
  rw [interactionLaw_pull, integral_map_equiv]
  congr 1
  funext ω
  rw [regret_pull]
  congr 1
  funext t
  exact action_transport π c ω.1 ω.2 t

end CLBT6

open CLBT6 in
theorem solution (α M T : ℕ) (hα : 1 ≤ α) (hM : 1 ≤ M) (hK : ((α + 1) * M) ^ 3 ≤ T)
    (hMT : M ∣ T) :
    ∃ E : Fin ((α + 1) * M) → Fin ((α + 1) * M) → Prop,
      (∀ a, ¬ E a a) ∧ (∀ a b d, E a b → E b d → E a d) ∧ HasIndependenceNumber E α ∧
      ∀ (U : Type) [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
        (π : Policy M (Fin ((α + 1) * M)) U),
        ∃ P : Measure (Fin M → Fin ((α + 1) * M) → ℝ),
          IsPartiallyOrderedContextualBandit E P (fun c₁ c₂ : Fin M => c₁ ≤ c₂) ∧
          HasOrderIndependenceNumber (fun c₁ c₂ : Fin M => c₁ ≤ c₂) 1 ∧
          ∃ c : Fin T → Fin M,
            Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / (32 * Real.exp 3) ≤
              expectedRegret E P μU π c := by
  have hKT : (α + 1) * M ≤ T := by
    have h1 : 1 ≤ (α + 1) * M := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc (α + 1) * M = ((α + 1) * M) ^ 1 := (pow_one _).symm
      _ ≤ ((α + 1) * M) ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
      _ ≤ T := hK
  have hM0 : 0 < M := hM
  have hC := construction_is_pocb M α T hα hM hKT (fun _ => 0)
  obtain ⟨⟨⟨_, _, hloop⟩, htrans, _, _⟩, ⟨⟨S0, hS0, hS0c⟩, hSle⟩, _⟩ := hC
  refine ⟨Epull M α, fun a => hloop _, fun a b d h1 h2 => htrans _ _ _ h1 h2, ?_, ?_⟩
  · refine ⟨⟨S0.map (eqv M α).symm.toEmbedding, ?_, by simp [hS0c]⟩, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.mem_map_equiv, Equiv.symm_symm] at ha hb
      simp only [Epull]
      exact hS0 _ ha _ hb (fun h => hab ((eqv M α).injective h))
    · intro S hS
      have := hSle (S.map (eqv M α).toEmbedding) (by
        intro a ha b hb hab
        simp only [Finset.mem_map_equiv] at ha hb
        have h := hS _ ha _ hb (fun h => hab (by simpa using congrArg (eqv M α) h))
        simpa [Epull] using h)
      simpa using this
  · intro U _ μU _ π
    obtain ⟨u, hu⟩ := exists_eq_ciSup_of_finite
      (f := fun u : Fin M → Fin (α + 1) =>
        expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU (polPush π) (blockContext M T hM0))
    obtain ⟨⟨⟨hprob, hsupp, hloop'⟩, htrans', hpo, astar, hastar, hmono⟩, _, hord⟩ :=
      construction_is_pocb M α T hα hM hKT u
    refine ⟨lawPull M α T u, ⟨⟨?_, ?_, fun a => hloop' _⟩, fun a b d h1 h2 => htrans' _ _ _ h1 h2,
      hpo, fun c => (eqv M α).symm (astar c), ?_, ?_⟩, hord, blockContext M T hM0, ?_⟩
    · exact Measure.isProbabilityMeasure_map measurable_sig.aemeasurable
    · rw [show lawPull M α T u = (hardLaw M α T u).map (sigE M α) from rfl,
        (sigE M α).map_apply]
      refine measure_mono_null ?_ hsupp
      intro x hx
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq] at hx ⊢
      intro hall
      exact hx (fun c a => hall c _)
    · intro c a
      rw [meanReward_pull, meanReward_pull, Equiv.apply_symm_apply]
      exact hastar c _
    · intro c₁ c₂ h
      rcases hmono c₁ c₂ h with h | h
      · left; simp only [h]
      · right; simpa [Epull] using h
    · have hconc := conclusion M α T hα hM0 hK hMT μU (polPush π)
      rw [expectedRegret_pull]
      unfold maxRegret at hconc
      rw [← hu] at hconc
      exact hconc
