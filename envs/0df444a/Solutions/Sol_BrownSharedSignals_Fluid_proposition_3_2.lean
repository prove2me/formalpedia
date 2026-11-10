-- Prove2me | solution 1 for BrownSharedSignals.Fluid.proposition_3_2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:43:18.457967+00:00
-- url     : https://prove2.me/submissions/2cdb3417-bf48-4d40-a855-4bfb3b3bea3a

import Mathlib
import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open Classical
noncomputable section

namespace BrownSharedSignals.Fluid

abbrev ceStateDist : Arlib.Probability.FinDist (Fin 2) where
  p := fun s => if s = 0 then 1 else 0
  p_nonneg := fun s => by split_ifs <;> norm_num
  p_sum := by simp

abbrev ceSignalDist : Arlib.Probability.FinDist (Fin 1) where
  p := fun _ => 1
  p_nonneg := fun _ => by norm_num
  p_sum := by simp

abbrev ceProject : ControlledProcess (Fin 2) (Fin 1) where
  actions := fun _ s _ => if s = 0 then {0} else {0, 1}
  zero_mem := fun _ s _ => by split_ifs <;> simp
  action_nonneg := fun _ s _ a ha => by
    split_ifs at ha
    · simp only [Finset.mem_singleton] at ha
      linarith
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> norm_num
  reward := fun _ s _ a => if s = 1 ∧ a = 1 then 1 else 0
  transition := fun _ _ _ _ => ceStateDist

abbrev ceModel : Model 1 1 where
  horizon_pos := Nat.zero_lt_one
  stateSize := fun _ => 1
  signalSize := 0
  project := fun _ => ceProject
  signal := fun _ _ => ceSignalDist
  consumption := fun _ _ _ _ a => a
  consumption_zero := fun _ _ _ _ => rfl
  consumption_pos := fun t i s z a ha hne => by
    dsimp [ceProject] at ha
    split_ifs at ha
    · simp only [Finset.mem_singleton] at ha
      exact False.elim (hne ha)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact False.elim (hne rfl)
      · norm_num
  budget := fun _ _ => 1
  budget_nonneg := fun _ _ => by norm_num
  initialState := fun _ => 0
  initialSignal := 0

def zeroAction (t : ℕ) (i : Fin 1) (s : Fin 2) (z : Fin 1) : Action ceModel t i s z :=
  ⟨0, ceProject.zero_mem t s z⟩

lemma action_state_zero_eq (t : ℕ) (i : Fin 1) (z : Fin 1)
    (a : Action ceModel t i 0 z) : a = zeroAction t i 0 z := by
  ext
  have ha := a.property
  dsimp [ceModel, ceProject] at ha
  exact Finset.mem_singleton.mp ha

lemma action_state_one_cases (t : ℕ) (i : Fin 1) (z : Fin 1)
    (a : Action ceModel t i 1 z) :
    a.val = 0 ∨ a.val = 1 := by
  have ha := a.property
  change a.val ∈ (if (1 : Fin 2) = 0 then ({0} : Finset ℝ) else {0, 1}) at ha
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  rw [if_neg h1] at ha
  simpa using ha

lemma sum_action_zero_indicator (t : ℕ) (i : Fin 1) (s : Fin 2) (z : Fin 1) :
    ∑ a : Action ceModel t i s z, (if a.val = 0 then (1 : ℝ) else 0) = 1 := by
  have hmem : zeroAction t i s z ∈ (Finset.univ : Finset (Action ceModel t i s z)) :=
    Finset.mem_univ _
  rw [Finset.sum_eq_single (zeroAction t i s z)]
  · change (if (0 : ℝ) = 0 then (1 : ℝ) else 0) = 1
    simp
  · intro b _ hb
    have hval : b.val ≠ 0 := by
      intro hv
      apply hb
      ext
      exact hv
    rw [if_neg hval]
  · intro h
    exact False.elim (h hmem)

def ceLocalPolicy : LocalPolicy ceModel :=
  fun t h i s =>
    { p := fun a => if a.val = 0 then 1 else 0
      p_nonneg := fun a => by split_ifs <;> norm_num
      p_sum := sum_action_zero_indicator t i s (current ceModel h) }

lemma ceLocalPolicy_is_occupancy {μ : Occupancy ceModel} (hμ : LP7Optimal ceModel μ) :
    OccupancyPolicy ceModel μ ceLocalPolicy := by
  intro t ht h i s hpos a
  have ht0 : t = 0 := Nat.lt_one_iff.mp ht
  subst ht0
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl
  · have ha : a = zeroAction 0 0 0 (current ceModel h) :=
      action_state_zero_eq 0 0 (current ceModel h) a
    subst ha
    have hmass : occupancyMass ceModel μ 0 h 0 0 =
        μ 0 h 0 0 (zeroAction 0 0 0 (current ceModel h)) := by
      unfold occupancyMass
      rw [Finset.sum_eq_single (zeroAction 0 0 0 (current ceModel h))]
      · intro b _ hb
        exact False.elim (hb (action_state_zero_eq 0 0 (current ceModel h) b))
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    rw [hmass] at hpos ⊢
    change (if (0 : ℝ) = 0 then (1 : ℝ) else 0) = _
    rw [if_pos rfl, div_self (ne_of_gt hpos)]
  · have hmass0 : occupancyMass ceModel μ 0 h 0 1 = 0 := by
      have h3 := hμ.1.2.2.1 h 0 1
      have hne : ¬ (h 0 = ceModel.initialSignal ∧ (1 : Fin 2) = ceModel.initialState 0) := by
        rintro ⟨_, h10⟩
        revert h10
        decide
      rw [if_neg hne] at h3
      exact h3
    rw [hmass0] at hpos
    exact False.elim (lt_irrefl 0 hpos)

def witnessLam : Multiplier ceModel := fun _ _ => 0

def witnessEll : ProjectCoordinates ceModel :=
  fun t _ _ s => if t = 0 ∧ s = 1 then 1 else 0

lemma witness_LP6Feasible : LP6Feasible ceModel witnessLam witnessEll := by
  refine ⟨?_, ?_, ?_⟩
  · intro t _ h
    dsimp [witnessLam]
    exact le_rfl
  · intro h i s
    simp [witnessEll]
  · intro t ht h i s a
    have ht0 : t = 0 := Nat.lt_one_iff.mp ht
    subst ht0
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    unfold localActionValue
    have hnext : (∑ z', ∑ s', ceModel.signal 0 (current ceModel h) z' *
        (ceModel.project 0).transition 0 s (current ceModel h) a.val s' *
        witnessEll (0 + 1) (Fin.snoc h z') 0 s') = 0 := by
      apply Finset.sum_eq_zero
      intro z' _
      apply Finset.sum_eq_zero
      intro s' _
      dsimp [witnessEll]
      simp
    rw [hnext, add_zero]
    dsimp [witnessLam, witnessEll, ceModel, ceProject]
    rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl
    · have h01 : (0 : Fin 2) ≠ 1 := by decide
      simp [h01]
    · rcases action_state_one_cases 0 0 (current ceModel h) a with ha0 | ha1
      · rw [ha0]
        norm_num
      · rw [ha1]
        norm_num

lemma penalty_ce (lam : Multiplier ceModel) :
    penalty ceModel lam 0 (initialHistory ceModel) = lam 0 (initialHistory ceModel) := by
  change lam 0 (initialHistory ceModel) * 1 +
    ∑ z' : Fin 1, (1 : ℝ) * 0 = lam 0 (initialHistory ceModel)
  simp

lemma witness_LP6Objective : LP6Objective ceModel witnessLam witnessEll = 0 := by
  unfold LP6Objective
  rw [penalty_ce, Fin.sum_univ_one]
  dsimp [witnessLam, witnessEll, ceModel]
  simp

lemma lam_zero_of_LP6Optimal {lam : Multiplier ceModel} {ℓ : ProjectCoordinates ceModel}
    (hopt : LP6Optimal ceModel lam ℓ) :
    lam 0 (initialHistory ceModel) = 0 := by
  have hle : LP6Objective ceModel lam ℓ ≤ 0 := by
    rw [← witness_LP6Objective]
    exact hopt.2 witnessLam witnessEll witness_LP6Feasible
  have hlam_nonneg : 0 ≤ lam 0 (initialHistory ceModel) :=
    hopt.1.1 0 Nat.zero_lt_one (initialHistory ceModel)
  have hell_nonneg : 0 ≤ ℓ 0 (initialHistory ceModel) 0 0 := by
    have h1 := hopt.1.2.2 0 Nat.zero_lt_one (initialHistory ceModel) 0 0
      (zeroAction 0 0 0 (current ceModel (initialHistory ceModel)))
    unfold localActionValue at h1
    have hnext : (∑ z', ∑ s', ceModel.signal 0 (current ceModel (initialHistory ceModel)) z' *
        (ceModel.project 0).transition 0 0 (current ceModel (initialHistory ceModel)) 0 s' *
        ℓ (0 + 1) (Fin.snoc (initialHistory ceModel) z') 0 s') = 0 := by
      apply Finset.sum_eq_zero
      intro z' _
      apply Finset.sum_eq_zero
      intro s' _
      rw [hopt.1.2.1 (Fin.snoc (initialHistory ceModel) z') 0 s', mul_zero]
    change (ceModel.project 0).reward 0 0 (current ceModel (initialHistory ceModel)) 0 -
      lam 0 (initialHistory ceModel) *
        ceModel.consumption 0 0 0 (current ceModel (initialHistory ceModel)) 0 +
      (∑ z', ∑ s', ceModel.signal 0 (current ceModel (initialHistory ceModel)) z' *
        (ceModel.project 0).transition 0 0 (current ceModel (initialHistory ceModel)) 0 s' *
        ℓ (0 + 1) (Fin.snoc (initialHistory ceModel) z') 0 s') ≤
      ℓ 0 (initialHistory ceModel) 0 0 at h1
    rw [hnext] at h1
    dsimp [ceModel, ceProject] at h1
    norm_num at h1
    exact h1
  unfold LP6Objective at hle
  rw [penalty_ce, Fin.sum_univ_one] at hle
  change lam 0 (initialHistory ceModel) + ℓ 0 (initialHistory ceModel) 0 0 ≤ 0 at hle
  linarith

def oneAction : Action ceModel 0 0 1 (current ceModel (initialHistory ceModel)) :=
  ⟨1, by dsimp [ceModel, ceProject]; simp⟩

lemma localActionValue_zero_eq {lam : Multiplier ceModel}
    (hlam : lam 0 (initialHistory ceModel) = 0)
    (a : Action ceModel 0 0 1 (current ceModel (initialHistory ceModel))) :
    localActionValue ceModel lam (projectValue ceModel lam) 0 (initialHistory ceModel) 0 1 a =
      if a.val = 1 then 1 else 0 := by
  unfold localActionValue
  have hnext : (∑ z', ∑ s', ceModel.signal 0 (current ceModel (initialHistory ceModel)) z' *
      (ceModel.project 0).transition 0 1 (current ceModel (initialHistory ceModel)) a.val s' *
      projectValue ceModel lam (0 + 1) (Fin.snoc (initialHistory ceModel) z') 0 s') = 0 := by
    apply Finset.sum_eq_zero
    intro z' _
    apply Finset.sum_eq_zero
    intro s' _
    change _ * projectAux ceModel lam 0 0 1 (Fin.snoc (initialHistory ceModel) z') s' = 0
    unfold projectAux
    rw [mul_zero]
  rw [hnext, hlam, zero_mul, sub_zero, add_zero]
  dsimp [ceModel, ceProject]
  simp

end BrownSharedSignals.Fluid

theorem solution : ¬ (∀ {N T : ℕ} (M : BrownSharedSignals.Fluid.Model N T),
    (∃ lam ℓ, BrownSharedSignals.Fluid.LP6Optimal M lam ℓ) ∧
    (∃ μ, BrownSharedSignals.Fluid.LP7Optimal M μ) ∧
    BrownSharedSignals.Fluid.LP6Value M = BrownSharedSignals.Fluid.LP7Value M ∧
    BrownSharedSignals.Fluid.LP6Value M = BrownSharedSignals.Fluid.optimalRelaxation M ∧
    ∀ lam ℓ μ, BrownSharedSignals.Fluid.LP6Optimal M lam ℓ →
    BrownSharedSignals.Fluid.LP7Optimal M μ →
    ∀ p : BrownSharedSignals.Fluid.LocalPolicy M,
    BrownSharedSignals.Fluid.OccupancyPolicy M μ p →
      BrownSharedSignals.Fluid.penalizedPolicyAux M lam (BrownSharedSignals.Fluid.independentPolicy M p)
        T 0 (BrownSharedSignals.Fluid.initialHistory M) M.initialState =
        BrownSharedSignals.Fluid.lagrangian M lam 0 (BrownSharedSignals.Fluid.initialHistory M) M.initialState ∧
      (∀ t < T, ∀ h i s (a : BrownSharedSignals.Fluid.Action M t i s (BrownSharedSignals.Fluid.current M h)),
        ((∀ b : BrownSharedSignals.Fluid.Action M t i s (BrownSharedSignals.Fluid.current M h), b ≠ a →
            BrownSharedSignals.Fluid.localActionValue M lam (BrownSharedSignals.Fluid.projectValue M lam) t h i s b <
            BrownSharedSignals.Fluid.localActionValue M lam (BrownSharedSignals.Fluid.projectValue M lam) t h i s a) →
          p t h i s a = 1) ∧
        (BrownSharedSignals.Fluid.localActionValue M lam (BrownSharedSignals.Fluid.projectValue M lam) t h i s a <
            BrownSharedSignals.Fluid.projectValue M lam t h i s →
          p t h i s a = 0)) ∧
      (∀ t < T, ∀ h, h 0 = M.initialSignal →
        let C := BrownSharedSignals.Fluid.conditionalActionExpectation M
          (BrownSharedSignals.Fluid.independentPolicy M p) t h
          (fun s a => BrownSharedSignals.Fluid.consumption M t s (BrownSharedSignals.Fluid.current M h)
            (BrownSharedSignals.Fluid.actionVector M a))
        C ≤ M.budget t (BrownSharedSignals.Fluid.current M h) ∧ 0 ≤ lam t h ∧
          lam t h * (M.budget t (BrownSharedSignals.Fluid.current M h) - C) = 0)) := by
  intro hall
  rcases hall BrownSharedSignals.Fluid.ceModel with
    ⟨⟨lam, ℓ, hLP6⟩, ⟨μ, hLP7⟩, _, _, hmain⟩
  have hp := BrownSharedSignals.Fluid.ceLocalPolicy_is_occupancy hLP7
  have hclaim := (hmain lam ℓ μ hLP6 hLP7 BrownSharedSignals.Fluid.ceLocalPolicy hp).2.1
    0 Nat.zero_lt_one (BrownSharedSignals.Fluid.initialHistory BrownSharedSignals.Fluid.ceModel)
    0 1 BrownSharedSignals.Fluid.oneAction
  have hlam0 := BrownSharedSignals.Fluid.lam_zero_of_LP6Optimal hLP6
  have hp1 : BrownSharedSignals.Fluid.ceLocalPolicy 0
      (BrownSharedSignals.Fluid.initialHistory BrownSharedSignals.Fluid.ceModel)
      0 1 BrownSharedSignals.Fluid.oneAction = 1 := by
    apply hclaim.1
    intro b hb
    rw [BrownSharedSignals.Fluid.localActionValue_zero_eq hlam0 b,
      BrownSharedSignals.Fluid.localActionValue_zero_eq hlam0 BrownSharedSignals.Fluid.oneAction]
    have hb0 : b.val ≠ 1 := by
      intro hv
      apply hb
      ext
      exact hv
    rw [if_neg hb0]
    change (0 : ℝ) < if (1 : ℝ) = 1 then 1 else 0
    norm_num
  have hp0 : BrownSharedSignals.Fluid.ceLocalPolicy 0
      (BrownSharedSignals.Fluid.initialHistory BrownSharedSignals.Fluid.ceModel)
      0 1 BrownSharedSignals.Fluid.oneAction = 0 := by
    change (if (1 : ℝ) = 0 then (1 : ℝ) else 0) = 0
    norm_num
  linarith
