-- Prove2me | solution 1 for BrownSharedSignals.Fluid.proposition_4_2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:51:15.783707+00:00
-- url     : https://prove2.me/submissions/961ec654-132d-44c1-8822-4e656ea0e7ee

import Mathlib
import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open Classical
noncomputable section

namespace BrownSharedSignals.Fluid

abbrev ceStateDist : Arlib.Probability.FinDist (Fin 1) where
  p := fun _ => 1
  p_nonneg := fun _ => by norm_num
  p_sum := by simp

abbrev ceSignalDist : Arlib.Probability.FinDist (Fin 2) where
  p := fun z => if z = 0 then 1 else 0
  p_nonneg := fun z => by split_ifs <;> norm_num
  p_sum := by simp

abbrev ceProject : ControlledProcess (Fin 1) (Fin 2) where
  actions := fun _ _ _ => {0}
  zero_mem := fun _ _ _ => by simp
  action_nonneg := fun _ _ _ a ha => by
    simp only [Finset.mem_singleton] at ha
    linarith
  reward := fun _ _ _ _ => 0
  transition := fun _ _ _ _ => ceStateDist

abbrev ceModel : Model 1 2 where
  horizon_pos := by decide
  stateSize := fun _ => 0
  signalSize := 1
  project := fun _ => ceProject
  signal := fun _ _ => ceSignalDist
  consumption := fun _ _ _ _ _ => 0
  consumption_zero := fun _ _ _ _ => rfl
  consumption_pos := fun _ _ _ _ a ha hne => by
    dsimp [ceProject] at ha
    exact False.elim (hne (Finset.mem_singleton.mp ha))
  budget := fun _ _ => 0
  budget_nonneg := fun _ _ => le_rfl
  initialState := fun _ => 0
  initialSignal := 0

def zeroAction (t : ℕ) (i : Fin 1) (s : Fin 1) (z : Fin 2) : Action ceModel t i s z :=
  ⟨0, by simp⟩

instance actionSubsingleton (t : ℕ) (i : Fin 1) (s : Fin 1) (z : Fin 2) :
    Subsingleton (Action ceModel t i s z) where
  allEq a b := by
    ext
    have ha : a.val = 0 := Finset.mem_singleton.mp a.property
    have hb : b.val = 0 := Finset.mem_singleton.mp b.property
    rw [ha, hb]

def ceSchedule : Schedule ceModel := fun _ _ _ _ _ => 1

lemma scheduleState_ce :
    ∀ (t : ℕ) (h : History ceModel t) (i : Fin 1) (s : Fin 1),
      scheduleState ceModel ceSchedule t h i s = 1
  | 0, _, i, s => by
    dsimp [scheduleState, initialFluid]
    have hs : s = ceModel.initialState i := Subsingleton.elim _ _
    rw [if_pos hs]
  | t + 1, h, i, s => by
    dsimp [scheduleState, fluidNext]
    rw [Fin.sum_univ_one]
    rw [Finset.sum_eq_single (zeroAction t i 0 (current ceModel (Fin.init h)))]
    · dsimp [ceModel, ceProject, ceStateDist, ceSchedule]
      ring
    · intro b _ hb
      exact False.elim (hb (Subsingleton.elim _ _))
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))

lemma ceSchedule_optimal : OptimalSchedule ceModel ceSchedule := by
  intro t _ h _
  have hfeas : ControlFeasible ceModel t (scheduleState ceModel ceSchedule t h)
      (current ceModel h) (ceSchedule t h) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i s a
      dsimp [ceSchedule]
      norm_num
    · intro i s
      rw [scheduleState_ce]
      rw [Finset.sum_eq_single (zeroAction t i s (current ceModel h))]
      · rfl
      · intro b _ hb
        exact False.elim (hb (Subsingleton.elim _ _))
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · dsimp [ceModel]
      simp
  refine ⟨hfeas, ?_⟩
  intro v hv
  have hveq : v = ceSchedule t h := by
    ext i s a
    have hsum := hv.2.1 i s
    rw [scheduleState_ce] at hsum
    rw [Finset.sum_eq_single a] at hsum
    · exact hsum
    · intro b _ hb
      exact False.elim (hb (Subsingleton.elim _ _))
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  rw [hveq]

def lamZero : Multiplier ceModel := fun _ _ => 0

def ellZero : ProjectCoordinates ceModel := fun _ _ _ _ => 0

def ellOne : ProjectCoordinates ceModel :=
  fun t h _ _ => if t = 1 ∧ current ceModel h = 1 then 1 else 0

lemma penaltyAux_ce (lam : Multiplier ceModel) :
    ∀ (k t : ℕ) (h : History ceModel t), penaltyAux ceModel lam k t h = 0
  | 0, _, _ => rfl
  | k + 1, t, h => by
    unfold penaltyAux
    have hsum : (∑ z', ceModel.signal t (current ceModel h) z' *
        penaltyAux ceModel lam k (t + 1) (Fin.snoc h z')) = 0 := by
      apply Finset.sum_eq_zero
      intro z' _
      rw [penaltyAux_ce lam k (t + 1) (Fin.snoc h z'), mul_zero]
    rw [hsum]
    dsimp [ceModel]
    ring

lemma penalty_ce (lam : Multiplier ceModel) (t : ℕ) (h : History ceModel t) :
    penalty ceModel lam t h = 0 := by
  unfold penalty
  exact penaltyAux_ce lam (2 - t) t h

lemma localActionValue_ce (lam : Multiplier ceModel) (ℓ : ProjectCoordinates ceModel)
    (t : ℕ) (h : History ceModel t) (i : Fin 1) (s : Fin 1)
    (a : Action ceModel t i s (current ceModel h)) :
    localActionValue ceModel lam ℓ t h i s a =
      ℓ (t + 1) (@Fin.snoc (t + 1) (fun _ => Signal ceModel) h 0) 0 0 := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  unfold localActionValue
  rw [Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_one]
  dsimp [ceModel, ceProject, ceSignalDist]
  ring

lemma LP6Objective_nonneg {lam : Multiplier ceModel} {ℓ : ProjectCoordinates ceModel}
    (hfeas : LP6Feasible ceModel lam ℓ) :
    0 ≤ LP6Objective ceModel lam ℓ := by
  let h0 : History ceModel 0 := initialHistory ceModel
  let h00 : History ceModel 1 := @Fin.snoc 1 (fun _ => Signal ceModel) h0 0
  have h1 := hfeas.2.2 1 (by decide) h00 0 0 (zeroAction 1 0 0 (current ceModel h00))
  rw [localActionValue_ce, hfeas.2.1 (@Fin.snoc 2 (fun _ => Signal ceModel) h00 0) 0 0] at h1
  have h2 := hfeas.2.2 0 (by decide) h0 0 0 (zeroAction 0 0 0 (current ceModel h0))
  rw [localActionValue_ce] at h2
  unfold LP6Objective
  rw [penalty_ce, Fin.sum_univ_one]
  change 0 ≤ 0 + ℓ 0 h0 0 0
  linarith

lemma ellZero_LP6Optimal : LP6Optimal ceModel lamZero ellZero := by
  have hfeas : LP6Feasible ceModel lamZero ellZero := by
    refine ⟨fun _ _ _ => le_rfl, fun _ _ _ => rfl, ?_⟩
    intro t _ h i s a
    rw [localActionValue_ce]
    rfl
  refine ⟨hfeas, ?_⟩
  intro lam' ℓ' hfeas'
  have hobj : LP6Objective ceModel lamZero ellZero = 0 := by
    unfold LP6Objective
    rw [penalty_ce, Fin.sum_univ_one]
    dsimp [ellZero]
    ring
  rw [hobj]
  exact LP6Objective_nonneg hfeas'

lemma ellOne_LP6Optimal : LP6Optimal ceModel lamZero ellOne := by
  have hfeas : LP6Feasible ceModel lamZero ellOne := by
    refine ⟨fun _ _ _ => le_rfl, ?_, ?_⟩
    · intro h i s
      simp [ellOne]
    · intro t ht h i s a
      rw [localActionValue_ce]
      have hts : t = 0 ∨ t = 1 := by omega
      rcases hts with rfl | rfl
      · have hlast : current ceModel (@Fin.snoc 1 (fun _ => Signal ceModel) h 0) = 0 := rfl
        simp [ellOne, hlast]
      · dsimp [ellOne]
        split_ifs <;> norm_num
  refine ⟨hfeas, ?_⟩
  intro lam' ℓ' hfeas'
  have hobj : LP6Objective ceModel lamZero ellOne = 0 := by
    unfold LP6Objective
    rw [penalty_ce, Fin.sum_univ_one]
    dsimp [ellOne]
    simp
  rw [hobj]
  exact LP6Objective_nonneg hfeas'

def nullHistory : History ceModel 1 := fun k => if k.val = 0 then 0 else 1

end BrownSharedSignals.Fluid

theorem solution : ¬ (∀ {N T : ℕ} (M : BrownSharedSignals.Fluid.Model N T),
    (∀ u : BrownSharedSignals.Fluid.Schedule M,
      BrownSharedSignals.Fluid.OptimalSchedule M u →
      BrownSharedSignals.Fluid.LP7Optimal M (BrownSharedSignals.Fluid.scheduleOccupancy M u)) ∧
    (∀ μ : BrownSharedSignals.Fluid.Occupancy M,
      BrownSharedSignals.Fluid.LP7Optimal M μ →
      ∃ u : BrownSharedSignals.Fluid.Schedule M,
        BrownSharedSignals.Fluid.OptimalSchedule M u ∧
        ∀ t < T, ∀ h, 0 < BrownSharedSignals.Fluid.historyProb M t h →
          ∀ i s a, u t h i s a = μ t h i s a / BrownSharedSignals.Fluid.historyProb M t h) ∧
    (∀ t < T, ∀ (h : BrownSharedSignals.Fluid.History M t) (f : BrownSharedSignals.Fluid.FluidVector M),
      BrownSharedSignals.Fluid.IsFluidState M f →
      ∀ ν : Arlib.Probability.FinDist (BrownSharedSignals.Fluid.State M),
        (∀ i s, (∑ x : BrownSharedSignals.Fluid.State M, if x i = s then ν x else 0) = f i s) →
        (∑ s, ν s * BrownSharedSignals.Fluid.optimalValue M t h s) ≤
          BrownSharedSignals.Fluid.fluidValue M t f (BrownSharedSignals.Fluid.current M h)) ∧
    (∀ lam : BrownSharedSignals.Fluid.Multiplier M,
      BrownSharedSignals.Fluid.NonnegativeMultiplier M lam →
      ∀ t < T, ∀ h f, BrownSharedSignals.Fluid.IsFluidState M f →
        BrownSharedSignals.Fluid.fluidValue M t f (BrownSharedSignals.Fluid.current M h) ≤
          BrownSharedSignals.Fluid.penalty M lam t h +
          ∑ i, ∑ s, f i s * BrownSharedSignals.Fluid.projectValue M lam t h i s) ∧
    (∀ lam ℓ, BrownSharedSignals.Fluid.LP6Optimal M lam ℓ →
      ∀ u : BrownSharedSignals.Fluid.Schedule M,
      BrownSharedSignals.Fluid.OptimalSchedule M u →
      ∀ t < T, ∀ h, h 0 = M.initialSignal →
        BrownSharedSignals.Fluid.fluidValue M t
          (BrownSharedSignals.Fluid.scheduleState M u t h)
          (BrownSharedSignals.Fluid.current M h) =
          BrownSharedSignals.Fluid.penalty M lam t h +
          ∑ i, ∑ s, BrownSharedSignals.Fluid.scheduleState M u t h i s * ℓ t h i s ∧
        BrownSharedSignals.Fluid.Supergradient M t
          (BrownSharedSignals.Fluid.current M h)
          (BrownSharedSignals.Fluid.scheduleState M u t h) (ℓ t h))) := by
  intro hall
  have hd := (hall BrownSharedSignals.Fluid.ceModel).2.2.2.2
  have hroot : BrownSharedSignals.Fluid.nullHistory 0 =
      BrownSharedSignals.Fluid.ceModel.initialSignal := rfl
  have heq0 := (hd BrownSharedSignals.Fluid.lamZero BrownSharedSignals.Fluid.ellZero
    BrownSharedSignals.Fluid.ellZero_LP6Optimal
    BrownSharedSignals.Fluid.ceSchedule BrownSharedSignals.Fluid.ceSchedule_optimal
    1 (by decide) BrownSharedSignals.Fluid.nullHistory hroot).1
  have heq1 := (hd BrownSharedSignals.Fluid.lamZero BrownSharedSignals.Fluid.ellOne
    BrownSharedSignals.Fluid.ellOne_LP6Optimal
    BrownSharedSignals.Fluid.ceSchedule BrownSharedSignals.Fluid.ceSchedule_optimal
    1 (by decide) BrownSharedSignals.Fluid.nullHistory hroot).1
  rw [BrownSharedSignals.Fluid.penalty_ce, Fin.sum_univ_one, Fin.sum_univ_one,
    BrownSharedSignals.Fluid.scheduleState_ce] at heq0 heq1
  change BrownSharedSignals.Fluid.fluidValue BrownSharedSignals.Fluid.ceModel 1
      (BrownSharedSignals.Fluid.scheduleState BrownSharedSignals.Fluid.ceModel
        BrownSharedSignals.Fluid.ceSchedule 1 BrownSharedSignals.Fluid.nullHistory)
      (BrownSharedSignals.Fluid.current BrownSharedSignals.Fluid.ceModel
        BrownSharedSignals.Fluid.nullHistory) = 0 + 1 * 0 at heq0
  change BrownSharedSignals.Fluid.fluidValue BrownSharedSignals.Fluid.ceModel 1
      (BrownSharedSignals.Fluid.scheduleState BrownSharedSignals.Fluid.ceModel
        BrownSharedSignals.Fluid.ceSchedule 1 BrownSharedSignals.Fluid.nullHistory)
      (BrownSharedSignals.Fluid.current BrownSharedSignals.Fluid.ceModel
        BrownSharedSignals.Fluid.nullHistory) = 0 + 1 * 1 at heq1
  linarith
