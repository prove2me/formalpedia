-- Prove2me | solution 1 for CorruptRobustRL.Supervised.lemma4_6_admissible_of_valid
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:15:12.512283+00:00
-- url     : https://prove2.me/submissions/a2896e36-97f6-4ac9-8e87-b261abc3a1de

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

open CorruptRobustRL.Supervised
open Finset QSupervisor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CRRL_L46

variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

theorem backup_nonneg (H : ℕ) (m : ModelEst X A) (hm : m.IsModelEst H) (V : X → ℝ)
    (hV : ∀ x, 0 ≤ V x) (x : X) (a : A) : 0 ≤ backup m V x a := by
  obtain ⟨⟨hr, -⟩, ⟨hp, -⟩, -⟩ := hm x a
  unfold backup
  exact add_nonneg hr (Finset.sum_nonneg fun y _ => mul_nonneg (hp y) (hV y))

theorem backup_le (H : ℕ) (m : ModelEst X A) (hm : m.IsModelEst H) (V : X → ℝ) (c : ℝ)
    (hV : ∀ x, V x ≤ c) (x : X) (a : A) : backup m V x a ≤ 1 + c := by
  obtain ⟨⟨-, hr⟩, ⟨hp, hp1⟩, -⟩ := hm x a
  unfold backup
  have : ∑ x', m.p x a x' * V x' ≤ ∑ x', m.p x a x' * c :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hV y) (hp y)
  rw [← Finset.sum_mul, hp1, one_mul] at this
  linarith

theorem vals_bounds (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A)
    (sel : Selector A) (hgl : gl.IsModelEst H) (hsb : sb.IsModelEst H) :
    ∀ n x, (0 ≤ (ucbviVals H act gl sb sel n).1 x ∧ (ucbviVals H act gl sb sel n).1 x ≤ H) ∧
      (0 ≤ (ucbviVals H act gl sb sel n).2 x ∧ (ucbviVals H act gl sb sel n).2 x ≤ n) := by
  intro n
  induction n with
  | zero => intro x; simp [ucbviVals]
  | succ n ih =>
    intro x
    simp only [ucbviVals]
    refine ⟨⟨?_, min_le_left _ _⟩, ?_⟩
    · apply le_min (Nat.cast_nonneg _)
      apply le_min
      · exact add_nonneg (backup_nonneg H gl hgl _ (fun y => (ih y).1.1) _ _)
          ((hgl x _).2.2.1)
      · exact add_nonneg (backup_nonneg H sb hsb _ (fun y => (ih y).1.1) _ _)
          ((hsb x _).2.2.1)
    · have hq : ∀ a, 0 ≤ qLow gl sb (ucbviVals H act gl sb sel n).2 x a ∧
          qLow gl sb (ucbviVals H act gl sb sel n).2 x a ≤ (n + 1 : ℕ) := by
        intro a
        refine ⟨le_max_left _ _, max_le (by positivity) (max_le ?_ ?_)⟩
        · have h1 := backup_le H gl hgl _ (n : ℝ) (fun y => (ih y).2.2) x a
          have h2 := (hgl x a).2.2.1
          push_cast; linarith
        · have h1 := backup_le H sb hsb _ (n : ℝ) (fun y => (ih y).2.2) x a
          have h2 := (hsb x a).2.2.1
          push_cast; linarith
      unfold CorruptRobustRL.Supervised.maxOn
      split_ifs with hne
      · obtain ⟨a0, ha0⟩ := hne
        exact ⟨le_trans (hq a0).1 (Finset.le_sup' _ ha0),
          Finset.sup'_le _ _ fun a _ => (hq a).2⟩
      · exact ⟨le_rfl, by positivity⟩

theorem Vbar_eq (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (h : ℕ) (hh : h < H) (x : X) :
    Vbar H (ucbviSup H act gl sb sel) (h + 1) x = (ucbviVals H act gl sb sel (H - (h + 1))).1 x := by
  unfold Vbar
  split_ifs with h1
  · rw [show H - (h + 1) = (H - (h + 1 + 1)) + 1 by omega, ucbviVals]
    simp only [ucbviSup]
    rw [show H - (H - (h + 1 + 1) + 1) = h + 1 by omega]
  · rw [show H - (h + 1) = 0 by omega]; rfl

theorem Vlow_eq (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (h : ℕ) (hh : h < H) (x : X) :
    Vlow H (ucbviSup H act gl sb sel) (h + 1) x = (ucbviVals H act gl sb sel (H - (h + 1))).2 x := by
  unfold Vlow
  by_cases h1 : h + 1 < H
  · rw [if_pos h1]
    rw [show H - (h + 1) = (H - (h + 1 + 1)) + 1 by omega, ucbviVals]
    simp only [ucbviSup]
    rw [show H - (H - (h + 1 + 1) + 1) = h + 1 by omega]
    unfold CorruptRobustRL.Supervised.maxOn
    rfl
  · rw [if_neg h1, show H - (h + 1) = 0 by omega]; rfl


theorem VstarRem_bounds (M : NominalMDP X A) (hM : M.IsNominal) :
    ∀ n x, 0 ≤ VstarRem M n x ∧ VstarRem M n x ≤ n := by
  intro n
  induction n with
  | zero => intro x; simp [VstarRem]
  | succ n ih =>
    intro x
    simp only [VstarRem]
    have hq : ∀ a, 0 ≤ M.rstar x a + ∑ x', M.pstar x a x' * VstarRem M n x' ∧
        M.rstar x a + ∑ x', M.pstar x a x' * VstarRem M n x' ≤ (n + 1 : ℕ) := by
      intro a
      obtain ⟨hp0, hp1⟩ := hM.2.1 x a
      obtain ⟨hr0, hr1⟩ := hM.2.2 x a
      have hs0 : 0 ≤ ∑ x', M.pstar x a x' * VstarRem M n x' :=
        Finset.sum_nonneg fun y _ => mul_nonneg (hp0 y) (ih y).1
      have hs1 : ∑ x', M.pstar x a x' * VstarRem M n x' ≤ n := by
        have : ∑ x', M.pstar x a x' * VstarRem M n x' ≤ ∑ x', M.pstar x a x' * (n : ℝ) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih y).2 (hp0 y)
        rwa [← Finset.sum_mul, hp1, one_mul] at this
      push_cast
      constructor <;> linarith
    obtain ⟨a0⟩ := (inferInstance : Nonempty A)
    exact ⟨le_trans (hq a0).1 (Finset.le_sup' (fun a => M.rstar x a + ∑ x', M.pstar x a x' * VstarRem M n x') (mem_univ a0)),
      Finset.sup'_le _ _ fun a _ => (hq a).2⟩

theorem Vstar_eq_sup (M : NominalMDP X A) (H h : ℕ) (hh : h < H) (x : X) :
    Vstar M H h x = univ.sup' univ_nonempty (Qstar M H h x) := by
  unfold Vstar Qstar
  rw [show H - h = (H - (h + 1)) + 1 by omega, VstarRem]
  rfl

theorem Qstar_le_Vstar (M : NominalMDP X A) (H h : ℕ) (hh : h < H) (x : X) (a : A) :
    Qstar M H h x a ≤ Vstar M H h x := by
  rw [Vstar_eq_sup M H h hh x]; exact Finset.le_sup' _ (mem_univ a)

theorem exists_opt (M : NominalMDP X A) (H h : ℕ) (hh : h < H) (x : X) :
    ∃ a, a ∈ optActions M H h x := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) (Qstar M H h x)
  refine ⟨a, ?_⟩
  unfold optActions
  simp only [Finset.mem_filter, mem_univ, true_and]
  rw [Vstar_eq_sup M H h hh x, ha]

theorem mem_opt (M : NominalMDP X A) (H h : ℕ) (x : X) (a : A) (ha : a ∈ optActions M H h x) :
    Qstar M H h x a = Vstar M H h x := by
  unfold optActions at ha
  simpa using ha

theorem Vstar_bounds (M : NominalMDP X A) (hM : M.IsNominal) (H h : ℕ) (x : X) :
    0 ≤ Vstar M H h x ∧ Vstar M H h x ≤ H := by
  obtain ⟨h1, h2⟩ := VstarRem_bounds M hM (H - h) x
  exact ⟨h1, le_trans h2 (by exact_mod_cast Nat.sub_le H h)⟩

theorem Qstar_nonneg (M : NominalMDP X A) (hM : M.IsNominal) (H h : ℕ) (x : X) (a : A) :
    0 ≤ Qstar M H h x a := by
  unfold Qstar
  exact add_nonneg (hM.2.2 x a).1
    (Finset.sum_nonneg fun y _ => mul_nonneg ((hM.2.1 x a).1 y) (Vstar_bounds M hM H _ y).1)

theorem Qstar_le_H (M : NominalMDP X A) (hM : M.IsNominal) (H h : ℕ) (hh : h < H) (x : X) (a : A) :
    Qstar M H h x a ≤ H := by
  unfold Qstar Vstar
  obtain ⟨hp0, hp1⟩ := hM.2.1 x a
  have hs1 : ∑ x', M.pstar x a x' * VstarRem M (H - (h + 1)) x' ≤ ((H - (h + 1) : ℕ) : ℝ) := by
    have : ∑ x', M.pstar x a x' * VstarRem M (H - (h + 1)) x' ≤
        ∑ x', M.pstar x a x' * ((H - (h + 1) : ℕ) : ℝ) :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (VstarRem_bounds M hM _ y).2 (hp0 y)
    rwa [← Finset.sum_mul, hp1, one_mul] at this
  have hc : ((H - (h + 1) : ℕ) : ℝ) + 1 ≤ H := by
    exact_mod_cast (show H - (h + 1) + 1 ≤ H by omega)
  have := (hM.2.2 x a).2
  linarith

/-- One-model sandwich step. -/
theorem model_step (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (m : ModelEst X A)
    (hm : m.IsModelEst H) (Vs Vb Vl : X → ℝ) (hb : ∀ y, Vs y ≤ Vb y) (hl : ∀ y, Vl y ≤ Vs y)
    (x : X) (a : A) (hd : |m.dev M Vs x a| ≤ m.b x a) :
    M.rstar x a + ∑ x', M.pstar x a x' * Vs x' ≤ backup m Vb x a + m.b x a ∧
      backup m Vl x a - m.b x a ≤ M.rstar x a + ∑ x', M.pstar x a x' * Vs x' := by
  obtain ⟨-, ⟨hp0, -⟩, -⟩ := hm x a
  have hd' := abs_le.mp hd
  unfold ModelEst.dev at hd'
  have e : ∑ x', (m.p x a x' - M.pstar x a x') * Vs x' =
      ∑ x', m.p x a x' * Vs x' - ∑ x', M.pstar x a x' * Vs x' := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun y _ => by ring
  rw [e] at hd'
  have s1 : ∑ x', m.p x a x' * Vs x' ≤ ∑ x', m.p x a x' * Vb x' :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hb y) (hp0 y)
  have s2 : ∑ x', m.p x a x' * Vl x' ≤ ∑ x', m.p x a x' * Vs x' :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hl y) (hp0 y)
  unfold backup
  constructor <;> linarith [hd'.1, hd'.2]

theorem dev_of_valid (M : NominalMDP X A) (H : ℕ) (T : QSupervisor X A) (m : ModelEst X A)
    (hv : m.IsValid M H T) (h : ℕ) (hh : h < H) (x : X) (a : A) :
    |m.dev M (Vstar M H (h + 1)) x a| ≤ m.b x a := by
  rcases hv h hh x a with h1 | h1
  · exact h1.2
  · exact h1.1

/-- A run of UCBVI-BASE whose active sets contain the optimal actions and whose model-estimates
are valid is confidence-admissible; moreover `V̲ ≤ V⋆ ≤ V̄` at every stage. -/
theorem learner_admissible (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ)
    (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (hsel : IsArgmaxSelector sel) (hgl : gl.IsModelEst H) (hsb : sb.IsModelEst H)
    (hopt : ∀ h < H, ∀ x, optActions M H h x ⊆ act h x)
    (hvgl : gl.IsValid M H (ucbviSup H act gl sb sel))
    (hvsb : sb.IsValid M H (ucbviSup H act gl sb sel)) :
    IsAdmissible M H (ucbviSup H act gl sb sel) := by
  set T := ucbviSup H act gl sb sel with hT
  -- Bellman step at stage h < H from the sandwich at h + 1
  have step : ∀ h < H, (∀ y, Vlow H T (h + 1) y ≤ Vstar M H (h + 1) y ∧
      Vstar M H (h + 1) y ≤ Vbar H T (h + 1) y) →
      ∀ x a, T.Qlow h x a ≤ Qstar M H h x a ∧ Qstar M H h x a ≤ T.Qbar h x a := by
    intro h hh hS x a
    have hVb : ∀ y, Vbar H T (h + 1) y = (ucbviVals H act gl sb sel (H - (h + 1))).1 y :=
      fun y => Vbar_eq H act gl sb sel h hh y
    have hVl : ∀ y, Vlow H T (h + 1) y = (ucbviVals H act gl sb sel (H - (h + 1))).2 y :=
      fun y => Vlow_eq H act gl sb sel h hh y
    have g1 := model_step M hM H gl hgl (Vstar M H (h + 1)) (Vbar H T (h + 1)) (Vlow H T (h + 1))
      (fun y => (hS y).2) (fun y => (hS y).1) x a (dev_of_valid M H T gl hvgl h hh x a)
    have g2 := model_step M hM H sb hsb (Vstar M H (h + 1)) (Vbar H T (h + 1)) (Vlow H T (h + 1))
      (fun y => (hS y).2) (fun y => (hS y).1) x a (dev_of_valid M H T sb hvsb h hh x a)
    have eVb : Vbar H T (h + 1) = (ucbviVals H act gl sb sel (H - (h + 1))).1 := funext hVb
    have eVl : Vlow H T (h + 1) = (ucbviVals H act gl sb sel (H - (h + 1))).2 := funext hVl
    rw [eVb, eVl] at g1 g2
    have hQ : Qstar M H h x a = M.rstar x a + ∑ x', M.pstar x a x' * Vstar M H (h + 1) x' := rfl
    constructor
    · show max 0 (max _ _) ≤ _
      exact max_le (Qstar_nonneg M hM H h x a) (max_le (hQ ▸ g1.2) (hQ ▸ g2.2))
    · show _ ≤ min (H : ℝ) (min _ _)
      exact le_min (Qstar_le_H M hM H h hh x a) (le_min (hQ ▸ g1.1) (hQ ▸ g2.1))
  -- the sandwich at stage h from the Bellman step at h
  have sand : ∀ h < H, (∀ x a, T.Qlow h x a ≤ Qstar M H h x a ∧ Qstar M H h x a ≤ T.Qbar h x a) →
      ∀ y, Vlow H T h y ≤ Vstar M H h y ∧ Vstar M H h y ≤ Vbar H T h y := by
    intro h hh hB y
    obtain ⟨a0, ha0⟩ := exists_opt M H h hh y
    have ha0' := hopt h hh y ha0
    have hstar := mem_opt M H h y a0 ha0
    constructor
    · unfold Vlow
      rw [if_pos hh]
      split_ifs with hne
      · exact Finset.sup'_le _ _ fun a _ => le_trans (hB y a).1 (Qstar_le_Vstar M H h hh y a)
      · exact (Vstar_bounds M hM H h y).1
    · unfold Vbar
      rw [if_pos hh]
      have hmax := (hsel (act h y) (fun a => T.Qbar h y a) ⟨a0, ha0'⟩).2 a0 ha0'
      calc Vstar M H h y = Qstar M H h y a0 := hstar.symm
        _ ≤ T.Qbar h y a0 := (hB y a0).2
        _ ≤ _ := hmax
  -- backward induction
  have main : ∀ k, ∀ h, h + k = H → ∀ y, Vlow H T h y ≤ Vstar M H h y ∧ Vstar M H h y ≤ Vbar H T h y := by
    intro k
    induction k with
    | zero =>
      intro h hk y
      have : h = H := by omega
      subst this
      simp [Vlow, Vbar, Vstar, VstarRem]
    | succ k ih =>
      intro h hk
      exact sand h (by omega) (step h (by omega) (ih (h + 1) (by omega)))
  intro h hh x
  refine ⟨hopt h hh x, fun a => ?_⟩
  exact step h hh (main (H - (h + 1)) (h + 1) (by omega)) x a

theorem opt_key (M : NominalMDP X A) (H : ℕ)
    (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (hadm : IsAdmissible M H (ucbviSup H act gl sb sel)) (h : ℕ) (hh : h < H) (x : X)
    (a0 : A) (ha0 : a0 ∈ optActions M H h x) :
    a0 ∈ act h x ∧ CorruptRobustRL.Supervised.maxOn (act h x) ((ucbviSup H act gl sb sel).Qlow h x) ≤
      (ucbviSup H act gl sb sel).Qbar h x a0 := by
  obtain ⟨hsub, hQ⟩ := hadm h hh x
  refine ⟨hsub ha0, ?_⟩
  have hstar := mem_opt M H h x a0 ha0
  unfold CorruptRobustRL.Supervised.maxOn
  split_ifs with hne
  · apply Finset.sup'_le
    intro a _
    calc (ucbviSup H act gl sb sel).Qlow h x a ≤ Qstar M H h x a := (hQ a).1
      _ ≤ Vstar M H h x := Qstar_le_Vstar M H h hh x a
      _ = Qstar M H h x a0 := hstar.symm
      _ ≤ _ := (hQ a0).2
  · exact absurd ⟨a0, hsub ha0⟩ hne

/-- For an admissible learner the filtered set is nonempty, so `nextAct` is the filter. -/
theorem nextAct_spec (M : NominalMDP X A) (H : ℕ)
    (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (hadm : IsAdmissible M H (ucbviSup H act gl sb sel)) (h : ℕ) (hh : h < H) (x : X) (a : A) :
    a ∈ nextAct H act gl sb sel h x ↔ a ∈ act h x ∧
      CorruptRobustRL.Supervised.maxOn (act h x) ((ucbviSup H act gl sb sel).Qlow h x) ≤
        (ucbviSup H act gl sb sel).Qbar h x a := by
  obtain ⟨a0, ha0⟩ := exists_opt M H h hh x
  have k0 := opt_key M H act gl sb sel hadm h hh x a0 ha0
  unfold nextAct
  dsimp only
  split_ifs with hs
  · rw [Finset.mem_filter]
  · exact absurd ⟨a0, by rw [Finset.mem_filter]; exact k0⟩ hs

theorem opt_sub_nextAct (M : NominalMDP X A) (H : ℕ)
    (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (hadm : IsAdmissible M H (ucbviSup H act gl sb sel)) (h : ℕ) (hh : h < H) (x : X) :
    optActions M H h x ⊆ nextAct H act gl sb sel h x := fun a0 ha0 =>
  (nextAct_spec M H act gl sb sel hadm h hh x a0).2 (opt_key M H act gl sb sel hadm h hh x a0 ha0)

theorem layerAct_succ (H ℓmax : ℕ) (E : EpisodeEst X A) (sel : Selector A) (d : ℕ)
    (hd : d + 1 ≤ ℓmax) :
    layerAct H ℓmax E sel (ℓmax - (d + 1)) =
      nextAct H (layerAct H ℓmax E sel (ℓmax - d)) (E.gl (ℓmax - d)) (E.sb (ℓmax - d)) sel := by
  unfold layerAct
  rw [show ℓmax - (ℓmax - (d + 1)) = d + 1 by omega, show ℓmax - (ℓmax - d) = d by omega]
  rfl

end CRRL_L46

open CRRL_L46 in
theorem solution
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H ℓmax : ℕ) (hH : 1 ≤ H)
    (E : EpisodeEst X A)
    (hrange : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax → (E.gl ℓ).IsModelEst H ∧ (E.sb ℓ).IsModelEst H)
    (sel : Selector A) (hsel : IsArgmaxSelector sel)
    (lst : ℕ) (hlst : 1 ≤ lst) (hlstmax : lst ≤ ℓmax)
    (hvalid : ∀ ℓ, lst ≤ ℓ → ℓ ≤ ℓmax →
      (E.gl ℓ).IsValid M H (layerSup H ℓmax E sel ℓ) ∧
        (E.sb ℓ).IsValid M H (layerSup H ℓmax E sel ℓ)) :
    ∀ ℓ, lst ≤ ℓ → ℓ ≤ ℓmax → IsAdmissible M H (layerSup H ℓmax E sel ℓ) := by
  have adm : ∀ ℓ, lst ≤ ℓ → ℓ ≤ ℓmax → (∀ h < H, ∀ x, optActions M H h x ⊆ layerAct H ℓmax E sel ℓ h x) →
      IsAdmissible M H (layerSup H ℓmax E sel ℓ) := by
    intro ℓ hl hlm hopt
    exact learner_admissible M hM H _ _ _ sel hsel (hrange ℓ (by omega) hlm).1
      (hrange ℓ (by omega) hlm).2 hopt (hvalid ℓ hl hlm).1 (hvalid ℓ hl hlm).2
  have chain : ∀ d, d ≤ ℓmax - lst → ∀ h < H, ∀ x,
      optActions M H h x ⊆ layerAct H ℓmax E sel (ℓmax - d) h x := by
    intro d
    induction d with
    | zero =>
      intro _ h _ x
      unfold layerAct
      rw [show ℓmax - (ℓmax - 0) = 0 by omega]
      intro a _
      exact mem_univ a
    | succ d ih =>
      intro hd h hh x
      rw [layerAct_succ H ℓmax E sel d (by omega)]
      exact opt_sub_nextAct M H _ _ _ sel
        (adm (ℓmax - d) (by omega) (by omega) (ih (by omega))) h hh x
  intro ℓ hl hlm
  apply adm ℓ hl hlm
  have := chain (ℓmax - ℓ) (by omega)
  rwa [show ℓmax - (ℓmax - ℓ) = ℓ by omega] at this
