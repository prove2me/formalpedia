-- Prove2me | solution 1 for BanditAlgorithm.pmMinimaxRegret_eq_zero_of_universally_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T16:16:39.868022+00:00
-- url     : https://prove2.me/submissions/07cac0b5-c111-4daf-9b14-eb30f6414199

import Definitions.Def_PartialMonitoringGame

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

noncomputable def pmConstantPolicy {k : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊]
    (a : Fin k) : PMPolicy k 𝕊 where
  select := fun _ => Kernel.const _ (Measure.dirac a)
  markov := by
    intro t
    infer_instance

private lemma pmMeasure_constantPolicy {k d : ℕ} {𝕊 : Type*}
    [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    ∀ (n : ℕ) (i : Fin n → Fin d),
      pmMeasure G (pmConstantPolicy a) n i =
        Measure.dirac (fun t ↦ (a, G.Φ a (i t))) := by
  intro n
  induction n with
  | zero =>
      intro i
      rw [pmMeasure]
      congr
      funext t
      exact t.elim0
  | succ n ih =>
      intro i
      rw [pmMeasure, ih]
      have hstep :
          pmStepKernel G (pmConstantPolicy (𝕊 := 𝕊) a) (i (Fin.last n)) n =
            Kernel.const _ (Measure.dirac (a, G.Φ a (i (Fin.last n)))) := by
        rw [pmStepKernel, pmConstantPolicy,
          ProbabilityTheory.Kernel.map_const _ (measurable_of_finite _)]
        rw [Measure.map_dirac' (by exact measurable_of_finite _)]
      rw [hstep]
      have hprod :
          (Measure.dirac (fun t : Fin n ↦ (a, G.Φ a (i t.castSucc))) ⊗ₘ
              Kernel.const _ (Measure.dirac (a, G.Φ a (i (Fin.last n))))) =
            Measure.dirac
              ((fun t : Fin n ↦ (a, G.Φ a (i t.castSucc))),
                (a, G.Φ a (i (Fin.last n)))) := by
        ext s hs
        rw [Measure.dirac_compProd_apply hs, Kernel.const_apply]
        rw [MeasureTheory.Measure.dirac_apply' _ (hs.preimage measurable_prodMk_left),
          MeasureTheory.Measure.dirac_apply' _ hs]
        rfl
      rw [hprod, Measure.map_dirac' measurable_pmHistorySnoc]
      congr
      funext t
      refine Fin.lastCases ?_ (fun j ↦ ?_) t
      · simp
      · simp

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a : Fin k)
    (ha : ∀ b : Fin k, ∀ i : Fin d, G.L a i ≤ G.L b i) :
    ∀ n : ℕ, pmMinimaxRegret G n = 0 := by
  intro n
  induction n with
  | zero => simp [pmMinimaxRegret, pmRegret]
  | succ n =>
      cases d with
      | zero => simp [pmMinimaxRegret]
      | succ d =>
          letI : Nonempty (Fin k) := ⟨a⟩
          letI : Nonempty (PMPolicy k 𝕊) :=
            ⟨pmConstantPolicy (𝕊 := 𝕊) a⟩
          let i0 : Fin (n + 1) → Fin (d + 1) := fun _ => 0
          have hnonneg : ∀ π : PMPolicy k 𝕊,
              0 ≤ ⨆ i : Fin (n + 1) → Fin (d + 1), pmRegret G π (n + 1) i := by
            intro π
            refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) i0)
            unfold pmRegret
            refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) a)
            apply integral_nonneg
            intro hist
            apply Finset.sum_nonneg
            intro t _
            exact sub_nonneg.mpr (ha (hist t).1 (i0 t))
          apply le_antisymm
          · unfold pmMinimaxRegret
            refine ciInf_le_of_le
              (f := fun π : PMPolicy k 𝕊 =>
                ⨆ i : Fin (n + 1) → Fin (d + 1), pmRegret G π (n + 1) i)
              (by exact ⟨0, by rintro _ ⟨π, rfl⟩; exact hnonneg π⟩)
              (pmConstantPolicy (𝕊 := 𝕊) a) ?_
            apply ciSup_le
            intro i
            unfold pmRegret
            apply ciSup_le
            intro b
            rw [pmMeasure_constantPolicy]
            simp only [integral_dirac]
            apply Finset.sum_nonpos
            intro t _
            exact sub_nonpos.mpr (ha b (i t))
          · unfold pmMinimaxRegret
            apply le_ciInf
            intro π
            exact hnonneg π
