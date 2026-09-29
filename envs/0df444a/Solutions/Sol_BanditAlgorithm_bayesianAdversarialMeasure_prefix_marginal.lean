-- Prove2me | solution 1 for BanditAlgorithm.bayesianAdversarialMeasure_prefix_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T00:47:16.385636+00:00
-- url     : https://prove2.me/submissions/aad88556-96bf-43f8-a20b-0b233d8c7449

import Definitions.Def_ThompsonSampling

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem measurable_bayesianPrefix {k N u t : ℕ} (ht : t ≤ u) :
    Measurable (fun p : (Fin N → Fin k → ℝ) × BanditHistory k u ↦
      (p.1, fun s : Fin t ↦ p.2 (Fin.castLE ht s))) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro s
  exact (measurable_pi_apply (Fin.castLE ht s)).comp measurable_snd

theorem _root_.solution {k n : ℕ}
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (u : ℕ) (hu : u ≤ n) (t : ℕ) (ht : t ≤ u) :
    Measure.map
        (fun p : (Fin n → Fin k → ℝ) × BanditHistory k u ↦
          (p.1, fun s : Fin t ↦ p.2 (Fin.castLE ht s)))
        (bayesianAdversarialMeasure Q pi u hu) =
      bayesianAdversarialMeasure Q pi t (ht.trans hu) := by
  induction u generalizing t with
  | zero =>
      have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
      subst t
      rw [bayesianAdversarialMeasure]
      rw [Measure.map_map]
      · apply Measure.map_congr
        exact Filter.Eventually.of_forall fun X ↦ by rfl
      · exact measurable_bayesianPrefix ht
      · exact measurable_id.prodMk measurable_const
  | succ u ih =>
      by_cases htu : t = u + 1
      · subst t
        have hfun :
            (fun p : (Fin n → Fin k → ℝ) × BanditHistory k (u + 1) ↦
              (p.1, fun s : Fin (u + 1) ↦ p.2 (Fin.castLE ht s))) = id := by
          funext p
          apply Prod.ext rfl
          funext s
          congr
        rw [hfun, Measure.map_id]
      · have ht' : t ≤ u := Nat.le_of_lt_succ (lt_of_le_of_ne ht htu)
        rw [bayesianAdversarialMeasure, Measure.map_map]
        · change Measure.map
            (fun p : ((Fin n → Fin k → ℝ) × BanditHistory k u) × (Fin k × ℝ) ↦
              (p.1.1, fun s : Fin t ↦
                (Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1.2 p.2)
                  (Fin.castLE ht s)))
            ((bayesianAdversarialMeasure Q pi u (Nat.le_of_succ_le hu)).compProd
              (bayesianAdversarialStepKernel pi u ⟨u, hu⟩)) = _
          have hfun :
              (fun p : ((Fin n → Fin k → ℝ) × BanditHistory k u) × (Fin k × ℝ) ↦
                (p.1.1, fun s : Fin t ↦
                  (Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1.2 p.2)
                    (Fin.castLE ht s))) =
              (fun p ↦ (p.1.1, fun s : Fin t ↦ p.1.2 (Fin.castLE ht' s))) := by
            funext p
            congr
            funext s
            have hcast : Fin.castLE ht s = (Fin.castLE ht' s).castSucc := by
              apply Fin.ext
              rfl
            rw [hcast, Fin.snoc_castSucc]
          rw [hfun]
          rw [show (fun p : ((Fin n → Fin k → ℝ) × BanditHistory k u) × (Fin k × ℝ) ↦
                (p.1.1, fun s : Fin t ↦ p.1.2 (Fin.castLE ht' s))) =
              (fun q : (Fin n → Fin k → ℝ) × BanditHistory k u ↦
                (q.1, fun s : Fin t ↦ q.2 (Fin.castLE ht' s))) ∘ Prod.fst by rfl]
          rw [← Measure.map_map (measurable_bayesianPrefix ht') measurable_fst]
          rw [show (((bayesianAdversarialMeasure Q pi u (Nat.le_of_succ_le hu)).compProd
              (bayesianAdversarialStepKernel pi u ⟨u, hu⟩)).map Prod.fst) =
              bayesianAdversarialMeasure Q pi u (Nat.le_of_succ_le hu) by
            exact Measure.fst_compProd _ _]
          exact ih (Nat.le_of_succ_le hu) t ht'
        · exact measurable_bayesianPrefix ht
        · exact (measurable_fst.comp measurable_fst).prodMk
            (measurable_banditHistorySnoc.comp
              ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

end BanditAlgorithm
