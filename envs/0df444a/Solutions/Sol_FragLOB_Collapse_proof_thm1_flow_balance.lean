-- Prove2me | solution 1 for FragLOB.Collapse.proof_thm1_flow_balance
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:46:15.81535+00:00
-- url     : https://prove2.me/submissions/fac4b732-56ad-4d93-8241-e889649c4673

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

open FragLOB.Collapse in
theorem solution {N : ℕ} (M : Market N) (hM : M.Standing) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0) (pi : ℝ → Fin (N + 1) → ℝ)
    (hpi : IsRouting pi) (hbal : AggBalance M F pi) (W : ℝ) (hW : 0 < W) :
    ∀ i, M.lam i + M.Lam * ∫ γ, pi γ i.succ ∂F = marketRate M (lift M F pi W) i := by
  obtain ⟨_, _, hmu, hbeta⟩ := hM
  have hw : workload M (lift M F pi W) = W := by
    unfold workload lift
    have h1 : ∀ j, M.beta j * ((M.lam j + M.Lam * ∫ γ, pi γ j.succ ∂F) * W / (M.mu * M.beta j))
        = (M.lam j + M.Lam * ∫ γ, pi γ j.succ ∂F) * (W / M.mu) := by
      intro j
      have := hbeta j
      field_simp
    rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_mul]
    unfold AggBalance at hbal
    rw [hbal, mul_div_cancel₀ W hmu.ne']
  intro i
  have hb := hbeta i
  have hW' := hW.ne'
  unfold marketRate
  rw [hw]
  unfold lift
  field_simp
