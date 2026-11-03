-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_capped_killed_Qp_closed_CDF_regeneration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:17:40.205393+00:00
-- url     : https://prove2.me/submissions/33e5cbf0-ffe3-4902-a0ed-cccfaa10a50f

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_capped_killed_Qp_rational_survival_regeneration
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_killed_record_rational_reward_indicator_bridge
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_fresh_rational_Qp_renewal_factor_eq_closed_survival
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_source_capped_lower_killed_history_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b a : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     let Bfull : Set (Ω × ℝ) := {z |
       (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
         0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}
     let discount : ℝ≥0 → ℝ≥0∞ := fun u =>
       ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z, Bfull.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
       (∫⁻ z, ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ s : ℝ≥0,
         s ≤ Real.toNNReal z.2 → 0 ≤ a + X.X s z.1}).indicator
           (fun _ => (1 : ℝ≥0∞)) z ∂Qp)) := by
  classical
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω :=
    {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
    {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
  let Bfull : Set (Ω × ℝ) := {z |
    (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
    ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
      0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}
  let Bgrid : Set (Ω × ℝ) := {z |
    (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
    ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
        Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1 -
          X.X (τ z.1) z.1)}
  let discount : ℝ≥0 → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
  let Qp : Measure (Ω × ℝ) :=
    (P.prod (expMeasure p)).withDensity
      (fun z => ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
  let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun u f =>
    if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < u →
        0 ≤ a + f ((k : ℝ≥0) * (n : ℝ≥0)⁻¹))
    then 1 else 0
  let W : Ω → ℝ≥0∞ := fun ω => if ω ∈ A then 1 else 0
  let R : ℝ≥0∞ :=
    ∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P
  let E : ℝ≥0∞ :=
    ∫⁻ z : Ω × ℝ,
      if (τ z.1 : ℝ) ≤ z.2 then
        W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      else 0 ∂Qp
  let F : ℝ≥0∞ :=
    ∫⁻ r : ℝ, (∫⁻ ω,
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal r) ω -
          (Real.toNNReal r : ℝ) * X.ψ θ)) *
      H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
      ∂(expMeasure p)
  let G : ℝ≥0∞ :=
    ∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 → 0 ≤ a + X.X s z.1}).indicator
          (fun _ => (1 : ℝ≥0∞)) z ∂Qp
  obtain ⟨hτ, hA⟩ :=
    avram_ws01h_source_capped_lower_killed_history_measurable X lower b N
  have hclose :=
    avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral
      X θ p hθ hp a τ hτ A hA
  change (∫⁻ z, Bgrid.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
    (∫⁻ z, Bfull.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) at hclose
  have hbridge :
      E = (∫⁻ z, Bgrid.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) := by
    dsimp only [E]
    apply lintegral_congr
    intro z
    classical
    simp only [Bgrid, H, W, Set.indicator, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have hreg : E = R * F := by
    simpa [E, R, F, H, W, discount, Qp, τ, A] using
      (avram_ws01h_actual_capped_killed_Qp_rational_survival_regeneration
        X lower b a hb N θ p hθ hp)
  have hfresh :=
    avram_ws01h_fresh_rational_Qp_renewal_factor_eq_closed_survival
      X θ p hθ hp a
  change F = G at hfresh
  have hfinal :
      (∫⁻ z, Bfull.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
        R * G := by
    calc
      _ = (∫⁻ z, Bgrid.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) :=
        hclose.symm
      _ = E := hbridge.symm
      _ = R * F := hreg
      _ = R * G := congrArg (R * ·) hfresh
  simpa [τ, A, Bfull, discount, Qp, R, G] using hfinal
