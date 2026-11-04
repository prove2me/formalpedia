-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_clock_witness_from_source_mesh_component_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:12.916897+00:00
-- url     : https://prove2.me/submissions/2d8db0a9-f2ac-4a35-a391-68306ceac955

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_source_mesh_limit_signed_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact conditional original stopped-clock assembly from source mesh
    convergence and genuinely centred L¹ stochastic contributions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (Mseq Gseq Hseq : ℕ → Ω → ℝ)
    (Mc Ms Ml G H : Ω → ℝ)
    (hc : Integrable Mc P) (hs : Integrable Ms P)
    (hl : Integrable Ml P) (hg : Integrable G P)
    (hh : Integrable H P)
    (hc0 : (∫ ω, Mc ω ∂P) = 0)
    (hs0 : (∫ ω, Ms ω ∂P) = 0)
    (hl0 : (∫ ω, Ml ω ∂P) = 0)
    (hupper : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Term ω + Cash ω ≤ w x + Mseq k ω + Gseq k ω + Hseq k ω)
    (hsign : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Gseq k ω + Hseq k ω ≤ 0)
    (hconv : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => Mseq k ω) atTop
        (𝓝 (Mc ω + Ms ω + Ml ω)) ∧
      Tendsto (fun k : ℕ => Gseq k ω) atTop (𝓝 (G ω)) ∧
      Tendsto (fun k : ℕ => Hseq k ω) atTop (𝓝 (H ω))) :
    ∃ M G' H' : Ω → ℝ,
      Integrable M P ∧ Integrable G' P ∧ Integrable H' P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G' ω + H' ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + M ω + G' ω + H' ω) := by
  have hlim :=
    avram_p4_f_assembly_source_mesh_limit_signed_budget
      X q x w D τ W Cash Term hW hCash hTerm
      Mseq Gseq Hseq (fun ω => Mc ω + Ms ω + Ml ω) G H
      hupper hsign hconv
  have hito : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + H ω := by
    filter_upwards [hlim.2] with ω hω
    convert hω using 1 <;> ring
  exact avram_p4_f_assembly_three_source_martingales
    w x Term Cash Mc Ms Ml G H
    hc hs hl hg hh hc0 hs0 hl0 hlim.1 hito
