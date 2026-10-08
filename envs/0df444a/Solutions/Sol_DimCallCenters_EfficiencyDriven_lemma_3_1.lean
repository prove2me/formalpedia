-- Prove2me | solution 1 for DimCallCenters.EfficiencyDriven.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:08:40.194411+00:00
-- url     : https://prove2.me/submissions/da4b8005-f41b-41cb-a744-1973b9aff9a3

import Mathlib
import Definitions.Def_DimCallCenters_EfficiencyDriven_Optima
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate

open Filter

namespace P6ff9d752

open DimCallCenters.Rationalized

lemma piLam_nonneg (μ lam x : ℝ) (hμ : 0 < μ) (hl : 0 < lam) : 0 ≤ piLam μ lam x := by
  unfold piLam contErlangC
  apply inv_nonneg.2
  apply mul_nonneg (div_pos hl hμ).le
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have : (0:ℝ) < t := ht
  positivity

lemma Glam_nonneg (M : WaitModel) (lam x : ℝ) (hl : 0 < lam) (hx : 0 ≤ x) :
    0 ≤ Glam M lam x := by
  unfold Glam waitCost servers
  apply mul_nonneg hl.le
  apply mul_nonneg
  · have h1 : lam / M.μ * M.μ = lam := div_mul_cancel₀ lam M.hμ.ne'
    have h2 := mul_nonneg (mul_nonneg hx (Real.sqrt_nonneg (lam / M.μ))) M.hμ.le
    nlinarith
  · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht
    apply mul_nonneg _ (Real.exp_pos _).le
    have h0 := M.hD0 lam hl
    have ht' : (0:ℝ) ≤ t := le_of_lt ht
    rw [← h0]
    exact (M.hDmono lam hl).monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht') ht'

lemma Clam_pos (M : WaitModel) (F : ℝ → ℝ) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (lam u : ℝ) (hl : 0 < lam) (hu : 0 < u) : 0 < Clam M F lam u := by
  unfold Clam
  have hF : 0 < Flam F M.μ lam u := by
    unfold Flam servers
    have hα : 0 < lam / M.μ := div_pos hl M.hμ
    have hs : 0 < Real.sqrt (lam / M.μ) := Real.sqrt_pos.2 hα
    have hN : lam / M.μ < lam / M.μ + u * Real.sqrt (lam / M.μ) := by
      have := mul_pos hu hs
      linarith
    exact sub_pos.2 (hFmono hα (lt_trans hα hN) hN)
  exact add_pos_of_pos_of_nonneg hF
    (mul_nonneg (piLam_nonneg M.μ lam u M.hμ hl) (Glam_nonneg M lam u hl hu.le))

end P6ff9d752

open Filter DimCallCenters.EfficiencyDriven in
theorem solution (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (Fh pih Gh : ℝ → ℝ → ℝ) (x z : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F)
    (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hx : IsContinuousOpt M F x)
    (hz : IsSurrogateOpt Fh pih Gh z)
    (happroxX : Tendsto (fun lam =>
      DimCallCenters.Rationalized.Clam M F lam (x lam) /
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) atTop (nhds 1))
    (happroxZ : Tendsto (fun lam =>
      DimCallCenters.Rationalized.Clam M F lam (z lam) /
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) atTop (nhds 1)) :
    Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (z lam) / DimCallCenters.Rationalized.Clam M F lam (x lam))
      atTop (nhds 1) := by
  have hup := happroxZ.mul (happroxX.inv₀ one_ne_zero)
  rw [inv_one, mul_one] at hup
  have ev0 : ∀ᶠ lam : ℝ in atTop, 0 < lam := eventually_gt_atTop 0
  have evZ := happroxZ.eventually (lt_mem_nhds one_pos)
  have evX := happroxX.eventually (lt_mem_nhds one_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [ev0] with lam hl
    have b0 := P6ff9d752.Clam_pos M F hFmono lam (x lam) hl (hx lam hl).1
    have hle := (hx lam hl).2 (z lam) (hz lam hl).1
    exact (one_le_div b0).2 hle
  · filter_upwards [ev0, evZ, evX] with lam hl haA hbB
    have b0 := P6ff9d752.Clam_pos M F hFmono lam (x lam) hl (hx lam hl).1
    have hle := (hx lam hl).2 (z lam) (hz lam hl).1
    have hAB := (hz lam hl).2 (x lam) (hx lam hl).1
    set a := DimCallCenters.Rationalized.Clam M F lam (z lam)
    set b := DimCallCenters.Rationalized.Clam M F lam (x lam)
    set A := DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam)
    set B := DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (x lam)
    have a0 : 0 < a := lt_of_lt_of_le b0 hle
    have A0 : 0 < A := by
      rcases div_pos_iff.mp haA with h | h
      · exact h.2
      · linarith [h.1]
    have B0 : 0 < B := by
      rcases div_pos_iff.mp hbB with h | h
      · exact h.2
      · linarith [h.1]
    show a / b ≤ a / A * (b / B)⁻¹
    rw [inv_div, div_mul_div_comm, div_le_div_iff₀ b0 (mul_pos A0 b0)]
    nlinarith [mul_le_mul_of_nonneg_left hAB (mul_pos a0 b0).le]
