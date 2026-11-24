-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.tuo_smulRight_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:13.110804+00:00
-- url     : https://prove2.me/submissions/fcf9fb36-82b8-4f40-9275-e1b6e37cd346

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {𝔤 E : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {Ω : Set 𝔤} (a : ι → 𝔤 → (𝔤 →L[ℝ] ℝ)) (B : ℝ) (hB : ∀ i, ∀ Y ∈ Ω, ‖a i Y‖ ≤ B)
    (Ψ : ι → ℕ → 𝔤 → E) (L : ι → 𝔤 → E) (h : ∀ i, TendstoUniformlyOn (Ψ i) (L i) atTop Ω) :
    TendstoUniformlyOn (fun n Y => ∑ i, (a i Y).smulRight (Ψ i n Y))
      (fun Y => ∑ i, (a i Y).smulRight (L i Y)) atTop Ω := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set B' := max B 1 with hB'def
  have hB' : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set N : ℝ := (Fintype.card ι : ℝ) + 1 with hNdef
  have hN : 0 < N := by positivity
  have hη : 0 < ε / (B' * N) := by positivity
  have hev : ∀ᶠ n in atTop, ∀ i, ∀ Y ∈ Ω, dist (L i Y) (Ψ i n Y) < ε / (B' * N) := by
    rw [Filter.eventually_all]
    intro i
    exact (Metric.tendstoUniformlyOn_iff.1 (h i)) _ hη
  filter_upwards [hev] with n hn Y hY
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ i, ((a i Y).smulRight (L i Y) - (a i Y).smulRight (Ψ i n Y))‖
      ≤ ∑ i, ‖(a i Y).smulRight (L i Y) - (a i Y).smulRight (Ψ i n Y)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, B' * (ε / (B' * N)) := by
        apply Finset.sum_le_sum
        intro i _
        have e : (a i Y).smulRight (L i Y) - (a i Y).smulRight (Ψ i n Y) =
            (a i Y).smulRight (L i Y - Ψ i n Y) := by
          ext v; simp [smul_sub]
        rw [e, ContinuousLinearMap.norm_smulRight_apply]
        have h1 := hn i Y hY
        rw [dist_eq_norm] at h1
        exact mul_le_mul (le_trans (hB i Y hY) (le_max_left _ _)) h1.le (norm_nonneg _) hB'.le
    _ = (Fintype.card ι : ℝ) * (ε / N) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hN, hNdef]; nlinarith
end Formalism.FourierDecayAlt.P.Ux1
