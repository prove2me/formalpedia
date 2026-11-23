-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGeLe_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:05.640382+00:00
-- url     : https://prove2.me/submissions/5675a339-a1b1-4297-9c25-c4a1bc313567

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormNatCastEqOneOfNotDvd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_multiplicative_weight_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v} {pi : ℝ}
    (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {κ : ι →₀ ℕ} {f : MvPowerSeries ι K}
    (hf : WtGeLe pi r wt κ f) (k : ℕ) : WtGeLe pi r (k * wt) κ (f ^ k) := by
  induction k with
  | zero =>
    intro n _
    simpa using wtGe_one (K := K) h0 r n
  | succ k ih =>
    rw [pow_succ]
    have := multiplicative_weight_le K pi h0 ι r _ _ κ _ _ ih hf
    push_cast
    rwa [add_mul, one_mul]
end Formalism.DworkPowerSeriesWeights
