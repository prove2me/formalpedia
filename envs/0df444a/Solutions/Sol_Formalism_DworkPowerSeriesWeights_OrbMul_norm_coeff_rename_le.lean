-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OrbMul.norm_coeff_rename_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:45.711916+00:00
-- url     : https://prove2.me/submissions/09c9dcc4-a302-4cf8-a626-9812398e9cd5

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OrbMul
variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ₁ σ₂ : Type}
namespace Formalism.DworkPowerSeriesWeights.OrbMul
theorem _root_.solution {σ τ : Type} (e : σ → τ) (he : Function.Injective e)
    (A : MvPolynomial σ K) {B : ℝ} (hA : ∀ n, ‖MvPolynomial.coeff n A‖ ≤ B) (n : τ →₀ ℕ) :
    ‖MvPolynomial.coeff n (MvPolynomial.rename e A)‖ ≤ B := by
  by_cases hn : ∃ u : σ →₀ ℕ, u.mapDomain e = n
  · obtain ⟨u, rfl⟩ := hn
    rw [MvPolynomial.coeff_rename_mapDomain e he]
    exact hA u
  · rw [MvPolynomial.coeff_rename_eq_zero e A n fun u hu => absurd ⟨u, hu⟩ hn, norm_zero]
    exact le_trans (norm_nonneg _) (hA 0)
end Formalism.DworkPowerSeriesWeights.OrbMul
