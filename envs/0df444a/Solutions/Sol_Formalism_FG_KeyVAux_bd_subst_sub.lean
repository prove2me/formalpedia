-- Prove2me | solution 1 for Formalism.FG.KeyVAux.bd_subst_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:40.39049+00:00
-- url     : https://prove2.me/submissions/6229557d-30a1-4058-b5c9-c8d08d14a396

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Theorems.Thm_Formalism_FG_KeyVAux_norm_finsum_le
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_finsum_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.KeyVAux
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.KeyVAux
theorem _root_.solution {ι : Type v} {τ : Type w} (φ : MvPowerSeries ι K)
    (A B : ι → MvPowerSeries τ K) (hA : MvPowerSeries.HasSubst A) (hB : MvPowerSeries.HasSubst B)
    {c : ℝ} (hc : 0 ≤ c)
    (H : ∀ (n : ι →₀ ℕ) d, ‖MvPowerSeries.coeff n φ‖ *
      ‖MvPowerSeries.coeff d (n.prod (fun s e => A s ^ e) - n.prod (fun s e => B s ^ e))‖ ≤ c) :
    Bd c (MvPowerSeries.subst A φ - MvPowerSeries.subst B φ) := by
  intro d
  rw [map_sub, MvPowerSeries.coeff_subst hA, MvPowerSeries.coeff_subst hB,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hA φ d)
      (MvPowerSeries.coeff_subst_finite hB φ d)]
  apply norm_finsum_le hc
  intro n
  rw [← smul_sub, ← map_sub, smul_eq_mul, norm_mul]
  exact H n d
end Formalism.FG.KeyVAux
