-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.threeDimData_schurH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:53.608047+00:00
-- url     : https://prove2.me/submissions/0758b141-327d-408a-b746-9be98cec1e82

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_iota_measEmb
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_exists_map_iota
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_toURep_irred
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_isURepOn_of_ds
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_isIrredOn_of_ds
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_memLp_of_ds
import Theorems.Thm_CompanionTheory_LimBd_URep_schur_orthogonality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
namespace CompanionTheory.LimBd.SchurHpk
theorem _root_.solution : Formalism.FourierDecayAlt.ThreeDimData.SchurH := by
  intro k r ε lam H _ _ _ σ μG _ hds hμ
  have hU := isURepOn_of_ds hds
  have hI := isIrredOn_of_ds hds
  have hL := memLp_of_ds hds hμ
  obtain ⟨P, ⟨hP, -⟩, -, hnt, -⟩ := hds
  obtain ⟨c, hc0, hcT, e⟩ := exists_map_iota hP hμ
  have : (c • muG ε).IsHaarMeasure := Measure.IsHaarMeasure.smul _ hc0 hcT
  have hsq : SqInt (c • muG ε) (toURep hP σ hU) := fun v w => by
    have := hL v w
    rw [e, (iota_measEmb hP).memLp_map_measure_iff] at this
    exact this
  obtain ⟨d, hd, h⟩ := schur_orthogonality (toURep_irred hP σ hU hI) hsq
  refine ⟨d, hd, fun v w v' w' => ⟨(hL v w).integrable_mul (hL v' w').star, ?_⟩⟩
  rw [e, (iota_measEmb hP).integral_map]
  exact h v w v' w'
end CompanionTheory.LimBd.SchurHpk
