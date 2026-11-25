-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.realF_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:33.733681+00:00
-- url     : https://prove2.me/submissions/7d3ffdca-5d64-4292-841b-2f98cad8b24b

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_actA_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_jdh_actA_listsum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.FourierDecayAlt.P.CutMP
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
variable {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} {L : R.LevelData (MA.A P (MA.DQ P)) P.r} {o κ : ℕ}
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution {b : MA.A P (MA.DQ P)} (hb : b ∈ Submonoid.closure (MA.bddSet P L))
    {Φ : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT} (hΦ : RealF P Bs e L o κ Φ) :
    RealF P Bs e L o κ (fun J => MA.actA P b (Φ J)) := by
  obtain ⟨ts, hts, hJ⟩ := hΦ
  refine ⟨ts.map fun t => (b * t.1, t.2), fun t ht => ?_, fun J hJJ => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨Submonoid.mul_mem _ hb (hts t' ht').1, (hts t' ht').2⟩
  · show MA.actA P b (Φ J) = _
    rw [hJ J hJJ, jdh_actA_listsum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    rw [Gauge.actA_mul]
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
