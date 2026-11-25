-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.hReal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:56:13.714139+00:00
-- url     : https://prove2.me/submissions/af3642bc-9318-4916-86b2-effa8f5b012f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_jdh_actA_listsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_actA_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cc : ℝ} {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
  {v : Fin S.f} {e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
  {L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r}
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution {b X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))}
    (hb : b ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L)) (hX : HReal Cc S T v e L X) :
    HReal Cc S T v e L (b * X) := by
  obtain ⟨ts, hts, hJ⟩ := hX
  refine ⟨ts.map fun t => (b * t.1, t.2), fun t ht => ?_, fun J hJJ => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨Submonoid.mul_mem _ hb (hts t' ht').1, (hts t' ht').2⟩
  · rw [Gauge.actA_mul, hJ J hJJ, jdh_actA_listsum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    rw [Gauge.actA_mul]
end Formalism.FourierDecayAlt.P.CutMP
