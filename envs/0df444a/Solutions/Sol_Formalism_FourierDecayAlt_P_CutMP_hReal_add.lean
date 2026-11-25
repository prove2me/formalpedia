-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.hReal_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:59.232067+00:00
-- url     : https://prove2.me/submissions/d18a9fbd-c27e-44f1-8b19-35ccfc29849d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_actA_add


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
theorem _root_.solution {X Y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X)
    (hY : HReal Cc S T v e L Y) : HReal Cc S T v e L (X + Y) := by
  obtain ⟨ts, hts, hJ⟩ := hX
  obtain ⟨ts', hts', hJ'⟩ := hY
  refine ⟨ts ++ ts', fun t ht => ?_, fun J hJJ => ?_⟩
  · rcases List.mem_append.1 ht with h | h
    · exact hts t h
    · exact hts' t h
  · rw [Gauge.actA_add, hJ J hJJ, hJ' J hJJ, List.map_append, List.sum_append]
end Formalism.FourierDecayAlt.P.CutMP
