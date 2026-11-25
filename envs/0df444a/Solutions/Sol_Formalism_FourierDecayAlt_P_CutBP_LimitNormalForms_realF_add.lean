-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.realF_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:01:15.557972+00:00
-- url     : https://prove2.me/submissions/1e0d1bc4-485d-43c7-9058-d7372722017f

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd

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
theorem _root_.solution {Φ Ψ : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT}
    (hΦ : RealF P Bs e L o κ Φ) (hΨ : RealF P Bs e L o κ Ψ) : RealF P Bs e L o κ (fun J => Φ J + Ψ J) := by
  obtain ⟨ts, hts, hJ⟩ := hΦ
  obtain ⟨ts', hts', hJ'⟩ := hΨ
  refine ⟨ts ++ ts', fun t ht => ?_, fun J hJJ => ?_⟩
  · rcases List.mem_append.1 ht with h | h
    · exact hts t h
    · exact hts' t h
  · rw [List.map_append, List.sum_append, ← hJ J hJJ, ← hJ' J hJJ]
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
