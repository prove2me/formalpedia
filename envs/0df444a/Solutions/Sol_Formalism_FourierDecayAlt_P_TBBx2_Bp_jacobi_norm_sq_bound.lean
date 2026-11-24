-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Bp.jacobi_norm_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:26.905567+00:00
-- url     : https://prove2.me/submissions/b24dbd5c-1fe3-4ed0-8c28-7a9d9e3b8cb2

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Bp
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P.TBBx2.Bp
theorem _root_.solution {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (f F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (n₀ p₀ : ℕ) (hT : 1 ≤ Tq p)
    (h : ∀ c : Fin (P.r + 1) → ℂ, Ew p (fun _ => 1) F (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)) :
    jN2 p F ≤ ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) := by
  have hnn : 0 ≤ (Tq p)⁻¹ ^ n₀ := pow_nonneg (inv_nonneg.mpr (by linarith)) _
  unfold jN2 bigCellDetWeightedEnergyIntegral
  rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply MeasureTheory.lintegral_mono
  intro c
  dsimp only
  rw [← ENNReal.ofReal_mul hnn]
  apply ENNReal.ofReal_le_ofReal
  exact (h c).trans (le_of_eq (by ring))
end Formalism.FourierDecayAlt.P.TBBx2.Bp
