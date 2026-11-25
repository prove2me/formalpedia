-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxG.betaBig_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:01:08.002683+00:00
-- url     : https://prove2.me/submissions/08e2b79a-008e-42eb-a2ac-271044fec002

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RadialAdjointOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_bcWeight_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_big_cell_orbit_set


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JFxG
theorem _root_.solution (D : RealPlaceData k r Wp Wq)
    {J₁ J₁' J₂ J₂' : Mat k r → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)}
    (h : ∀ g ∈ Om k r D.z D.z', J₁ g = J₂ g) (h' : ∀ g ∈ Om k r D.z D.z', J₁' g = J₂' g) :
    betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec J₁ J₁' = betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec J₂ J₂' := by
  unfold betaBig
  apply integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ Om k r D.z D.z' := hq hQ
    simp only [h _ hg, h' _ hg]
  · have h0 : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (bcWeight_nonneg _ _ q)
    simp only [h0, Complex.ofReal_zero, zero_mul]
end Formalism.FourierDecayAlt.P.JFxG
