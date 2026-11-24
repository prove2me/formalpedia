-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.rdV_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:15:57.722488+00:00
-- url     : https://prove2.me/submissions/26932093-fcb9-4559-8ca5-4b090ae80563

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresLie_hasDerivAt_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) : RdV X (fun y => L (f y)) g = L (RdV X f g) := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hd := Formalism.FourierDecayAlt.Q.TPresLie.hasDerivAt_ext i X hX f F U g hU hgU hg.1 hF hfF
  have hd2 : HasDerivAt (fun t : ℝ => L (f (g * NormedSpace.exp ((t : ℂ) • X))))
      (L (fderiv ℝ F g (g * X))) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  simp only [RdV]
  rw [hd2.deriv, hd.deriv]
end Formalism.FourierDecayAlt.Q.TPresMain
