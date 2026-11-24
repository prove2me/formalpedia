-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.level_integrand_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:49.442232+00:00
-- url     : https://prove2.me/submissions/c6023981-10e3-46a0-8e45-dd65398ea997

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_extension_glue
import Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_extension_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_weight_measurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (hM : TopDensMeas S P z z' π π' μ L st K) (w : List (Letter ℂ S))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K (Fin.last P.r)) x) (hy : InK (K (Fin.last P.r)) y)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) :
    AEStronglyMeasurable (fun q : Cf P.r i × Mt P.k P.r => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      topDens L st w x y (glue i c q.1) (Matrix.of q.2)) (volume.prod μ) := by
  have h0 := hM w x y hx hy c
  have e : (fun q : Cf P.r i × Mt P.k P.r => topDens L st w x y (glue i c q.1) (Matrix.of q.2)) =
      (fun q : Cf P.r 0 × Mt P.k P.r => topDens L st w x y (glue 0 c q.1) (Matrix.of q.2)) ∘
        Prod.map (coordinateExtension i c) id := by
    funext q; simp only [Function.comp, Prod.map, coordinate_extension_glue]; rfl
  have h1 : StronglyMeasurable (fun q : Cf P.r i × Mt P.k P.r => topDens L st w x y (glue i c q.1) (Matrix.of q.2)) := by
    rw [e]; exact h0.comp_measurable ((coordinate_extension_measurable i c).prodMap measurable_id)
  exact (level_weight_measurable i).aestronglyMeasurable.mul h1.aestronglyMeasurable
end Formalism.FourierDecayAlt.P5
