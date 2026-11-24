-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.mp_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:19.483908+00:00
-- url     : https://prove2.me/submissions/603b6031-db85-4095-bd3e-54f6b979f610

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
theorem _root_.solution {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (d : Measure δ) [SFinite a] [SFinite b] [SFinite c] [SFinite d] :
    MeasurePreserving (fun x : (α × β) × (γ × δ) => ((x.2.1, x.1.1), (x.2.2, x.1.2)))
      ((a.prod b).prod (c.prod d)) ((c.prod a).prod (d.prod b)) := by
  have e1 := Measure.measurePreserving_swap (μ := a.prod b) (ν := c.prod d)
  have e2 := measurePreserving_prodAssoc c d (a.prod b)
  have g1 := (measurePreserving_prodAssoc d a b).symm MeasurableEquiv.prodAssoc
  have g2 := (Measure.measurePreserving_swap (μ := d) (ν := a)).prod (MeasurePreserving.id b)
  have g3 := measurePreserving_prodAssoc a d b
  have eg := (MeasurePreserving.id c).prod (g3.comp (g2.comp g1))
  have e4 := (measurePreserving_prodAssoc c a (d.prod b)).symm MeasurableEquiv.prodAssoc
  have := e4.comp (eg.comp (e2.comp e1))
  convert this using 1
  all_goals (funext x; rfl)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
