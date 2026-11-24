-- Prove2me | solution 1 for Formalism.L2.Pj.lawA13_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:18.507869+00:00
-- url     : https://prove2.me/submissions/a51af1b1-6a0d-4682-81e6-7b11fe8bde1f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LawA13OfContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MeasureTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))
namespace Formalism.L2.Pj
theorem _root_.solution (hc : A13ContinuousOffNull d) : A13Measurable d := by
  intro Z sg G f hf hf0
  obtain ⟨S, hSm, hS0, hcont⟩ := hc Z sg hf hf0
  have h1 := hcont.aemeasurable (μ := d.sphMeasure) hSm.compl
  have h2 : d.sphMeasure.restrict Sᶜ = d.sphMeasure :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 hS0)
  rw [h2] at h1
  exact h1
end Formalism.L2.Pj
