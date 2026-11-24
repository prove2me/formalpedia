-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.measurePreserving_pi_comp_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:38.867418+00:00
-- url     : https://prove2.me/submissions/ad5a0d89-3314-461d-989d-96101798bdeb

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {α β γ δ : Type*} [MeasureSpace α] [MeasureSpace β] [MeasureSpace γ]
    [MeasureSpace δ] [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)]
    [SigmaFinite (volume : Measure γ)] [SigmaFinite (volume : Measure δ)] (r : ℕ) (f : α → β)
    (g : β → γ × δ) (hf : MeasurePreserving f) (hg : MeasurePreserving g) :
    MeasurePreserving (fun a : Fin r → α =>
      ((fun b => (g (f (a b))).1), (fun b => (g (f (a b))).2))) volume volume := by
  have h1 := volume_preserving_pi (fun _ : Fin r => hf)
  have h2 := volume_preserving_pi (fun _ : Fin r => hg)
  have h3 := volume_measurePreserving_arrowProdEquivProdArrow γ δ (Fin r)
  exact h3.comp (h2.comp h1)
end Formalism.HermitianLatticeCounting.P
