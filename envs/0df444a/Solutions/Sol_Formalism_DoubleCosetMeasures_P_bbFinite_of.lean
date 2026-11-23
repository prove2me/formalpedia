-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.bbFinite_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:46.218057+00:00
-- url     : https://prove2.me/submissions/ea16107f-3e81-4a2f-be26-d1b26c9b0906

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isOpen_intSub
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_phi_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : IntTwoSided → IntInv → IsoInv → SimpleAdd → BBFinite := by
  intro hTS hII hIso hSA K _ _ _ R hR s t ψ hψ μ₁ μ₂ _ _ _ _ C _ _ e lam hcs
  have h := hTS (lowW K s t) (upUniG K s.sum) μ₁ μ₂ (intSub R (lowW K s t))
    (intSub R (upUniG K s.sum)) (isOpen_intSub R hR _) (isOpen_intSub R hR _) ℂ
    (phi R s t ψ C e lam) (phi_inv hII hIso hSA R s t ψ hψ C e lam) hcs
  refine ⟨h.1, ?_⟩
  rw [BB, h.2]
  congr 1
end Formalism.DoubleCosetMeasures.P
