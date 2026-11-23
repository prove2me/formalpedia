-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.phi1_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:51.956456+00:00
-- url     : https://prove2.me/submissions/f31e1556-8e1d-4d11-8eb5-c20d726d6e74

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable (Ψ : Finset (E →+* ℂ))
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (x : ℝ) (e : 𝓞 E) :
    phi1 Ψ (x ⊗ₜ e) = fun τ : Ψ => (x : ℂ) * (τ : E →+* ℂ) (e : E) := by
  ext τ
  simp [phi1, LinearMap.liftBaseChange_tmul, embO, Complex.real_smul]
end Formalism.L2.Pj.DatLin
