-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.theta_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:34.746006+00:00
-- url     : https://prove2.me/submissions/15e62dab-def8-4fef-8f2a-9ae0de2bf4ee

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
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis ι E V) (Ψ : Finset (E →+* ℂ)) (M : Submodule (𝓞 E) V)
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (x : ℝ) (v : M) :
    theta b Ψ M (x ⊗ₜ v) = fun (τ : Ψ) i => (x : ℂ) * (τ : E →+* ℂ) (b.repr v i) := by
  ext τ i
  simp [theta, LinearMap.liftBaseChange_tmul, coordO, Complex.real_smul]
end Formalism.L2.Pj.DatLin
