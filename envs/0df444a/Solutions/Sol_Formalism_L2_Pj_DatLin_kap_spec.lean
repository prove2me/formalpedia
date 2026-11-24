-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.kap_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:15:40.615244+00:00
-- url     : https://prove2.me/submissions/2b932ad0-c39d-4648-975c-9db0dc54e015

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
variable {Ψ}
variable {b M}
variable (b M)
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (s : 𝓞 E) (hs) (v : M) (i : ι) :
    algebraMap (𝓞 E) E (kap b M s hs v i) = algebraMap (𝓞 E) E s * b.repr v i :=
  kapF_spec b M s hs v i
end Formalism.L2.Pj.DatLin
