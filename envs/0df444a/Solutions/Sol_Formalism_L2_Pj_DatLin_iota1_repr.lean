-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.iota1_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:15:37.342953+00:00
-- url     : https://prove2.me/submissions/66179a4d-0bfc-4831-9e0f-ef8f4fe9a162

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
theorem _root_.solution (s' : 𝓞 E) (hs') (n : ι → 𝓞 E) (i : ι) :
    b.repr (iota1 b M s' hs' n) i = algebraMap (𝓞 E) E (n i) * algebraMap (𝓞 E) E s' := by
  have e : ((iota1 b M s' hs' n : M) : V) =
      ∑ k, (algebraMap (𝓞 E) E (n k) * algebraMap (𝓞 E) E s') • b k := by
    simp only [iota1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, ← map_mul, algebraMap_smul]
  rw [e, b.repr_sum_self]
end Formalism.L2.Pj.DatLin
