-- Prove2me | solution 1 for Formalism.L2.SG.Pf.SatGramLoc.rc_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:38.812744+00:00
-- url     : https://prove2.me/submissions/2db7616d-2ea8-4457-94b7-9e7f37662206

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.SG.Pf.SatGramLoc
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) = Module.finrank F E := by
  let e : (v.adicCompletion F ⊗[F] E) ≃ₗ[v.adicCompletion F] (E ⊗[F] v.adicCompletion F) :=
    { TensorProduct.comm F (v.adicCompletion F) E with
      map_smul' := fun a x => by
        show TensorProduct.comm F _ _ (a • x) = a • TensorProduct.comm F _ _ x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b y =>
          rw [TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul]
          first
          | (show y ⊗ₜ[F] (a • b) = (1 ⊗ₜ[F] a) * (y ⊗ₜ[F] b)
             rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul])
          | (rw [Algebra.smul_def]
             show y ⊗ₜ[F] (a • b) = (1 ⊗ₜ[F] a) * (y ⊗ₜ[F] b)
             rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul])
          | (simp [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]; done)
        | add x y hx hy =>
          rw [smul_add, map_add, map_add, hx, hy, smul_add] }
  rw [← e.finrank_eq, Module.finrank_baseChange]
end Formalism.L2.SG.Pf.SatGramLoc
