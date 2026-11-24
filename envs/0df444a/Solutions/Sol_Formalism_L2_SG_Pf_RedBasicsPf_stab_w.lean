-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.stab_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:44.099056+00:00
-- url     : https://prove2.me/submissions/dc07c6de-4ac4-42c8-8b9c-b56e12c61e34

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_lamAf_w_le
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_smul_mem
import Theorems.Thm_PIW_AdelClassFin_DictGen_iv_mem


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
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedBasicsPf
theorem _root_.solution {x : I.Gf} (hx : x ∈ I.Kset) {v : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hv : v ∈ lamAf (F := I.F) (wLat0 I w)) : I.fmat x *ᵥ v ∈ lamAf (F := I.F) (wLat0 I w) := by
  have hx' : ∀ u, u ∈ I.Lf ↔ I.fmat x *ᵥ u ∈ I.Lf := hx
  let S : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    (lamAf (F := I.F) (wLat0 I w)).comap ((Matrix.mulVecLin (I.fmat x)).restrictScalars (IntAf I.F I.E))
  refine lamAf_w_le I w S (fun a ha y hy => ?_) hv
  show I.fmat x *ᵥ iv I (((a : 𝓞 I.E) : I.E) • y) ∈ lamAf (F := I.F) (wLat0 I w)
  rw [DictLat.iv_smulE, Matrix.mulVec_smul]
  exact smul_mem I w ha ((hx' _).1 (DictLat.iv_mem I hy))
end Formalism.L2.SG.Pf.RedBasicsPf
