-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:29:50.414645+00:00
-- url     : https://prove2.me/submissions/a6f70441-a3d1-4a82-b537-d2bef32a3970

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.L2.Host.restr_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedBasicsPf
theorem _root_.solution : Module.finrank (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) ≤ I.n := by
  let e := Module.finBasis (𝓞 I.E ⧸ w.asIdeal) (RedQ I w)
  choose b' hb' using fun i => Submodule.Quotient.mk_surjective _ (e i)
  have hli : LinearIndependent (𝓞 I.E ⧸ w.asIdeal)
      (Submodule.mkQ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) ∘ b') := by
    have : (Submodule.mkQ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) ∘ b') = ⇑e := funext fun i => hb' i
    rw [this]; exact e.linearIndependent
  have hker : RingHom.ker (algebraMap (𝓞 I.E) (𝓞 I.E ⧸ w.asIdeal)) ≠ ⊤ := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact w.isPrime.ne_top
  have h := Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (K := I.E) (V := Fin I.n → I.E) hker
    I.L.subtype Subtype.val_injective _ hli
  have h2 := h.fintype_card_le_finrank
  simpa using h2
end Formalism.L2.SG.Pf.RedBasicsPf
