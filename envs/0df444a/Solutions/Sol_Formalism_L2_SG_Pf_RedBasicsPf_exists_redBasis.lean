-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.exists_redBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:35.24365+00:00
-- url     : https://prove2.me/submissions/9a5af052-bae0-43c0-888d-0abfc5b47d06

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_coe_smul
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_mem_wLat0_of_mem
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_mem_iff
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_int_surj
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_exists_lift
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_finrank_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_exists_lift
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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) :
    ∃ b : Fin I.n → (Fin I.n → I.E), IsRedBasis0 I w b := by
  classical
  let e : Module.Basis (Fin I.n) (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) :=
    Module.finBasisOfFinrankEq _ _ (finrank_eq I w)
  have hl : ∀ i, ∃ b : I.L, Submodule.Quotient.mk b = e i := fun i => Submodule.Quotient.mk_surjective _ (e i)
  choose b' hb' using hl
  refine ⟨fun i => (b' i : Fin I.n → I.E), fun i => (b' i).2, fun y hy => ?_⟩
  obtain ⟨α, hα⟩ := exists_lift I w ⟨y, hy⟩ e b' hb'
  choose c hc using fun i => int_surj I w hp hcard (Ideal.Quotient.mk w.asIdeal (α i))
  refine ⟨c, ?_⟩
  have h1 : (((⟨y, hy⟩ : I.L) - ∑ i, α i • b' i : I.L) : Fin I.n → I.E) ∈ wLat0 I w := (mem_iff I w _).mpr hα
  have h2 : ∀ i, (((α i : 𝓞 I.E) : I.E) - (c i : I.E)) • (b' i : Fin I.n → I.E) ∈ wLat0 I w := by
    intro i
    have hm : α i - (c i : 𝓞 I.E) ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, hc i, sub_self]
    have := mem_wLat0_of_mem I w hm (b' i).2
    simpa using this
  have key : y - ∑ i, (c i : I.E) • (b' i : Fin I.n → I.E) =
      (((⟨y, hy⟩ : I.L) - ∑ i, α i • b' i : I.L) : Fin I.n → I.E) +
        ∑ i, (((α i : 𝓞 I.E) : I.E) - (c i : I.E)) • (b' i : Fin I.n → I.E) := by
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, ← coe_smul, sub_smul,
      Finset.sum_sub_distrib]
    abel
  rw [key]
  exact Submodule.add_mem _ h1 (Submodule.sum_mem _ fun i _ => h2 i)
end Formalism.L2.SG.Pf.RedBasicsPf
