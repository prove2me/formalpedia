-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.smul_mem_Lw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:10:23.469289+00:00
-- url     : https://prove2.me/submissions/0efb1885-ed36-4dc2-8d11-466fc82b7b94

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_iv_mem_Lw
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PIW_AdelClassFin_DictGen_lf_eq
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
open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedConj0Pf
open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedConj0Pf
theorem _root_.solution {a : 𝓞 I.E} (ha : a ∈ w.asIdeal) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • y ∈ Lw I w := by
  rw [DictGen.lf_eq] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hx
    have e : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • iv I l = iv I ((a : I.E) • l) := by
      funext i; simp [iv, Algebra.smul_def]
    rw [e]
    exact iv_mem_Lw I w (Submodule.subset_span ⟨a, ha, l, hl, rfl⟩)
  | zero => rw [smul_zero]; exact (Lw I w).zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact (Lw I w).add_mem hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, smul_comm, ← Subring.smul_def]
    exact (Lw I w).smul_mem r hx
end Formalism.L2.SG.Pf.RedConj0Pf
