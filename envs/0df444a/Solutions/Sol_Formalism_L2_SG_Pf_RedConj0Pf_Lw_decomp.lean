-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.Lw_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:17.797341+00:00
-- url     : https://prove2.me/submissions/d38c6776-2e1b-471c-889c-4562a411fc9b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_wLat0_le
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PIW_AdelClassFin_DictGen_iv_mem
import Theorems.Thm_PIW_AdelClassFin_dual_dense
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
theorem _root_.solution (p : ℕ) (hp0 : 0 < p) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ Lw I w) :
    ∃ l ∈ wLat0 I w, ∃ y ∈ I.Lf, z = iv I l + (p : I.E ⊗[I.F] Af I.F) • y := by
  have hz' : z ∈ Submodule.span (IntAf I.F I.E)
      (Set.range fun x : wLat0 I w => iv I (x : Fin I.n → I.E)) := hz
  clear hz
  induction hz' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hx
    exact ⟨l, hl, 0, I.Lf.zero_mem, by rw [smul_zero, add_zero]⟩
  | zero => exact ⟨0, (wLat0 I w).zero_mem, 0, I.Lf.zero_mem, by rw [DictLat.iv_zero, smul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, hl, a, ha, rfl⟩ := hx
    obtain ⟨m, hm, b, hb, rfl⟩ := hy
    exact ⟨l + m, (wLat0 I w).add_mem hl hm, a + b, I.Lf.add_mem ha hb,
      by rw [DictLat.iv_add, smul_add]; abel⟩
  | smul r x _ hx =>
    obtain ⟨l, hl, a, ha, rfl⟩ := hx
    obtain ⟨c, r', hr', hr⟩ := dual_dense I.F I.E p hp0 r.1 r.2
    have hlL : iv I l ∈ I.Lf := DictGen.iv_mem I (wLat0_le I w hl)
    refine ⟨c • l, (wLat0 I w).smul_mem c hl, (⟨r', hr'⟩ : IntAf I.F I.E) • iv I l + r • a,
      I.Lf.add_mem (I.Lf.smul_mem _ hlL) (I.Lf.smul_mem r ha), ?_⟩
    have e1 : iv I (c • l) = Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) • iv I l := by
      funext i; simp [iv, Algebra.smul_def]
    rw [e1]
    simp only [Subring.smul_def]
    rw [hr]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
end Formalism.L2.SG.Pf.RedConj0Pf
