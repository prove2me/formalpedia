-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.mem_wLat0_of_iv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:28.599233+00:00
-- url     : https://prove2.me/submissions/6ef9d38b-b0c5-4cbb-8833-0d619b3d4a5d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_Lw_decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_P2M_PIW_AdelClassFin_lattice_intersection__c78dcf3d0364
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
theorem _root_.solution (p : ℕ) (hp0 : 0 < p) (hpw : (p : 𝓞 I.E) ∈ w.asIdeal) (y : Fin I.n → I.E)
    (hy : iv I y ∈ Lw I w) : y ∈ wLat0 I w := by
  obtain ⟨l, hl, y', hy', he⟩ := Lw_decomp I w p hp0 hy
  have hpE : (p : I.E) ≠ 0 := by exact_mod_cast hp0.ne'
  have hsub : iv I (y - l) = (p : I.E ⊗[I.F] Af I.F) • y' := by
    have e : iv I (y - l) = iv I y - iv I l := by funext i; simp [iv]
    rw [e, he]; abel
  have hu : iv I ((p : I.E)⁻¹ • (y - l)) = y' := by
    have e : iv I ((p : I.E)⁻¹ • (y - l)) =
        Formalism.UG.inclE (F := I.F) (Af I.F) ((p : I.E)⁻¹) • iv I (y - l) := by
      funext i; simp [iv, Algebra.smul_def]
    rw [e, hsub, smul_smul]
    have e2 : Formalism.UG.inclE (F := I.F) (Af I.F) ((p : I.E)⁻¹) * (p : I.E ⊗[I.F] Af I.F) = 1 := by
      rw [← map_natCast (Formalism.UG.inclE (F := I.F) (Af I.F)) p, ← map_mul, inv_mul_cancel₀ hpE, map_one]
    rw [e2, one_smul]
  have huL : (p : I.E)⁻¹ • (y - l) ∈ I.L := lattice_intersection' I _ (hu ▸ hy')
  have hyl : y - l ∈ wLat0 I w := by
    have e : y - l = ((p : 𝓞 I.E) : I.E) • ((p : I.E)⁻¹ • (y - l)) := by
      rw [smul_smul]; push_cast; rw [mul_inv_cancel₀ hpE, one_smul]
    rw [e]
    exact Submodule.subset_span ⟨p, hpw, _, huL, rfl⟩
  have e : y = l + (y - l) := by abel
  rw [e]
  exact (wLat0 I w).add_mem hl hyl
end Formalism.L2.SG.Pf.RedConj0Pf
