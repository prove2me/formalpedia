-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.span_of_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:57:13.985188+00:00
-- url     : https://prove2.me/submissions/3cfd387b-40dc-4390-afed-77dd5ff8e371

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_wLat0_eq
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
open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedConj0Pf
open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedConj0Pf
theorem _root_.solution {m : ℕ} {b : Fin m → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) :
    I.L ≤ Submodule.span (𝓞 I.E) (Set.range b) ⊔ w.asIdeal • I.L := by
  intro y hy
  obtain ⟨c, hc⟩ := hb.2 y hy
  rw [← wLat0_eq]
  have hS : ∑ i, (c i : I.E) • b i ∈ Submodule.span (𝓞 I.E) (Set.range b) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : (c i : I.E) • b i = (c i : 𝓞 I.E) • b i := by
      ext j; simp [Algebra.smul_def]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have e : y = ∑ i, (c i : I.E) • b i + (y - ∑ i, (c i : I.E) • b i) := by abel
  rw [e]
  exact Submodule.add_mem_sup hS hc
end Formalism.L2.SG.Pf.RedConj0Pf
