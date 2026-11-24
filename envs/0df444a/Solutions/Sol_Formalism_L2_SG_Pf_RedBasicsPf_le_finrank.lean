-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:36.543552+00:00
-- url     : https://prove2.me/submissions/a8264f8d-8210-4ae4-80d0-c915ddd1e609

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_coe_smul
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_wLat0_eq
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_mem_iff
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_exists_lift
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
theorem _root_.solution : I.n ≤ Module.finrank (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) := by
  let e := Module.finBasis (𝓞 I.E ⧸ w.asIdeal) (RedQ I w)
  choose b' hb' using fun i => Submodule.Quotient.mk_surjective _ (e i)
  let N : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
    Submodule.span (𝓞 I.E) (Set.range fun i => (b' i : Fin I.n → I.E))
  have hsup : I.L ≤ N ⊔ w.asIdeal • I.L := by
    intro y hy
    obtain ⟨α, hα⟩ := exists_lift I w ⟨y, hy⟩ e b' hb'
    rw [← mem_iff, wLat0_eq] at hα
    have hsum : (((∑ i, α i • b' i : I.L)) : Fin I.n → I.E) ∈ N := by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have : y = ((∑ i, α i • b' i : I.L) : Fin I.n → I.E) +
        (((⟨y, hy⟩ : I.L) - ∑ i, α i • b' i : I.L) : Fin I.n → I.E) := by
      rw [Submodule.coe_sub]; abel
    rw [this]
    exact Submodule.add_mem_sup hsum hα
  obtain ⟨r, hr1, hrL⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup I.L_fg le_rfl hsup
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using w.asIdeal.neg_mem hr1
  have hrE : ((r : 𝓞 I.E) : I.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hr0
  have hspan : Submodule.span I.E (Set.range fun i => (b' i : Fin I.n → I.E)) = ⊤ := by
    rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    intro y hy
    have hry : r • y ∈ N := hrL (Submodule.smul_mem_pointwise_smul y r I.L hy)
    have h2 : r • y ∈ Submodule.span I.E (Set.range fun i => (b' i : Fin I.n → I.E)) :=
      Submodule.span_le_restrictScalars (𝓞 I.E) I.E _ hry
    have h3 : y = ((r : 𝓞 I.E) : I.E)⁻¹ • (r • y) := by
      rw [← coe_smul, smul_smul, inv_mul_cancel₀ hrE, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ h2
  have h := finrank_range_le_card (R := I.E) (fun i => (b' i : Fin I.n → I.E))
  rw [Set.finrank, hspan, finrank_top, Module.finrank_fin_fun] at h
  simpa using h
end Formalism.L2.SG.Pf.RedBasicsPf
