-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.redBasis_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:35.924804+00:00
-- url     : https://prove2.me/submissions/9c444a62-c71b-4e0d-b328-b967a140cc65

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_coe_smul
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_mem_iff
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_int_mem_iff
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_RedBasicsPf_mk_sum__ba6933ed2daa
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_finrank_eq
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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {b : Fin I.n → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) (c : Fin I.n → ℤ)
    (hc : ∑ i, (c i : I.E) • b i ∈ wLat0 I w) (i : Fin I.n) : (p : ℤ) ∣ c i := by
  classical
  let v : Fin I.n → RedQ I w := fun i => Submodule.Quotient.mk ⟨b i, hb.1 i⟩
  have hcoe : ∀ d : Fin I.n → ℤ,
      ((∑ i, (d i : 𝓞 I.E) • (⟨b i, hb.1 i⟩ : I.L) : I.L) : Fin I.n → I.E) = ∑ i, (d i : I.E) • b i := by
    intro d
    simp [← coe_smul]
  have hmk : ∀ d : Fin I.n → ℤ, ∑ i, Ideal.Quotient.mk w.asIdeal (d i : 𝓞 I.E) • v i =
      Submodule.Quotient.mk (∑ i, (d i : 𝓞 I.E) • (⟨b i, hb.1 i⟩ : I.L)) := by
    intro d
    rw [mk_sum']
    simp only [v, Module.Quotient.mk_smul_mk]
  have hspan : ⊤ ≤ Submodule.span (𝓞 I.E ⧸ w.asIdeal) (Set.range v) := by
    rintro q -
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨c', hc'⟩ := hb.2 y hy
    have hq : (Submodule.Quotient.mk (⟨y, hy⟩ : I.L) : RedQ I w) =
        ∑ i, Ideal.Quotient.mk w.asIdeal (c' i : 𝓞 I.E) • v i := by
      rw [hmk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero, ← mem_iff,
        Submodule.coe_sub, hcoe]
      exact hc'
    rw [hq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by rw [Fintype.card_fin, finrank_eq])
  have hz : ∑ i, Ideal.Quotient.mk w.asIdeal (c i : 𝓞 I.E) • v i = 0 := by
    rw [hmk, Submodule.Quotient.mk_eq_zero, ← mem_iff, hcoe]
    exact hc
  have h0 := Fintype.linearIndependent_iff.mp hli _ hz i
  rw [Ideal.Quotient.eq_zero_iff_mem, int_mem_iff I w hp hcard] at h0
  exact h0
end Formalism.L2.SG.Pf.RedBasicsPf
