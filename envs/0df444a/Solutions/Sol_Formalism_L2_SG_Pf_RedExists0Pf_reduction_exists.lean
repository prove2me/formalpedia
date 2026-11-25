-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedExists0Pf.reduction_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:28:42.634987+00:00
-- url     : https://prove2.me/submissions/d07937d1-f55d-4215-b3e3-be7b72680253

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ReductionExists
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_coords
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_exists_redBasis
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_inter
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_iv_lin
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_redBasis_indep
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_stab_w
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_val_sub
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PIW_AdelClassFin_DictGen_fmat_inv_mul
import Theorems.Thm_PIW_AdelClassFin_DictGen_iv_mem
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
open scoped TensorProduct Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedExists0Pf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
namespace Formalism.L2.SG.Pf.RedExists0Pf
theorem _root_.solution : Formalism.L2.SG.Pf.RowDictPf.RedExists0 := by
  intro I w p hp hcard m hm x hx
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨b, hb⟩ := exists_redBasis I w hp hcard
  have hx' : ∀ v, v ∈ I.Lf ↔ I.fmat x *ᵥ v ∈ I.Lf := hx
  have hxi : x⁻¹ ∈ I.Kset := (Formalism.UG.stabGL I.Lf).inv_mem hx
  have hxi' : ∀ v, v ∈ I.Lf ↔ I.fmat x⁻¹ *ᵥ v ∈ I.Lf := hxi
  choose c hc using fun i => coords I w hp hcard hb ((hx' _).1 (DictLat.iv_mem I (hb.1 i)))
  choose c' hc' using fun i => coords I w hp hcard hb ((hxi' _).1 (DictLat.iv_mem I (hb.1 i)))
  let M : Matrix (Fin I.n) (Fin I.n) (ZMod p) := Matrix.of fun j i => ((c i j : ℤ) : ZMod p)
  let N : Matrix (Fin I.n) (Fin I.n) (ZMod p) := Matrix.of fun k j => ((c' j k : ℤ) : ZMod p)
  have hzs : ∀ (z : ℤ) {v : Fin I.n → I.E ⊗[I.F] Af I.F}, v ∈ lamAf (F := I.F) (wLat0 I w) →
      (z : I.E ⊗[I.F] Af I.F) • v ∈ lamAf (F := I.F) (wLat0 I w) := fun z v hv => by
    rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hv z
  have hdiv : ∀ i k, (p : ℤ) ∣ (1 : Matrix (Fin I.n) (Fin I.n) ℤ) i k - ∑ j, c i j * c' j k := by
    intro i
    have hW : iv I (b i) - ∑ j, (c i j : I.E ⊗[I.F] Af I.F) •
        ∑ k, (c' j k : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ lamAf (F := I.F) (wLat0 I w) := by
      have h1 := stab_w I w hxi (hc i)
      have h2 : ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ iv I (b j) -
          ∑ k, (c' j k : I.E ⊗[I.F] Af I.F) • iv I (b k)) ∈ lamAf (F := I.F) (wLat0 I w) :=
        Submodule.sum_mem _ fun j _ => hzs _ (hc' j)
      have h3 := Submodule.add_mem _ h1 h2
      convert h3 using 1
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, DictGen.fmat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    have hW2 : iv I (b i - ∑ k, ((∑ j, c i j * c' j k : ℤ) : I.E) • b k) ∈
        lamAf (F := I.F) (wLat0 I w) := by
      rw [iv_lin]
      convert hW using 2
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [← Finset.sum_smul, Int.cast_sum, Int.cast_mul]
    have h4 := inter I w hW2
    intro k
    have h5 : ∑ k, (((1 : Matrix (Fin I.n) (Fin I.n) ℤ) i k - ∑ j, c i j * c' j k : ℤ) : I.E) • b k ∈
        wLat0 I w := by
      convert h4 using 1
      simp only [Int.cast_sub, sub_smul, Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply]
    exact redBasis_indep I w hp hcard hb _ h5 k
  have hNM : N * M = 1 := by
    ext k i
    have h := hdiv i k
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    push_cast at h
    rw [sub_eq_zero] at h
    simp only [N, M, Matrix.mul_apply, Matrix.of_apply]
    have e : ∑ j, ((c' j k : ℤ) : ZMod p) * ((c i j : ℤ) : ZMod p) =
        ∑ j, ((c i j : ℤ) : ZMod p) * ((c' j k : ℤ) : ZMod p) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e, ← h]
    by_cases hik : i = k
    · subst hik; simp
    · simp [Matrix.one_apply_ne hik, Matrix.one_apply_ne (Ne.symm hik)]
  have hMN : M * N = 1 := mul_eq_one_comm.1 hNM
  refine ⟨⟨M, N, hMN, hNM⟩, b, hb, fun i => ?_⟩
  show I.fmat x *ᵥ iv I (b i) - ∑ j, ((((M j i).val : ℕ)) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈
    lamAf (F := I.F) (wLat0 I w)
  have hS : (∑ j, ((((((c i j : ℤ) : ZMod p)).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ((c i j : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j))) ∈ lamAf (F := I.F) (wLat0 I w) :=
    Submodule.sum_mem _ fun j _ => val_sub I w hp hcard (hb.1 j) (c i j)
  have key := Submodule.sub_mem _ (hc i) hS
  convert key using 1
  simp only [M, Matrix.of_apply, Finset.sum_sub_distrib]
  abel
end Formalism.L2.SG.Pf.RedExists0Pf
