-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:03.953244+00:00
-- url     : https://prove2.me/submissions/5606567c-19cd-4086-a0a8-a46b7f694d41

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_comp_mul
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_comp_add
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_val_lt
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_iA_mem
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_iv_OF
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_denomO
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_P2M_PIW_AdelClassFin_lattice_intersection__c78dcf3d0364
import Theorems.Thm_PIW_AdelClassFin_DictGen_iv_mem
import Theorems.Thm_PIW_AdelClassFin_DictRing_af_approx
import Theorems.Thm_PIW_AdelClassFin_DictRing_comp_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z5
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
variable (I : AutInst)
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution (q : HeightOneSpectrum (𝓞 I.F)) {e : Af I.F} (he : e ∈ Formalism.UG.intAd I.F) (he1 : e q = 1)
    (w : Fin I.n → I.E) (hw : iA I e • iv I w ∈ I.Lf) :
    ∃ a : 𝓞 I.F, a ∉ q.asIdeal ∧ algebraMap (𝓞 I.F) (𝓞 I.E) a • w ∈ I.L := by
  obtain ⟨m, hm, hmw⟩ := denomO I w
  have hℓq : ((Ideal.absNorm q.asIdeal : ℕ) : 𝓞 I.F) ∈ q.asIdeal := Ideal.absNorm_mem _
  have hℓ0 : 0 < Ideal.absNorm q.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot)
  set ℓ := Ideal.absNorm q.asIdeal
  obtain ⟨β, y, hy, hβ⟩ := DictRing.af_approx e he (m * ℓ) (Nat.mul_pos hm hℓ0)
  have hy' : ∀ v : HeightOneSpectrum (𝓞 I.F), y v ∈ v.adicCompletionIntegers I.F := hy
  refine ⟨β, fun hβq => ?_, ?_⟩
  · have h1 := congrArg (fun t : Af I.F => t q) hβ
    rw [he1, comp_add, comp_mul, DictRing.comp_algebraMap,
      ← map_natCast (algebraMap (𝓞 I.F) (Af I.F)) (m * ℓ), DictRing.comp_algebraMap] at h1
    have hN : ((m * ℓ : ℕ) : 𝓞 I.F) ∈ q.asIdeal := by
      rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ hℓq
    have hy1 : Valued.v (y q) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 I.F) (K := I.F) (v := q)).1 (hy' q)
    have hlt := Valuation.map_add_lt Valued.v (val_lt hβq)
      (by rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' hy1) (val_lt hN))
    rw [← h1, map_one] at hlt
    exact lt_irrefl _ hlt
  · apply lattice_intersection' I
    rw [iv_OF]
    have hβ' : algebraMap (𝓞 I.F) (Af I.F) β = e - ((m * ℓ : ℕ) : Af I.F) * y := by rw [hβ]; ring
    have key : iA I (algebraMap (𝓞 I.F) (Af I.F) β) • iv I w =
        iA I e • iv I w - iA I ((ℓ : Af I.F) * y) • iv I (algebraMap (𝓞 I.F) (𝓞 I.E) (m : 𝓞 I.F) • w) := by
      rw [hβ', iv_OF, map_sub, sub_smul, smul_smul]
      congr 2
      simp only [map_mul, map_natCast]
      push_cast
      ring
    rw [key]
    exact sub_mem hw (DictLat.Lf_smul I (iA_mem I (mul_mem (natCast_mem _ ℓ) hy)) (DictLat.iv_mem I hmw))
end Formalism.L2.SG.Pf.LatDictZ.Z5
