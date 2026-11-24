-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:26:17.330719+00:00
-- url     : https://prove2.me/submissions/e0fee669-5996-431b-a178-a58db834139f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_add_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_smul_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_add_r
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_smul_r
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_neg_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_X_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_X_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_xiV_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_xiV_apply_last_block_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_nEich_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_neg_r
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_hzz_real
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianXiVector
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) (y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (C2.nEich k r z ξ *ᵥ y) (C2.nEich k r z ξ *ᵥ y') = herm (Hpk k r) y y' := by
  have hH := GBasic.Hpk_herm k r
  have hxx : herm (Hpk k r) (C2.xiV k r ξ) (C2.xiV k r ξ) = 0 :=
    herm_X_left _ _ (xiV_X ξ) (xiV_apply_last_block_zero ξ)
  have hxz : herm (Hpk k r) (C2.xiV k r ξ) z = 0 :=
    herm_X_left _ z (xiV_X ξ) (fun i hi => hz.1 i (Or.inr hi))
  have hzx : herm (Hpk k r) z (C2.xiV k r ξ) = 0 :=
    herm_X_right _ z (xiV_X ξ) (fun i hi => hz.1 i (Or.inr hi))
  have hzz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by rw [hzz_real]; push_cast; ring
  have hxy : herm (Hpk k r) (C2.xiV k r ξ) y' = conj (herm (Hpk k r) y' (C2.xiV k r ξ)) := ggHerm_swap _ hH _ _
  have hzy : herm (Hpk k r) z y' = conj (herm (Hpk k r) y' z) := ggHerm_swap _ hH _ _
  have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz.2.ne'
  have hcc : conj ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := by
    rw [map_div₀, map_one, Complex.conj_ofReal]
  rw [nEich_apply, nEich_apply]
  simp only [herm_add_l, herm_add_r, herm_smul_l, herm_smul_r, herm_neg_l, herm_neg_r, hxx, hxz, hzx, hzz,
    hxy, hzy, hcc, map_neg, map_mul, map_div₀, map_one, map_ofNat]
  set c : ℂ := (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) with hc
  have hcT : c * ((Tz k r z : ℝ) : ℂ) = 1 := by rw [hc]; field_simp
  linear_combination (-(c * herm (Hpk k r) y (C2.xiV k r ξ) * conj (herm (Hpk k r) y' (C2.xiV k r ξ)))) * hcT
end Formalism.FourierDecayAlt.P.HermitianXiVector
