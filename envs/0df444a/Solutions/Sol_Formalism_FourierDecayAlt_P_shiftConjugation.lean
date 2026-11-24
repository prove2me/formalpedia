-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.shiftConjugation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:14.718062+00:00
-- url     : https://prove2.me/submissions/2cbaeaf1-6a20-4057-b817-f0804f90e96e

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_alg
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_of_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_fc
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_ci
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_cb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_cbi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleGD_m___020c678e767a
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleGD_m__i_0b1ea39e3534
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleGD_m__b_202003117e66
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleGD_m__bi_812628c5ee53
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_GGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_keyA
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_keyV
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_commA
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_commV
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_Dr_Dri
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_Dri_Dr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_Drb_Drbi
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_Drbi_Drb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_comm_Dr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_comm_Drb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_fns_Dr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_fns_Drb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_p_Dr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_pb_Drb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.R.RuleD := by
  intro A _ _ r L Y

  set ψ1 := cj L.Dr L.Dri (Dr_Dri L) (Dri_Dr L)
  set ψ2 := cj L.ζ L.ζi L.ζ_ζi L.ζi_ζ
  have hφ : ∀ x, (ψ2.comp ψ1) x = L.Di * x * L.D := by
    intro x; simp only [ψ1, ψ2, RingHom.comp_apply, cj_apply, LevelData.Di, LevelData.D, mul_assoc]
  have f1 : ∀ x ∈ L.fns, ψ1 x = x := fun x hx => cj_fix _ _ _ _ (fns_Dr L hx)
  have f2 : ∀ x ∈ L.fns, ψ2 x = x := fun x hx => cj_fix _ _ _ _ (fc L hx (m_ζ L))
  have f12 : ∀ x ∈ L.fns, (ψ2.comp ψ1) x = x := fun x hx => by
    rw [RingHom.comp_apply, f1 x hx, f2 x hx]
  have hal : ∀ z, (ψ2.comp ψ1) (algebraMap ℂ A z) = algebraMap ℂ A z := fun z => by
    rw [RingHom.comp_apply, cj_alg, cj_alg]
  have hp : ∀ l, (ψ2.comp ψ1) (L.p l) = L.p l + algebraMap ℂ A 1 := fun l => by
    rw [RingHom.comp_apply, cj_of_eq _ _ _ _ (p_Dr L l), map_one, map_add, map_one,
      cj_fix _ _ _ _ (L.p_ζ l), map_one]
  have hnab : (ψ2.comp ψ1) L.nab = L.nab + algebraMap ℂ A 1 * (L.ζb * L.GGi)
      - (L.ζb * L.GGi - L.ζi) := by
    have e1 : ψ1 L.nab = L.nab := cj_fix _ _ _ _ (comm_Dr L L.nab_c)
    have e2 : ψ2 L.nab = L.nab + L.ζi := by
      rw [cj_of_eq _ _ _ _ (a := L.ζi) (by rw [L.nab_ζ, L.ζi_ζ]), f2 _ (m_ζi L)]
    rw [RingHom.comp_apply, e1, e2, map_one, one_mul]
    abel
  obtain ⟨a1, a2⟩ := keyA L (ψ2.comp ψ1) 1 (L.ζb * L.GGi - L.ζi) hal hp
    (fun l => f12 _ (m_c L l)) (fun l => f12 _ (m_ci L l)) (fun l => f12 _ (m_cb L l))
    (f12 _ (m_GG L)) (f12 _ (m_ζb L)) (f12 _ (m_GGi L)) hnab Y
  rw [hφ] at a1 a2

  set χ1 := cj L.Drb L.Drbi (Drb_Drbi L) (Drbi_Drb L)
  set χ2 := cj L.ζb L.ζbi L.ζb_ζbi L.ζbi_ζb
  have hχ : ∀ x, (χ2.comp χ1) x = L.Dbi * x * L.Db := by
    intro x; simp only [χ1, χ2, RingHom.comp_apply, cj_apply, LevelData.Dbi, LevelData.Db, mul_assoc]
  have g1 : ∀ x ∈ L.fns, χ1 x = x := fun x hx => cj_fix _ _ _ _ (fns_Drb L hx)
  have g2 : ∀ x ∈ L.fns, χ2 x = x := fun x hx => cj_fix _ _ _ _ (fc L hx (m_ζb L))
  have g12 : ∀ x ∈ L.fns, (χ2.comp χ1) x = x := fun x hx => by
    rw [RingHom.comp_apply, g1 x hx, g2 x hx]
  have hal' : ∀ z, (χ2.comp χ1) (algebraMap ℂ A z) = algebraMap ℂ A z := fun z => by
    rw [RingHom.comp_apply, cj_alg, cj_alg]
  have hpb : ∀ l, (χ2.comp χ1) (L.pb l) = L.pb l + algebraMap ℂ A 1 := fun l => by
    rw [RingHom.comp_apply, cj_of_eq _ _ _ _ (pb_Drb L l), map_one, map_add, map_one,
      cj_fix _ _ _ _ (L.pb_ζb l), map_one]
  have hnabs : (χ2.comp χ1) L.nabs = L.nabs - algebraMap ℂ A 1 * (L.ζ * L.GGi)
      - (L.ζbi - L.ζ * L.GGi) := by
    have e1 : χ1 L.nabs = L.nabs := cj_fix _ _ _ _ (comm_Drb L L.nabs_cb)
    have e2 : χ2 L.nabs = L.nabs + -L.ζbi := by
      rw [cj_of_eq _ _ _ _ (a := -L.ζbi) (by rw [L.nabs_ζb, neg_mul, L.ζbi_ζb, sub_eq_add_neg]), map_neg, g2 _ (m_ζbi L)]
    rw [RingHom.comp_apply, e1, e2, map_one, one_mul]
    abel
  obtain ⟨b1, b2⟩ := keyV L (χ2.comp χ1) 1 (L.ζbi - L.ζ * L.GGi) hal' hpb
    (fun l => g12 _ (m_cb L l)) (fun l => g12 _ (m_cbi L l)) (fun l => g12 _ (m_c L l))
    (g12 _ (m_GG L)) (g12 _ (m_ζ L)) (g12 _ (m_GGi L)) hnabs Y
  rw [hχ] at b1 b2

  have s1 : L.GG * (L.ζb * L.GGi - L.ζi) = algebraMap ℂ A L.TT * L.ζi := by
    rw [mul_sub, ← mul_assoc, fc L (m_GG L) (m_ζb L), mul_assoc, L.GG_GGi, mul_one, L.GG_def,
      sub_mul, mul_assoc, fc L (m_ζb L) (m_ζi L), ← mul_assoc, L.ζ_ζi, one_mul, sub_sub_cancel]
  have s2 : L.GG * (L.ζbi - L.ζ * L.GGi) = -(algebraMap ℂ A L.TT * L.ζbi) := by
    rw [mul_sub, ← mul_assoc, fc L (m_GG L) (m_ζ L), mul_assoc, L.GG_GGi, mul_one, L.GG_def,
      sub_mul, mul_assoc, L.ζb_ζbi, mul_one, sub_sub_cancel_left]
  have t1 : L.Drb * L.GG * (L.ζb * L.GGi - L.ζi) * L.Ar (Y + 1)
      = algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y + 1)) := by
    rw [mul_assoc L.Drb, s1, LevelData.Di, LevelData.Ahat]
    have h3 : L.Drb * (L.ζi * L.Dri) * (L.Dr * L.Ar (Y + 1)) = L.Drb * (L.ζi * L.Ar (Y + 1)) := by
      simp only [mul_assoc]; rw [← mul_assoc L.Dri, Dri_Dr, one_mul]
    rw [h3, Algebra.left_comm]; simp only [mul_assoc]
  have t2 : L.Dr * L.GG * (L.ζbi - L.ζ * L.GGi) * L.Avr (Y - 1)
      = -(algebraMap ℂ A L.TT * (L.Dr * L.Dbi * L.Ahatv (Y - 1))) := by
    rw [mul_assoc L.Dr, s2, LevelData.Dbi, LevelData.Ahatv]
    have h3 : L.Dr * (L.ζbi * L.Drbi) * (L.Drb * L.Avr (Y - 1)) = L.Dr * (L.ζbi * L.Avr (Y - 1)) := by
      simp only [mul_assoc]; rw [← mul_assoc L.Drbi, Drbi_Drb, one_mul]
    rw [h3, mul_neg, neg_mul, Algebra.left_comm]; simp only [mul_assoc]
  refine ⟨a1, a2.trans (by rw [t1]), b1, b2.trans (by rw [t2]; exact (sub_eq_add_neg _ _).symm), ?_, ?_⟩
  · rintro x ((⟨l, rfl⟩ | ⟨l, rfl⟩) | rfl | rfl)
    · exact commA L _ _ (L.cb_cbi l) (L.cbi_cb l) (fun m => L.p_cb m l)
        (fun y hy => fc L hy (m_cb L l)) (L.nab_cb l) Y
    · exact commA L _ _ (L.cbi_cb l) (L.cb_cbi l) (fun m => L.p_cbi m l)
        (fun y hy => fc L hy (m_cbi L l)) (L.nab_cbi l) Y
    · exact commA L _ _ L.ζb_ζbi L.ζbi_ζb (fun m => L.p_ζb m)
        (fun y hy => fc L hy (m_ζb L)) L.nab_ζb Y
    · exact commA L _ _ L.ζbi_ζb L.ζb_ζbi (fun m => L.p_ζbi m)
        (fun y hy => fc L hy (m_ζbi L)) L.nab_ζbi Y
  · rintro x ((⟨l, rfl⟩ | ⟨l, rfl⟩) | rfl | rfl)
    · exact commV L _ _ (L.c_ci l) (L.ci_c l) (fun m => L.pb_c m l)
        (fun y hy => fc L hy (m_c L l)) (L.nabs_c l) Y
    · exact commV L _ _ (L.ci_c l) (L.c_ci l) (fun m => L.pb_ci m l)
        (fun y hy => fc L hy (m_ci L l)) (L.nabs_ci l) Y
    · exact commV L _ _ L.ζ_ζi L.ζi_ζ (fun m => L.pb_ζ m)
        (fun y hy => fc L hy (m_ζ L)) L.nabs_ζ Y
    · exact commV L _ _ L.ζi_ζ L.ζ_ζi (fun m => L.pb_ζi m)
        (fun y hy => fc L hy (m_ζi L)) L.nabs_ζi Y
end Formalism.FourierDecayAlt.P
