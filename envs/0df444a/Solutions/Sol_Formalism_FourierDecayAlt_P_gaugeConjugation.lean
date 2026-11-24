-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gaugeConjugation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:42.918993+00:00
-- url     : https://prove2.me/submissions/63e49274-2bee-4098-81a9-7f667f7d0463

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_alg
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_of_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_ci
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_cb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_cbi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleGD_m___020c678e767a
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleGD_m__b_202003117e66
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_GGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_keyA
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_keyV

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
theorem _root_.solution : Formalism.FourierDecayAlt.R.RuleG := by
  intro A _ _ r L s Gs Gsi h1 h2 hf hp hpb hnab hnabs Y
  have hfx : ∀ x ∈ L.fns, cj Gs Gsi h1 h2 x = x := fun x hx => cj_fix Gs Gsi h1 h2 (hf x hx)
  have hpφ : ∀ l, cj Gs Gsi h1 h2 (L.p l) = L.p l + algebraMap ℂ A s := by
    intro l; rw [cj_of_eq Gs Gsi h1 h2 (hp l), cj_alg]
  have hpbφ : ∀ l, cj Gs Gsi h1 h2 (L.pb l) = L.pb l + algebraMap ℂ A s := by
    intro l; rw [cj_of_eq Gs Gsi h1 h2 (hpb l), cj_alg]
  have hnabφ : cj Gs Gsi h1 h2 L.nab = L.nab + algebraMap ℂ A s * (L.ζb * L.GGi) - 0 := by
    rw [sub_zero, cj_of_eq Gs Gsi h1 h2 (a := algebraMap ℂ A s * (L.ζb * L.GGi))
      (by rw [hnab]; simp only [mul_assoc]), map_mul, map_mul, cj_alg, hfx _ (m_ζb L),
      hfx _ (m_GGi L)]
  have hnabsφ : cj Gs Gsi h1 h2 L.nabs = L.nabs - algebraMap ℂ A s * (L.ζ * L.GGi) - 0 := by
    rw [sub_zero, cj_of_eq Gs Gsi h1 h2 (a := -(algebraMap ℂ A s * (L.ζ * L.GGi)))
      (by rw [hnabs, sub_eq_add_neg, neg_mul]; simp only [mul_assoc]), map_neg, map_mul,
      map_mul, cj_alg, hfx _ (m_ζ L), hfx _ (m_GGi L), sub_eq_add_neg]
  obtain ⟨a1, a2⟩ := keyA L (cj Gs Gsi h1 h2) s 0 (cj_alg Gs Gsi h1 h2) hpφ
    (fun l => hfx _ (m_c L l)) (fun l => hfx _ (m_ci L l)) (fun l => hfx _ (m_cb L l))
    (hfx _ (m_GG L)) (hfx _ (m_ζb L)) (hfx _ (m_GGi L)) hnabφ Y
  obtain ⟨b1, b2⟩ := keyV L (cj Gs Gsi h1 h2) s 0 (cj_alg Gs Gsi h1 h2) hpbφ
    (fun l => hfx _ (m_cb L l)) (fun l => hfx _ (m_cbi L l)) (fun l => hfx _ (m_c L l))
    (hfx _ (m_GG L)) (hfx _ (m_ζ L)) (hfx _ (m_GGi L)) hnabsφ Y
  rw [mul_zero, zero_mul, add_zero] at a2 b2
  exact ⟨a1, a2, b1, b2⟩
end Formalism.FourierDecayAlt.P
