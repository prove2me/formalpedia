-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.separating_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:32:31.449728+00:00
-- url     : https://prove2.me/submissions/f2f0330b-e344-4457-ac2c-56568425a838

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_map_eq_of_cpol
import Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_sdec_re
import Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_sdec_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.SepPoly := by
  intro n m m' h hm'
  have hmap := map_eq_of_cpol m m' h
  have hnd : (Multiset.map m univ.val).Nodup := by
    rw [hmap]
    exact Multiset.Nodup.map (sdec_inj hm') univ.nodup
  refine ⟨fun a b hab => Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab, ?_⟩
  intro hm
  have hmem : ∀ a, ∃ b, m' b = m a := by
    intro a
    have h1 : m a ∈ Multiset.map m univ.val := Multiset.mem_map_of_mem m (Finset.mem_univ a)
    rw [hmap, Multiset.mem_map] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, hb⟩
  have hmem' : ∀ a, ∃ b, m b = m' a := by
    intro a
    have h1 : m' a ∈ Multiset.map m' univ.val := Multiset.mem_map_of_mem m' (Finset.mem_univ a)
    rw [← hmap, Multiset.mem_map] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, hb⟩
  have hr : (fun a => (m a).re) = fun a => (m' a).re := by
    rw [← StrictAnti.range_inj (sdec_re hm) (sdec_re hm')]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem a
      exact ⟨b, by simp only [hb]⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem' a
      exact ⟨b, by simp only [hb]⟩
  funext a
  obtain ⟨b, hb⟩ := hmem a
  have h1 : (m' b).re = (m' a).re := by rw [hb]; exact congrFun hr a
  rw [← hb, (sdec_re hm').injective h1]
end Formalism.FourierDecayAlt.P
