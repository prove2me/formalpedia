-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_dual_kernel_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:09:28.317946+00:00
-- url     : https://prove2.me/submissions/9ad0bc94-6dbc-439c-a249-a35256a0eaca

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_admissible_word_pairwise_condition
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_good_of_adm
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_qw_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
theorem _root_.solution : AdmDK := by
  intro S _ _ α β q w L hL hG h1 h2
  have hpw := List.pairwise_append.1 (admissible_word_pairwise_condition h1)
  have hreal : ∀ l ∈ L, l.pt = ((l.pt.re : ℝ) : ℂ) := fun l hl =>
    Complex.ext (by simp) (by simpa using (h1.2.1 l (List.mem_append_left w hl)).1)
  have hpos : ∀ l ∈ L, (qw q w l.pt).im = 0 ∧ 0 < (qw q w l.pt).re := by
    intro l hl
    have hq := hG l.pt.re (h1.2.1 l (List.mem_append_left w hl)).2.1
    rw [hreal l hl]
    refine qw_pos q l.pt.re hq w fun l' hl' => ⟨(h1.2.1 l' (List.mem_append_right L hl')).1, ?_⟩
    have hc := (hpw.2.2 l hl l' hl').1
    unfold Cnd at hc
    exact hc
  refine ⟨⟨hL, good_of_adm h1, good_of_adm h2, ?_, fun l hl => ?_⟩, hpos⟩
  · refine hpw.1.imp_of_mem fun {l l'} hl hl' hc => ?_
    have hc1 := hc.1
    unfold Cnd at hc1
    rw [if_pos (hL l' hl')] at hc1
    rw [hreal l hl, hreal l' hl']
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
      rw [hre] at hc1
      norm_num at hc1
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hre
      rw [hre] at hc1
      norm_num at hc1
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hre
      rw [hre] at hc1
      norm_num at hc1
  · intro h0
    have := (hpos l hl).2
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
end Formalism.FourierDecayAlt.P.RealWeightedForms
