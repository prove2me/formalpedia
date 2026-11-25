-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:35:36.446934+00:00
-- url     : https://prove2.me/submissions/080d332d-715b-4e11-b41b-30e8d2f44bcb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_admissible_dual_kernel_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_re_mul_div
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_frm_act_act_of_star_mul_mul_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_mem_Lp
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_plus_Lp
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_prod_Lp
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_lemmaDK
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_pairAdj
import Theorems.Thm_Formalism_FourierDecayAlt_P_plane_wave_word_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
section admitted
variable {S : Type}
end admitted
section Rep
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
end Rep
private theorem sizeBoundOfParts_statement : SizeBoundOfParts := by
  intro hDK hPW hPA hAdm A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β y hD hG hI h1 h2
  obtain ⟨hS, hW, hWQ, -, -, -, -, -, -, -, -⟩ := hD
  obtain ⟨hDKH, hpos⟩ := hAdm S α β q w (Lp sl y) (plus_Lp sl y) hG h1 h2
  obtain ⟨-, -, hinv, -⟩ := hPW ℂ A S QQ f fi s (Lp sl y ++ w) hW hWQ h1.1
  obtain ⟨-, hle⟩ := hDK A S V ρ QQ q w (Lp sl y) hS hDKH (hI _ h1)
    (act (Vw f s (Lp sl y ++ w)) (letters vA vB (Lp sl y) x)) (letters vAv vBv ((Lp sl y).map dl) x)
  rw [frm_act_act_of_star_mul_mul_eq ρ _ _ hinv] at hle
  have hWK : WK ρ QQ f s w vA vB vAv vBv sl y x =
      pair ρ (act (JL (Lp sl y) * RRw QQ w) (act (Vw f s (Lp sl y ++ w)) (letters vA vB (Lp sl y) x)))
        (letters vAv vBv ((Lp sl y).map dl) x) := by
    unfold WK
    congr 1
    exact (hPA A S V ρ (JL (Lp sl y) * RRw QQ w) (Vw f s (Lp sl y ++ w)) 1
      (letters vA vB (Lp sl y) x) (letters vAv vBv ((Lp sl y).map dl) x)).1
  rw [hWK]
  refine hle.trans_eq ?_
  have hP : ((Lp sl y).map fun l => qw q w l.pt).prod = ((∏ a, (qw q w (y a)).re : ℝ) : ℂ) := by
    rw [prod_Lp sl y (qw q w), Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hm := (hpos _ (mem_Lp sl y a)).1
    exact Complex.ext (by simp) (by simpa using hm)
  rw [hP, re_mul_div _ _ _ ((hI _ h1) _).2]
end Formalism.FourierDecayAlt.P.RealWeightedForms
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
theorem _root_.solution : AdmissiblePointSizeBound := by
  exact sizeBoundOfParts_statement DualKernelLemmas.lemmaDK Formalism.FourierDecayAlt.P.plane_wave_word_identity GramProductIdentities.pairAdj admissible_dual_kernel_identity
end Formalism.FourierDecayAlt.P.RealWeightedForms
