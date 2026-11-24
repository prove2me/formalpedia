-- Prove2me | solution 1 for Formalism.DivisionValues.idxLcv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:24:20.456872+00:00
-- url     : https://prove2.me/submissions/b4c068ea-b809-4d4d-91ae-4984a6fa7908

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Theorems.Thm_Formalism_DivisionValues_idxLcv_lidx_add
import Theorems.Thm_Formalism_DivisionValues_imageLcv_std_li
import Theorems.Thm_Formalism_DivisionValues_imageLcv_std_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution (h : LcvBasis) : IdxLcv := by
  intro K _ _ _ _ d X hX A B hA hB
  classical
  have hE := imageLcv_std_li (K := K) d
  have hS := imageLcv_std_lat (K := K) d
  obtain ⟨sA, eA⟩ := h K d X hX A hA _ hE
  obtain ⟨sB, eB⟩ := h K d X hX B hB _ hE
  set S := Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K))) with hSdef
  have hadd : ∀ w : HeightOneSpectrum (𝓞 K), idx w S B = idx w S A + idx w A B := fun w =>
    idxLcv_lidx_add (K := K) w.asIdeal S A B hS hA hB
  have hfun : (fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)) =
      (fun w => lw w * (idx w S B : ℝ)) - (fun w => lw w * (idx w S A : ℝ)) := by
    funext w
    simp only [Pi.sub_apply, hadd w]
    push_cast
    ring
  have hsupp : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)).Finite := by
    rw [hfun]
    exact (sB.union sA).subset (Function.support_sub _ _)
  refine ⟨hsupp, ?_⟩
  have hsplit : (fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w S B : ℝ)) =
      fun w => lw w * (idx w S A : ℝ) + lw w * (idx w A B : ℝ) := by
    funext w
    rw [hadd w]
    push_cast
    ring
  rw [eB, eA, hsplit, finsum_add_distrib sA hsupp]
  ring
end Formalism.DivisionValues
