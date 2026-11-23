-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.mean
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:13.226508+00:00
-- url     : https://prove2.me/submissions/43c5e276-9d1d-4ace-acc8-0446bd8a2ed7

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_step1
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_finish
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_ngen_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
variable {Cl Nu : Type}
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
theorem _root_.solution (hS4 : Formalism.HermitianLatticeCounting.S4.Step4) (L : LocalNG Cl Nu) (C0 r κ e : ℕ) (Xp Yp : L.P → ℝ)
    (hX : ∀ p, 1 ≤ Xp p) (hY : ∀ p, 1 ≤ Yp p) (hb : L.Basic) (hM : L.MassRatioAt C0 r) (hU : L.Unfold)
    (h1 : ∀ p ∈ L.Om, ∑ d, L.wt p d * ‖L.aN p d‖ ^ 2 ≤ Xp p * ((L.q p : ℝ) ^ κ)⁻¹ * L.nn p)
    (h2 : ∀ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 ≤ Xp p * L.nn p)
    (h3 : ∀ p, L.nn p ≤ Yp p * L.ngen p)
    (h : ∀ p, (if p ∈ L.Om then (4 : ℝ) else 1) * (Xp p * Yp p) ≤ L.H p ^ e) (S : Finset (Cl × Nu)) :
    ∑ x ∈ S, L.a2 x.1 x.2 ≤ ((2 : ℝ) ^ κ)⁻¹ * L.Htot ^ e * L.ngenTot := by
  have hb' := hb
  unfold LocalNG.Basic at hb'
  have hV0 : 0 ≤ L.V0 := hb'.2.2.2.2.2.1
  have hng : 0 ≤ ∏ p, L.ngen p := Finset.prod_nonneg (fun p _ => ngen_nonneg L C0 r hb hM p)
  have hfin := finish L Xp Yp hX hY e h
  have hcore := core hS4 L κ Xp Yp hX hY hb h1 h2 h3
  have hstep := step1 L hU S
  have hk : 0 ≤ ((2 : ℝ) ^ κ)⁻¹ := by positivity
  calc ∑ x ∈ S, L.a2 x.1 x.2 ≤ L.V0 * ∑ d, (∏ p, L.wt p (d p)) * ‖L.ampNG d‖ ^ 2 := hstep
    _ ≤ L.V0 * ((4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, L.ngen p) :=
        mul_le_mul_of_nonneg_left hcore hV0
    _ ≤ L.V0 * (L.Htot ^ e * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, L.ngen p) := by
        refine mul_le_mul_of_nonneg_left ?_ hV0
        refine mul_le_mul_of_nonneg_right ?_ hng
        exact mul_le_mul_of_nonneg_right hfin hk
    _ = ((2 : ℝ) ^ κ)⁻¹ * L.Htot ^ e * L.ngenTot := by
        unfold LocalNG.ngenTot
        ring
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
