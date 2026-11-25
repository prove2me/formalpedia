-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.poly_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:18:32.330113+00:00
-- url     : https://prove2.me/submissions/a6ac1afa-02dc-437b-a3ff-39fb4bdf4247

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTTaylor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
theorem _root_.solution {j i : ℕ} (hij : i ≠ j) (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) :
    iteratedFDeriv ℝ i (fun ζ => m (fun _ => ζ)) 0 = 0 := by
  have hg : ContDiff ℝ i (fun ζ : E => m (fun _ => ζ)) :=
    m.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
  set L : E →L[ℝ] E := (2 : ℝ) • ContinuousLinearMap.id ℝ E with hL
  have hcomp : (fun ζ : E => m (fun _ => ζ)) ∘ L = ((2 : ℝ) ^ j) • (fun ζ : E => m (fun _ => ζ)) := by
    funext ζ
    simp only [Function.comp_apply, Pi.smul_apply, hL, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [m.map_smul_univ (fun _ => (2 : ℝ)) (fun _ => ζ)]
    simp [Finset.prod_const]
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_right L hg 0 (i := i) le_rfl
  rw [hcomp, iteratedFDeriv_const_smul_apply hg.contDiffAt, map_zero] at h1
  have hne : (2 : ℝ) ^ j ≠ (2 : ℝ) ^ i := by
    intro h
    apply hij
    have : (2 : ℕ) ^ j = 2 ^ i := by exact_mod_cast h
    exact (Nat.pow_right_injective le_rfl this).symm
  ext v
  have key : ((2 : ℝ) ^ j) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v =
      ((2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v := by
    have hv := congrArg (fun T => T v) h1
    simp only [ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply] at hv
    rw [hv, hL]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    rw [ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0)
      (fun _ => (2 : ℝ)) v]
    simp [Finset.prod_const]
  have h0 : ((2 : ℝ) ^ j - (2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v = 0 := by
    rw [sub_smul, key, sub_self]
  rw [ContinuousMultilinearMap.zero_apply]
  exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
