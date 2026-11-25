-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.taylor_expansion_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:55:35.346826+00:00
-- url     : https://prove2.me/submissions/4c504902-e026-4076-ae5f-5e03410e844c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTTaylor
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_RadTTaylor_symm_iter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_RadTTaylor_poly_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_RadTTaylor_poly_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution : GTCLRTaylor := by
  intro V _ _ ψ U ζ₀ N hU hζ hψ i hi
  have hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun k => by
    first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)
  have hψat : ContDiffAt ℝ i ψ ζ₀ := (hψ.contDiffAt (hU.mem_nhds hζ)).of_le (hle i)
  have hS : ContDiff ℝ i (fun ζ : ℂ => ∑ j ∈ Finset.range (N + 1),
      ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) :=
    ContDiff.sum fun j _ => (poly_contDiff _ _).const_smul _
  refine (iteratedFDeriv_sub_apply hψat hS.contDiffAt).trans ?_
  rw [sub_eq_zero, iteratedFDeriv_sum (fun j _ => (poly_contDiff _ _).const_smul _)]
  ext v
  rw [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      iteratedFDeriv ℝ i (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ v =
        if j = i then ((i.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ)
        else 0 := by
    intro j _
    rw [show (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) =
        ((j.factorial : ℝ)⁻¹) • (fun ζ : ℂ => iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) from rfl,
      iteratedFDeriv_const_smul_apply ((poly_contDiff _ _).contDiffAt),
      ContinuousMultilinearMap.smul_apply, poly_at]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (N + 1)) i,
    if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hi))]
  have hs : ∀ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ) = iteratedFDeriv ℝ i ψ ζ₀ v :=
    fun σ => symm_iter i V ψ U hU hψ ζ₀ hζ σ v
  rw [Finset.sum_congr rfl (fun σ _ => hs σ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)), one_smul]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
