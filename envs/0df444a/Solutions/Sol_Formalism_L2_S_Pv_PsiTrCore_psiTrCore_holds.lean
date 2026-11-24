-- Prove2me | solution 1 for Formalism.L2.S.Pv.PsiTrCore.psiTrCore_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:37:15.326818+00:00
-- url     : https://prove2.me/submissions/b6fb72a4-21a5-49a3-9e38-19fc06346154

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LevelCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreTrace
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCore
import Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_intAf_le_congSub
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
namespace Formalism.L2.S.Pv.PsiTrCore
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
private lemma sum_embedding_eq_trace_of_totallyReal {K : Type} [Field K] [NumberField K]
    (hK : NumberField.IsTotallyReal K) (a : K) :
    ∑ v : InfinitePlace K, v.embedding a = ((Algebra.trace ℚ K a : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ K a : ℚ) : ℂ) = ∑ σ : K →ₐ[ℚ] ℂ, σ a := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings]
  have h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ a = ∑ φ : K →+* ℂ, φ a :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ a) (fun σ : K →ₐ[ℚ] ℂ => σ a)
      (fun φ => rfl)).symm
  have h3 : ∑ v : InfinitePlace K, v.embedding a = ∑ φ : K →+* ℂ, φ a := by
    refine Fintype.sum_bijective (fun v : InfinitePlace K => v.embedding) ⟨fun v w h => ?_, fun φ => ?_⟩
      _ _ (fun v => rfl)
    · simpa [InfinitePlace.mk_embedding] using congrArg InfinitePlace.mk h
    · exact ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.mp (hK.isReal _))⟩
  rw [h3, h1]
  exact h2.symm
private lemma sum_phi_add_star_eq_trace (I : AutInst) (z : I.E) :
    ∑ v, (I.φ v z + star (I.φ v z)) = ((Algebra.trace ℚ I.E z : ℚ) : ℂ) := by
  obtain ⟨a, ha⟩ := (I.cm.fixed (z + star z)).mp (by rw [star_add, star_star, add_comm])
  have hφ : ∀ v, I.φ v z + star (I.φ v z) = v.embedding a := by
    intro v
    have hs : star (I.φ v z) = I.φ v (star z) := by
      rw [I.cm.cmUnram.2.1, starRingEnd_apply]
    rw [hs, ← map_add, ← ha, I.φ_over]
  have hTr : Algebra.trace I.F I.E z = a := by
    let e : I.E ≃ₐ[I.F] I.E := AlgEquiv.ofRingEquiv (f := starRingAut) (fun x => by
      rw [starRingAut_apply]; exact (I.cm.fixed _).mpr ⟨x, rfl⟩)
    have e1 : Algebra.trace I.F I.E (star z) = Algebra.trace I.F I.E z := by
      first
      | exact Algebra.trace_eq_of_algEquiv e z
      | exact (Algebra.trace_eq_of_algEquiv e z).symm
    have e2 : Algebra.trace I.F I.E (z + star z) = 2 • a := by
      rw [← ha, Algebra.trace_algebraMap, I.cm.deg2]
    rw [map_add, e1, two_nsmul] at e2
    have e3 : (2 : I.F) * Algebra.trace I.F I.E z = 2 * a := by rw [two_mul, two_mul, e2]
    exact mul_left_cancel₀ two_ne_zero e3
  rw [Finset.sum_congr rfl (fun v _ => hφ v), sum_embedding_eq_trace_of_totallyReal I.cm.totReal a,
    ← Algebra.trace_trace (S := I.F) (T := I.E), hTr]
end Formalism.L2.S.Pv.PsiTrCore
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.PsiTrCore
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.S.Pv.PsiTrCore
theorem _root_.solution : Formalism.L2.SG.Pf.PsiTrCore := by
  intro I ψ hadd hint hprod y hy t ht
  obtain ⟨N, hN, hNy⟩ : ∃ N : ℤ, N ≠ 0 ∧ IsIntegral ℤ ((N : I.E) * y) := by
    obtain ⟨⟨N, hN⟩, h⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) y (Algebra.IsIntegral.isIntegral (R := ℚ) y)
    refine ⟨N, nonZeroDivisors.ne_zero hN, ?_⟩
    rw [Submonoid.smul_def, zsmul_eq_mul] at h
    exact h
  let o₀ : 𝓞 I.E := ⟨(N : I.E) * y, hNy⟩
  obtain ⟨o, s, hs, rfl⟩ := intAf_le_congSub (F := I.F) (E := I.E) N hN ht
  have hsplit : (Formalism.UG.inclE (F := I.F) (Af I.F) (o : I.E) + (N : I.E ⊗[I.F] Af I.F) * s) *
      Formalism.UG.inclE (F := I.F) (Af I.F) y =
      Formalism.UG.inclE (F := I.F) (Af I.F) ((o : I.E) * y) +
        s * Formalism.UG.inclE (F := I.F) (Af I.F) (o₀ : I.E) := by
    have h0 : (o₀ : I.E) = (N : I.E) * y := rfl
    rw [h0, map_mul, map_mul, map_intCast]
    ring
  rw [hsplit, hadd, hint _ (mul_mem hs (incl_mem o₀)), mul_one]
  obtain ⟨m, hm⟩ := hy o
  have hP := hprod ((o : I.E) * y)
  have hexp : ∏ v, Complex.exp (2 * Real.pi * Complex.I *
      (I.φ v ((o : I.E) * y) + star (I.φ v ((o : I.E) * y)))) = 1 := by
    rw [← Complex.exp_sum, ← Finset.mul_sum, sum_phi_add_star_eq_trace I, hm]
    push_cast
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I m
  rw [hexp, mul_one] at hP
  exact hP
end Formalism.L2.S.Pv.PsiTrCore
