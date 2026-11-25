-- Prove2me | solution 1 for Formalism.L2.Th1.C.endoAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:16:29.995816+00:00
-- url     : https://prove2.me/submissions/74c6b9a1-3f24-4ed5-b1f8-27e82e716e15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_P2M_Formalism_L2_Th1_C_integralEndoClosed__c3bb72aeab08
import Theorems.Thm_P2M_Formalism_L2_Th1_C_binomialScalarClosed__70abcca284e9
import Theorems.Thm_P2M_Formalism_L2_Th1_C_logNormClosed__bc2a9a014583
import Theorems.Thm_P2M_Formalism_L2_Th1_C_scalarLinearClosed__d624c2f8cbb5
import Theorems.Thm_P2M_Formalism_L2_Th1_C_scalarLinearInt__9d6bbd947da1
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_add
import Theorems.Thm_Formalism_L2_Th1_C_intBinomScalar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Clo
namespace Formalism.L2.Th1.C
theorem _root_.solution (hN : NormAdjAll) : EndoAll := by
  intro K _ _ _ _ R hR l linv ph h h1 O _ _ _ τ hτ hstar hsa h2R h2O hsum Dn hDn hD
  have hl := h.1.1
  have hli := h.1.2.2.1
  have hph := h.2.2
  have hEu : ∀ α : Oˣ, EndInt R l linv (τ α) := by
    intro α
    have hc : IsClosed {β : O | EndInt R l linv (τ β)} :=
      (integralEndoClosed' K R hR l linv hl).preimage hτ
    exact closure_minimal (fun β hβ => (hD β hβ).1) hc (hDn α)
  have hE : ∀ α : O, EndInt R l linv (τ α) := by
    intro α
    obtain ⟨u, v, rfl⟩ := hsum α
    rw [map_add]
    exact Pts.endInt_add h.1 h.2.1 (hEu u) (hEu v)
  have hPu : ∀ α : Oˣ, PhNormAt R l linv ph (τ α) (τ (star (α : O))) := by
    intro α
    have hc : IsClosed {β : O | PhNormAt R l linv ph (τ β) (τ (star β))} :=
      (logNormClosed' K R hR l linv ph hl hli hph).preimage
        (hτ.prodMk (hτ.comp hstar))
    exact closure_minimal (fun β hβ => (hD β hβ).2) hc (hDn α)
  have hB : ∀ z : O, star z = z → IsBinomScalar R (τ z) := by
    intro z hz
    refine closure_minimal ?_ (binomialScalarClosed' K R hR) (hsa z hz)
    rintro _ ⟨n, rfl⟩
    exact intBinomScalar K R n
  have hZ : ∀ z : O, star z = z → ZLinAt R l linv ph (τ z) := by
    intro z hz
    refine closure_minimal ?_ (scalarLinearClosed' K R hR l linv ph hl hli hph) (hsa z hz)
    rintro _ ⟨n, rfl⟩
    exact scalarLinearInt' K R l linv ph h h1 n
  intro α
  have := hN K R l linv ph h O τ hE hB hZ h1 h2R h2O hsum hPu α
  exact ⟨hE α, this.1, this.2⟩
end Formalism.L2.Th1.C
