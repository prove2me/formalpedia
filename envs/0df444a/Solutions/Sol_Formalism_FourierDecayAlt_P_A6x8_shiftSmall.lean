-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.shiftSmall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:43.304419+00:00
-- url     : https://prove2.me/submissions/7ccfdac1-e6bc-40fc-83a9-4e2939a558d6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_I_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_adic_of_datum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_unit_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_shift_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_shift_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
namespace Formalism.FourierDecayAlt.P.A6x8
theorem _root_.solution : ShiftSmall := by
  intro K _ _ _ R ψ hD hn Sg W hW
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg ϖ
  obtain ⟨n, hn'⟩ := h.basis W hW
  refine ⟨V ∩ I R ((ϖ ^ n : Kˣ) : K), inter_mem hV (I_nhds h.isOpen _),
    fun t t₁ ht σ hσ hs => ?_⟩
  obtain ⟨v, hv, e⟩ := h.unit_one _ (hVs _ ht.1 σ hσ)
  obtain ⟨r, hr, e'⟩ := ht.2
  have h1 := shift_alg t t₁ σ hs
  have : (t₁ : K) = (ϖ : K) ^ n * (r * v) := by
    push_cast at e'
    linear_combination (-(t₁ : K)) * e + v * h1 + v * e'
  rw [this]
  exact hn' _ (R.mul_mem hr hv)
end Formalism.FourierDecayAlt.P.A6x8
