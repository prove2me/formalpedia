-- Prove2me | solution 1 for Formalism.G.LogP.constantCoeff_subst_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:54.441709+00:00
-- url     : https://prove2.me/submissions/7cfdd946-0b1b-4363-99c0-0a4b27883e78

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
namespace Formalism.G.LogP
theorem _root_.solution {σ τ : Type*} [Finite σ] [Finite τ]
    (Φ : MvPowerSeries σ R) {b : σ → MvPowerSeries τ R} (hb : ∀ i, constantCoeff (b i) = 0) :
    constantCoeff (Φ.subst b) = constantCoeff Φ := by
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [MvPowerSeries.constantCoeff_subst hb', finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : constantCoeff (d.prod fun s e => b s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, hb i, zero_pow hi]
    rw [h0, smul_zero]
end Formalism.G.LogP
