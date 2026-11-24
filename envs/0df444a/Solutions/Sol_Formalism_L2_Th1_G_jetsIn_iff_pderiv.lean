-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn_iff_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:10:39.557097+00:00
-- url     : https://prove2.me/submissions/7bf19602-1510-4619-9c25-ba0d1c2d336c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_mfact_zero
import Theorems.Thm_Formalism_L2_Th1_G_jet_pderiv
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_pderiv
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral mfact_add_single)
variable {K : Type} [Field K] {R : Subring K} {ι : Type}
namespace Formalism.L2.Th1.G
theorem _root_.solution (f : MvPowerSeries ι K) :
    JetsIn R f ↔ MvPowerSeries.constantCoeff f ∈ R ∧
      ∀ i, JetsIn R (MvPowerSeries.pderiv K i f) := by
  constructor
  · intro hf
    refine ⟨?_, fun i => jetsIn_pderiv hf i⟩
    simpa [mfact_zero] using hf 0
  · rintro ⟨h0, hd⟩ κ
    classical
    by_cases hκ : κ = 0
    · subst hκ
      simpa [mfact_zero] using h0
    · obtain ⟨i, hi⟩ : ∃ i, κ i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hκ (Finsupp.ext h)
      have hk : κ - Finsupp.single i 1 + Finsupp.single i 1 = κ :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))
      have h := hd i (κ - Finsupp.single i 1)
      rw [jet_pderiv, hk] at h
      exact h
end Formalism.L2.Th1.G
