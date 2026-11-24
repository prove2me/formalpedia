-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.umean_le_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:03.923557+00:00
-- url     : https://prove2.me/submissions/e4e1c005-1afb-4e43-973e-bc867cfd81a7

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_mono
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_add
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_mul
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {ι : Type} [Fintype ι]
namespace Formalism.RankGapBounds.WeightedMeanData
theorem _root_.solution [Nonempty ι] {X A B P E : ι → ℝ} (p q K : ℝ)
    (h : ∀ i, X i ≤ A i + B i + p * P i + q * E i + K) :
    umean X ≤ umean A + umean B + p * umean P + q * umean E + K := by
  have h1 := umean_mono (X := X) (Y := fun i => A i + B i + p * P i + q * E i + K) h
  have h2 := umean_add (fun i => A i + B i + p * P i + q * E i) (fun _ => K)
  have h3 := umean_add (fun i => A i + B i + p * P i) (fun i => q * E i)
  have h4 := umean_add (fun i => A i + B i) (fun i => p * P i)
  have h5 := umean_add A B
  have h6 := umean_mul p P
  have h7 := umean_mul q E
  have h8 := umean_const (ι := ι) K
  linarith
end Formalism.RankGapBounds.WeightedMeanData
