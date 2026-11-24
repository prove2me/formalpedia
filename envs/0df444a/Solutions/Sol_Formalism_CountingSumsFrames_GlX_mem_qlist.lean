-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.mem_qlist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:21.60522+00:00
-- url     : https://prove2.me/submissions/a50f0d9c-5b93-4e41-b092-421badd333c5

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.GlX
theorem _root_.solution {S : Finset (Fin r → ℤ)} {c : ℤ} {ν : Fin r → ℤ} (hν : ν ∈ S) (hne : GlW.casI ν ≠ c) :
    GlW.casI ν ∈ qlist S c := by
  unfold qlist
  rw [Finset.mem_toList]
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem _ hν⟩
end Formalism.CountingSumsFrames.GlX
