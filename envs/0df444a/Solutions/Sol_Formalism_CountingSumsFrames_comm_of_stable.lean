-- Prove2me | solution 1 for Formalism.CountingSumsFrames.comm_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:41.274643+00:00
-- url     : https://prove2.me/submissions/f58e2a98-beda-496a-821a-e137387e4c49

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (P Q : V →ₗ[K] V) (hP : P ∘ₗ P = P) (hr : ∀ x ∈ LinearMap.range P, Q x ∈ LinearMap.range P)
    (hk : ∀ x ∈ LinearMap.ker P, Q x ∈ LinearMap.ker P) : ∀ x, P (Q x) = Q (P x) := by
  intro x
  have hPP : ∀ z, P (P z) = P z := fun z => by simpa using LinearMap.congr_fun hP z
  obtain ⟨y, hy⟩ := hr _ (LinearMap.mem_range_self P x)
  have h2 : x - P x ∈ LinearMap.ker P := by rw [LinearMap.mem_ker, map_sub, hPP, sub_self]
  have h3 := hk _ h2
  rw [LinearMap.mem_ker] at h3
  simp only [map_sub] at h3
  rw [sub_eq_zero] at h3
  rw [h3, ← hy, hPP]
end Formalism.CountingSumsFrames
