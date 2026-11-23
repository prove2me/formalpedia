-- Prove2me | solution 1 for Formalism.REAL.noncompact_arr_finite_dimensional
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:15.672256+00:00
-- url     : https://prove2.me/submissions/8536a4ee-ec69-4ac6-827a-929d5718b9c5

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_mem_noncompact_arr_iff_general

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {j : ℕ} {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    (hfd : FiniteDimensional ℂ (kSpan ε E u)) : FiniteDimensional ℂ (arrV0 ε E u j) := by
  have hmem : ∀ (F : arrV0 ε E u j) (α : Fin j → Fin n × Fin n),
      ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ arrOf V n j) ∘ₗ
        (arrV0 ε E u j).subtype) F ∈ kSpan ε E u := by
    intro F α
    have h := (mem_noncompact_arr_iff_general (F : Arr V n j)).mp F.2 α
    change ((F : Arr V n j) α) ∈ _
    split_ifs at h
    · exact h
    · rw [Submodule.mem_bot] at h
      rw [h]; exact Submodule.zero_mem _
  let φ : arrV0 ε E u j →ₗ[ℂ] ((Fin j → Fin n × Fin n) → kSpan ε E u) :=
    LinearMap.pi fun α => LinearMap.codRestrict (kSpan ε E u)
      ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ arrOf V n j) ∘ₗ
        (arrV0 ε E u j).subtype) (fun F => hmem F α)
  have hinj : Function.Injective φ := by
    intro F G hFG
    apply Subtype.ext
    apply PiLp.ext
    intro α
    have := congrArg (fun h => ((h α : kSpan ε E u) : V)) hFG
    simpa [φ, arrOf] using this
  exact Module.Finite.of_injective φ hinj
end Formalism.REAL
