-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.embSpan_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:20.175435+00:00
-- url     : https://prove2.me/submissions/2eb41473-7e24-49d0-bbbc-562c7bd9dc0c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
open Formalism.DivisionValues.ConjugateWeightGram
namespace Formalism.DivisionValues.ConjugateWeightGram
theorem _root_.solution {K : Type} [Field K] {n d : ℕ} (τ : K →+* ℂ) (z : Fin d → Fin n → K) :
    embSpan τ (Submodule.span K (Set.range z)) =
      Submodule.span ℂ (Set.range fun c => (fun i => τ (z c i) : Fin n → ℂ)) := by
  apply le_antisymm
  · unfold embSpan
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    have : (fun i => τ ((∑ k, c k • z k) i) : Fin n → ℂ) =
        ∑ k, τ (c k) • (fun i => τ (z k i) : Fin n → ℂ) := by
      funext i
      simp [Finset.sum_apply]
    change (fun i => τ ((∑ k, c k • z k) i) : Fin n → ℂ) ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span ⟨z c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩
end Formalism.DivisionValues.ConjugateWeightGram
