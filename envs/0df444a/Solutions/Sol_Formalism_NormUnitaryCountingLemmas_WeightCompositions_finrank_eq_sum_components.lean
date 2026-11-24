-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_eq_sum_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:01:27.779824+00:00
-- url     : https://prove2.me/submissions/4d618c78-6e4b-4159-960a-29aa81046f1a

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_comp_sum_components
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_weight


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
universe u
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.WeightCompositions
variable {N n : ℕ}
namespace Formalism.NormUnitaryCountingLemmas.WeightCompositions
theorem _root_.solution {σ M K : Type*} [Field K] [AddCommMonoid M] [DecidableEq M]
    (φ : σ → M) (V : Submodule K (MvPolynomial σ K)) [FiniteDimensional K V] (S : Finset M)
    (hcomp : ∀ F ∈ V, ∀ m, weightedHomogeneousComponent φ m F ∈ V)
    (hS : ∀ F ∈ V, ∀ m ∉ S, weightedHomogeneousComponent φ m F = 0) :
    Module.finrank K V =
      ∑ m ∈ S, Module.finrank K ↥(V ⊓ weightedHomogeneousSubmodule K φ m) := by
  classical
  let W : S → Submodule K (MvPolynomial σ K) :=
    fun m => V ⊓ weightedHomogeneousSubmodule K φ (m : M)
  have : ∀ m : S, FiniteDimensional K (W m) :=
    fun m => Submodule.finiteDimensional_of_le inf_le_left
  let Φ : V →ₗ[K] (∀ m : S, W m) := LinearMap.pi fun m =>
    { toFun := fun F => ⟨weightedHomogeneousComponent φ (m : M) (F : MvPolynomial σ K),
        hcomp F F.2 m, weightedHomogeneousComponent_mem _ _ _⟩
      map_add' := by intro a b; ext1; simp
      map_smul' := by intro c a; ext1; simp }
  have hΦ : ∀ F m, ((Φ F m : W m) : MvPolynomial σ K) =
      weightedHomogeneousComponent φ (m : M) (F : MvPolynomial σ K) := fun F m => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    have h0 : ∀ m, weightedHomogeneousComponent φ m (F : MvPolynomial σ K) = 0 := by
      intro m
      by_cases hm : m ∈ S
      · have := congrArg Subtype.val (congrFun hF ⟨m, hm⟩)
        rw [hΦ] at this
        simpa using this
      · exact hS F F.2 m hm
    apply Subtype.ext
    ext d
    have := congrArg (coeff d) (h0 (Finsupp.weight φ d))
    rw [coeff_weightedHomogeneousComponent, if_pos rfl] at this
    simpa using this
  have hsurj : Function.Surjective Φ := by
    intro g
    refine ⟨⟨∑ m : S, ((g m : W m) : MvPolynomial σ K),
      Submodule.sum_mem _ fun m _ => (g m).2.1⟩, ?_⟩
    funext m
    apply Subtype.ext
    rw [hΦ]
    exact comp_sum_components φ S (fun m : S => ((g m : W m) : MvPolynomial σ K))
      (fun m : S => (g m).2.2) m
  rw [(LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_coe_sort S (fun m => Module.finrank K ↥(V ⊓ weightedHomogeneousSubmodule K φ m))
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
