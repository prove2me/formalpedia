-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.coef_bound_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:57:03.900799+00:00
-- url     : https://prove2.me/submissions/cedd371d-52c8-46cb-a367-64eb3b93a837

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G K : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution {T : Submodule ℂ H} [FiniteDimensional ℂ T] {ρ : Mat n → ℝ}
    (hρ : ∀ g ∈ G, 0 ≤ ρ g)
    (hb : ∀ a ∈ T, ∀ b ∈ T, ∃ C : ℝ, ∀ g ∈ G, ‖⟪a, σ g b⟫_ℂ‖ ≤ C * ρ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ T, ∀ b ∈ T, ∀ g ∈ G, ‖⟪a, σ g b⟫_ℂ‖ ≤ C * ‖a‖ * ‖b‖ * ρ g := by
  let e := stdOrthonormalBasis ℂ T
  choose C hC using fun i j => hb _ (e i).2 _ (e j).2
  have hx : ∀ v : T, (v : H) = ∑ i, ⟪e i, v⟫_ℂ • (e i : H) := fun v => by
    conv_lhs => rw [← e.sum_repr' v]
    simp
  have hn : ∀ i (v : T), ‖⟪e i, v⟫_ℂ‖ ≤ ‖(v : H)‖ := fun i v => by
    have := norm_inner_le_norm (𝕜 := ℂ) (e i) v
    rwa [e.orthonormal.1 i, one_mul] at this
  refine ⟨∑ i, ∑ j, |C i j|, by positivity, fun a ha b hb g hg => ?_⟩
  have e1 : ⟪a, σ g b⟫_ℂ = ∑ i, ∑ j, (starRingEnd ℂ) ⟪e i, (⟨a, ha⟩ : T)⟫_ℂ *
      (⟪e j, (⟨b, hb⟩ : T)⟫_ℂ * ⟪(e i : H), σ g (e j)⟫_ℂ) := by
    conv_lhs => rw [show a = _ from hx ⟨a, ha⟩, show b = _ from hx ⟨b, hb⟩]
    simp only [sum_inner, inner_smul_left, map_sum, map_smul, inner_sum, inner_smul_right,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  have h1 := hn i ⟨a, ha⟩
  have h2 := hn j ⟨b, hb⟩
  have h3 := (hC i j g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hρ g hg))
  have h4 := hρ g hg
  calc _ ≤ ‖a‖ * (‖b‖ * (|C i j| * ρ g)) := by gcongr
    _ = _ := by ring
end CompanionTheory.D.Upq.Sm
