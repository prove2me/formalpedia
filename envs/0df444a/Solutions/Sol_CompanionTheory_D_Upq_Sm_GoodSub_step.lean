-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.GoodSub.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:53.531912+00:00
-- url     : https://prove2.me/submissions/97aca56a-c364-4021-8ea8-10c8aa4f02e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_exists_clm
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ds_sum
import Theorems.Thm_CompanionTheory_D_Upq_Sm_apply_ds_conj
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_continuousOn


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
namespace GoodSub
theorem _root_.solution (hG : IsMatGroup G) (h : RepOn G σ) (hK : K ⊆ G) {T : Submodule ℂ H}
    (hT : GoodSub G K σ T) : ∃ (T' : Submodule ℂ H) (C : ℝ), GoodSub G K σ T' ∧ T ≤ T' ∧ 0 ≤ C ∧
      ∀ X, (∀ t, ex X t ∈ G) → ‖X‖ ≤ 1 → ∀ v ∈ T, ds σ X v ∈ T' ∧ ‖ds σ X v‖ ≤ C * ‖v‖ := by
  haveI := hT.fin
  let b := stdOrthonormalBasis ℂ T
  have hb : ∀ i, IsSm G σ (b i : H) := fun i => hT.sm _ (b i).2
  choose D hD using fun i => (hb i).exists_clm h
  have hexp : ∀ X, (∀ t, ex X t ∈ G) → ∀ v : T,
      ds σ X (v : H) = ∑ i, ⟪b i, v⟫_ℂ • D i X := fun X hX v => by
    have e : (v : H) = ∑ i, ⟪b i, v⟫_ℂ • (b i : H) := by
      conv_lhs => rw [← b.sum_repr' v]
      simp
    rw [e, ds_sum h hX _ _ hb]
    exact Finset.sum_congr rfl fun i _ => by rw [hD i X hX]
  have hDb : ∀ i, ∃ c : ℝ, 0 ≤ c ∧ ∀ X : Mat n, ‖X‖ ≤ 1 → ‖D i X‖ ≤ c := fun i => by
    obtain ⟨c, hc⟩ := (isCompact_closedBall (0 : Mat n) 1).exists_bound_of_continuousOn
      (D i).continuous.continuousOn
    exact ⟨max c 0, le_max_right _ _, fun X hX =>
      (hc X (mem_closedBall_zero_iff.2 hX)).trans (le_max_left _ _)⟩
  choose cD hcD0 hcD using hDb
  let A : Set H := {y | ∃ X, (∀ t, ex X t ∈ G) ∧ ∃ v ∈ T, y = ds σ X v}
  let e := Module.finBasis ℝ (Mat n)
  let B : Submodule ℂ H := Submodule.span ℂ (range fun p : _ × _ => D p.1 (e p.2))
  haveI : FiniteDimensional ℂ B := FiniteDimensional.span_of_finite ℂ (finite_range _)
  have hAB : Submodule.span ℂ A ≤ B := Submodule.span_le.2 <| by
    rintro _ ⟨X, hX, v, hv, rfl⟩
    rw [show ds σ X v = _ from hexp X hX ⟨v, hv⟩]
    refine B.sum_mem fun i _ => B.smul_mem _ ?_
    rw [← e.sum_repr X, map_sum]
    refine B.sum_mem fun j _ => ?_
    rw [map_smul]
    exact B.smul_of_tower_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ A) := Submodule.finiteDimensional_of_le hAB
  refine ⟨T ⊔ Submodule.span ℂ A, ∑ i, cD i, ⟨inferInstance, ?_, fun k hk => ?_⟩, le_sup_left,
    Finset.sum_nonneg fun i _ => hcD0 i, fun X hX hX1 v hv => ⟨?_, ?_⟩⟩
  · change T ⊔ Submodule.span ℂ A ≤ smSub G σ
    refine sup_le hT.sm (Submodule.span_le.2 ?_)
    rintro _ ⟨X, hX, v, hv, rfl⟩
    exact (hT.sm v hv).dsW h (W := [X]) fun Y hY => by rwa [List.mem_singleton.1 hY]
  · change T ⊔ Submodule.span ℂ A ≤ (T ⊔ Submodule.span ℂ A).comap (σ k : H →ₗ[ℂ] H)
    refine sup_le (fun v hv => Submodule.mem_sup_left (hT.stab k hk v hv))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨X, hX, v, hv, rfl⟩
    obtain ⟨h1, h2⟩ := apply_ds_conj hG h (hK hk) hX (hT.sm v hv)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨_, h1, _, hT.stab k hk v hv, h2⟩)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨X, hX, v, hv, rfl⟩)
  · rw [show ds σ X v = _ from hexp X hX ⟨v, hv⟩, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, mul_comm]
    refine mul_le_mul (hcD i X hX1) ?_ (norm_nonneg _) (hcD0 i)
    have := norm_inner_le_norm (𝕜 := ℂ) (b i) (⟨v, hv⟩ : T)
    rwa [b.orthonormal.1 i, one_mul] at this
end GoodSub
end CompanionTheory.D.Upq.Sm
