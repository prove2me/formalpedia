-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:23.212465+00:00
-- url     : https://prove2.me/submissions/765bac14-17b8-434b-879e-0e0fa470c68f

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_proj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module
variable {O : Type} [CommRing O] [IsDedekindDomain O]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (p : Ideal O) [hp : p.IsMaximal] (hp0 : p ≠ ⊥) [Finite (O ⧸ p)] (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    Nat.card ((p →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X (Submodule.subtype p))) =
      Nat.card (O ⧸ p) ^ finrank O X := by
  classical
  have : Module.Projective O p := s5b7_proj p
  obtain ⟨t, htp, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hcomm : ∀ (ψ : p →ₗ[O] X) (a c : p), (a : O) • ψ c = (c : O) • ψ a := by
    intro ψ a c
    rw [← map_smul, ← map_smul]
    congr 1
    ext
    simp [mul_comm]
  have htf : Module.IsTorsionFree O (p →ₗ[O] X) := inferInstance
  have : Module.Projective O (p →ₗ[O] X) := s5b7_proj _
  have hrange : LinearMap.range (LinearMap.lcomp O X (Submodule.subtype p)) =
      p • (⊤ : Submodule O (p →ₗ[O] X)) := by
    apply le_antisymm
    · rintro _ ⟨ψ, rfl⟩
      obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' O p
      obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
      have hgs : ∀ c, g (s c) = c := fun c => by
        have := congrArg (fun u => u c) hs; simpa using this
      have key : LinearMap.lcomp O X (Submodule.subtype p) ψ =
          ∑ i, ((g (fun j => if i = j then 1 else 0) : p) : O) •
            ((LinearMap.toSpanSingleton O X (ψ 1)) ∘ₗ (LinearMap.proj i) ∘ₗ s) := by
        ext c
        have h1 : (c : O) = ∑ i, s c i * ((g (fun j => if i = j then 1 else 0) : p) : O) := by
          conv_lhs => rw [← hgs c, pi_eq_sum_univ (s c)]
          simp [map_sum]
        simp only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
          LinearMap.toSpanSingleton_apply]
        have h2 : ψ (c : O) = (c : O) • ψ 1 := by
          rw [← map_smul]; simp
        rw [h2, h1, Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, mul_comm]
      rw [key]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (g _).2 trivial
    · rw [Submodule.smul_le]
      intro a ha ψ _
      refine ⟨LinearMap.toSpanSingleton O X (ψ ⟨a, ha⟩), ?_⟩
      ext c
      simpa using hcomm ψ c ⟨a, ha⟩
  rw [hrange, s5b7_quot p (p →ₗ[O] X)]
  congr 1
  apply le_antisymm
  · let ev : (p →ₗ[O] X) →ₗ[O] X := LinearMap.applyₗ (⟨t, htp⟩ : p)
    have hev : Function.Injective ev := by
      rw [injective_iff_map_eq_zero]
      intro ψ hψ
      ext c
      have h1 := hcomm ψ ⟨t, htp⟩ c
      have h2 : ψ ⟨t, htp⟩ = 0 := hψ
      rw [h2, smul_zero] at h1
      exact (smul_eq_zero_iff_right ht0).mp h1
    exact LinearMap.finrank_le_finrank_of_injective hev
  · let j : X →ₗ[O] (p →ₗ[O] X) :=
      (LinearMap.lcomp O X (Submodule.subtype p)) ∘ₗ
        (LinearMap.ringLmapEquivSelf O O X).symm.toLinearMap
    have hj : Function.Injective j := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h1 : j x ⟨t, htp⟩ = 0 := by rw [hx]; rfl
      have h2 : t • x = 0 := by simpa [j] using h1
      exact (smul_eq_zero_iff_right ht0).mp h2
    exact LinearMap.finrank_le_finrank_of_injective hj
end Formalism.HermitianLatticeCounting.P
