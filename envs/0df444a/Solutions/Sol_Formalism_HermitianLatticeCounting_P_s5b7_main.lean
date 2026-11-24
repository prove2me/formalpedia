-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:52.854565+00:00
-- url     : https://prove2.me/submissions/7324b7cf-d2ba-480e-83a2-ed2db45169af

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_card_comp
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_proj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_step

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
theorem _root_.solution (hO : ¬ IsField O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] : ∀ (n : ℕ) (P M : Type) [AddCommGroup P] [Module O P] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] (ι : P →ₗ[O] M),
    Function.Injective ι → n ≠ 0 → Nat.card (M ⧸ LinearMap.range ι) = n →
    Nat.card ((P →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X ι)) = n ^ finrank O X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P M _ _ _ _ _ _ ι hι hn0 hn
  classical
  have hinf : Infinite O := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    exact hO (Finite.isField_of_domain O)
  rcases eq_top_or_exists_le_coatom (LinearMap.range ι) with htop | ⟨N, hN, hle⟩
  · have h1 : n = 1 := by
      rw [← hn, htop]; simp
    have hs : Function.Surjective ι := LinearMap.range_eq_top.mp htop
    let e := LinearEquiv.ofBijective ι ⟨hι, hs⟩
    have h2 : LinearMap.range (LinearMap.lcomp O X ι) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro φ
      refine ⟨φ ∘ₗ e.symm.toLinearMap, ?_⟩
      ext y
      change φ (e.symm (e y)) = φ y
      rw [e.symm_apply_apply]
    rw [h2, h1]; simp
  · let ι1 : P →ₗ[O] N := ι.codRestrict N (fun y => hle ⟨y, rfl⟩)
    have hι1 : Function.Injective ι1 := fun a b hab => hι (congrArg Subtype.val hab)
    have hcomp : ι = N.subtype ∘ₗ ι1 := by ext y; rfl
    have hc := s5b7_card_comp ι1 N.subtype N.injective_subtype
    rw [← hcomp, hn, Submodule.range_subtype] at hc
    have hA : Nat.card (N ⧸ LinearMap.range ι1) ≠ 0 := fun h => hn0 (by rw [hc, h, zero_mul])
    have hB : Nat.card (M ⧸ N) ≠ 0 := fun h => hn0 (by rw [hc, h, mul_zero])
    have hfB : Finite (M ⧸ N) := Nat.finite_of_card_ne_zero hB
    have hfA : Finite (N ⧸ LinearMap.range ι1) := Nat.finite_of_card_ne_zero hA
    have hnt : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.mpr hN.1
    have hB2 : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
    have hlt : Nat.card (N ⧸ LinearMap.range ι1) < n := by
      rw [hc]
      have : 0 < Nat.card (N ⧸ LinearMap.range ι1) := Nat.pos_of_ne_zero hA
      nlinarith
    have : IsNoetherian O M := isNoetherian_of_isNoetherianRing_of_finite O M
    have : Module.Projective O N := s5b7_proj N
    have h1 := ih _ hlt P N ι1 hι1 hA rfl
    have h2 := s5b7_step hO M X N hN
    have hinj : Function.Injective (LinearMap.lcomp O X ι1) := by
      rw [injective_iff_map_eq_zero]
      intro φ hφ
      ext y
      obtain ⟨a, b, hab, hEq⟩ := Finite.exists_ne_map_eq_of_infinite
        (fun a : O => (Submodule.Quotient.mk (a • y) : N ⧸ LinearMap.range ι1))
      rw [Submodule.Quotient.eq, ← sub_smul] at hEq
      obtain ⟨z, hz⟩ := hEq
      have h3 : φ (ι1 z) = 0 := by
        have := congrArg (fun u => u z) hφ
        simpa using this
      rw [hz, map_smul] at h3
      exact (smul_eq_zero_iff_right (sub_ne_zero.mpr hab)).mp h3
    have hc2 := s5b7_card_comp (LinearMap.lcomp O X N.subtype) (LinearMap.lcomp O X ι1) hinj
    have hcomp2 : LinearMap.lcomp O X ι1 ∘ₗ LinearMap.lcomp O X N.subtype = LinearMap.lcomp O X ι := by
      ext φ y
      rfl
    rw [hcomp2, h1, h2] at hc2
    rw [hc2, hc, mul_pow, mul_comm]
end Formalism.HermitianLatticeCounting.P
