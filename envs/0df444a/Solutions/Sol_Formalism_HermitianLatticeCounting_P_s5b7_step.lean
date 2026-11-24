-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:37.683148+00:00
-- url     : https://prove2.me/submissions/ffd02a1c-e852-484a-9511-c6138e4d5afd

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_ideal

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
theorem _root_.solution (hO : ¬ IsField O) (M X : Type) [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (N : Submodule O M) (hN : IsCoatom N) [Finite (M ⧸ N)] :
    Nat.card ((N →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X N.subtype)) =
      Nat.card (M ⧸ N) ^ finrank O X := by
  classical
  have hsimple : IsSimpleModule O (M ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  obtain ⟨p, hp, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp hO
  have : Finite (O ⧸ p) := Finite.of_equiv _ e.toEquiv
  let π : M →ₗ[O] O ⧸ p := e.toLinearMap ∘ₗ N.mkQ
  have hπs : Function.Surjective π := e.surjective.comp (Submodule.mkQ_surjective N)
  have hπN : ∀ m, π m = 0 ↔ m ∈ N := by
    intro m
    simp [π]
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (Submodule.mkQ p) π
    (Submodule.mkQ_surjective p)
  have hl' : ∀ m, Submodule.Quotient.mk (l m) = π m := fun m => by
    have := congrArg (fun u => u m) hl; simpa using this
  obtain ⟨x, hx⟩ := hπs (Submodule.Quotient.mk 1)
  have hlp : ∀ m, l m ∈ p ↔ m ∈ N := by
    intro m
    rw [← hπN, ← hl', Submodule.Quotient.mk_eq_zero]
  have hax : ∀ a : O, π (a • x) = Submodule.Quotient.mk a := by
    intro a
    rw [map_smul, hx, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  have hpx : ∀ a : p, (a : O) • x ∈ N := by
    intro a
    rw [← hπN, hax, Submodule.Quotient.mk_eq_zero]
    exact a.2
  let j : p →ₗ[O] N := ((LinearMap.toSpanSingleton O M x) ∘ₗ p.subtype).codRestrict N hpx
  have hj : ∀ a : p, ((j a : N) : M) = (a : O) • x := fun a => rfl
  let R := LinearMap.range (LinearMap.lcomp O X (Submodule.subtype p))
  let Θ : (N →ₗ[O] X) →ₗ[O] (p →ₗ[O] X) ⧸ R := R.mkQ ∘ₗ LinearMap.lcomp O X j
  have hres : ∀ m : M, m - l m • x ∈ N := by
    intro m
    rw [← hπN, map_sub, hax, hl', sub_self]
  have hker : LinearMap.ker Θ = LinearMap.range (LinearMap.lcomp O X N.subtype) := by
    ext φ
    simp only [Θ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, R, LinearMap.mem_range]
    constructor
    · rintro ⟨ψ, hψ⟩
      let ρ : M →ₗ[O] N :=
        (LinearMap.id - (LinearMap.toSpanSingleton O M x) ∘ₗ l).codRestrict N hres
      refine ⟨φ ∘ₗ ρ + ψ ∘ₗ l, ?_⟩
      ext m
      have h1 : ψ (l (m : M)) = φ (j ⟨l (m : M), (hlp _).mpr m.2⟩) := by
        have := congrArg (fun u => u ⟨l (m : M), (hlp _).mpr m.2⟩) hψ
        simpa using this
      have h2 : ρ (m : M) + j ⟨l (m : M), (hlp _).mpr m.2⟩ = m := by
        apply Subtype.ext
        change ((m : M) - l (m : M) • x) + l (m : M) • x = m
        exact sub_add_cancel _ _
      simp only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.add_apply,
        LinearMap.comp_apply]
      rw [h1, ← map_add, h2]
    · rintro ⟨Φ, rfl⟩
      refine ⟨LinearMap.toSpanSingleton O X (Φ x), ?_⟩
      ext a
      simp [hj]
  have hsurj : Function.Surjective Θ := by
    intro q
    obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let lN : N →ₗ[O] p := (l ∘ₗ N.subtype).codRestrict p (fun m => (hlp _).mpr m.2)
    refine ⟨ψ ∘ₗ lN, ?_⟩
    simp only [Θ, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have ht : l x - 1 ∈ p := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hl', hx, sub_self]
    refine ⟨LinearMap.toSpanSingleton O X (ψ ⟨l x - 1, ht⟩), ?_⟩
    ext a
    have h3 : lN (j a) = a + (a : O) • (⟨l x - 1, ht⟩ : p) := by
      ext
      simp [lN, hj]
      ring
    simp only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply,
      LinearMap.sub_apply, LinearMap.comp_apply]
    rw [h3, map_add, map_smul]
    abel
  rw [← hker, Nat.card_congr (LinearMap.quotKerEquivOfSurjective Θ hsurj).toEquiv,
    s5b7_ideal p hp0 X, Nat.card_congr e.toEquiv]
end Formalism.HermitianLatticeCounting.P
