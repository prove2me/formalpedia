-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.length_quot_pi_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:30.740308+00:00
-- url     : https://prove2.me/submissions/738b36c5-5598-44a6-9a86-ba4ae9e5fab4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (G : Type*) [Fintype G] [DecidableEq G]
    (A B : Submodule O M) :
    Module.length O ((Submodule.pi Set.univ fun _ : G => A) ⧸
        (Submodule.pi Set.univ fun _ : G => B).comap (Submodule.pi Set.univ fun _ : G => A).subtype) =
      Fintype.card G • Module.length O (A ⧸ B.comap A.subtype) := by
  set P := Submodule.pi Set.univ fun _ : G => A with hP
  set B' := B.comap A.subtype with hB'
  let pr : G → P →ₗ[O] A := fun g =>
    LinearMap.codRestrict A ((LinearMap.proj g).comp P.subtype) (fun x => x.2 g (Set.mem_univ g))
  let φ : P →ₗ[O] (G → A ⧸ B') := LinearMap.pi fun g => B'.mkQ.comp (pr g)
  have hsurj : Function.Surjective φ := by
    intro y
    choose x hx using fun g => Submodule.Quotient.mk_surjective B' (y g)
    refine ⟨⟨fun g => (x g : M), fun g _ => (x g).2⟩, ?_⟩
    funext g
    simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← hx g]
    rfl
  have hker : LinearMap.ker φ = (Submodule.pi Set.univ fun _ : G => B).comap P.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro h g
      have hg := congrFun h g
      simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap] at hg
      exact hg
    · intro h
      funext g
      simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap]
      exact h g
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective φ hsurj)
  rw [e.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card, nsmul_eq_mul]
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
