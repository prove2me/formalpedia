-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.orbitSum2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:28.686247+00:00
-- url     : https://prove2.me/submissions/f18b86dd-b33a-4053-a5f8-c97d59af8237

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped Classical ComplexConjugate
namespace Formalism.L2.SG.NormCut
section Asm
variable {I : Type*} [Group I] [Fintype I]
private lemma orbit_lemma_2 {C : Type*} [Fintype C] (A U : Set I) (s : C → I)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : I) * s x.2.1 * (x.2.2 : I))) (g : I → ℂ)
    (hg : ∀ x, ∀ a ∈ A, ∀ w ∈ U, g (a * x * w) = g x) :
    ∑ x : I, g x = ((Nat.card A : ℂ) * (Nat.card U : ℂ)) * ∑ c : C, g (s c) := by
  rw [← hb.sum_comp]
  simp only [Fintype.sum_prod_type]
  have e : ∀ (a : A) (c : C) (u : U), g ((a : I) * s c * (u : I)) = g (s c) :=
    fun a c u => hg (s c) a a.2 u u.2
  simp only [e]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, Nat.card_eq_fintype_card]
  ring
end Asm
section Inv
variable {I : Type*} [Group I] [Fintype I]
end Inv
section Main
variable {I : Type} [Group I] [Fintype I]
end Main
end Formalism.L2.SG.NormCut
end
end

set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
variable {I : Type*} [Group I] [Fintype I]
namespace Formalism.L2.SG.NormCut
theorem _root_.solution {C C' : Type*} [Fintype C] [Fintype C'] (A A' U : Set I) (s : C → I) (s' : C' → I)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : I) * s x.2.1 * (x.2.2 : I)))
    (hb' : Function.Bijective (fun x : A' × C' × U => (x.1 : I) * s' x.2.1 * (x.2.2 : I))) (f : I → I → ℂ)
    (hL : ∀ x y, ∀ a ∈ A, ∀ w ∈ U, f (a * x * w) y = f x y)
    (hR : ∀ x y, ∀ a ∈ A', ∀ w ∈ U, f x (a * y * w) = f x y) :
    ∑ x : I, ∑ y : I, f x y =
      ((Nat.card A : ℂ) * (Nat.card U : ℂ)) * ((Nat.card A' : ℂ) * (Nat.card U : ℂ)) *
        ∑ c : C, ∑ c' : C', f (s c) (s' c') := by
  rw [orbit_lemma_2 A U s hb (fun x => ∑ y, f x y)
    (fun x a ha w hw => Finset.sum_congr rfl fun y _ => hL x y a ha w hw)]
  have e : ∀ c, ∑ y, f (s c) y = ((Nat.card A' : ℂ) * (Nat.card U : ℂ)) * ∑ c', f (s c) (s' c') :=
    fun c => orbit_lemma_2 A' U s' hb' (f (s c)) (fun y a ha w hw => hR (s c) y a ha w hw)
  simp_rw [e, ← Finset.mul_sum]
  ring
end Formalism.L2.SG.NormCut
