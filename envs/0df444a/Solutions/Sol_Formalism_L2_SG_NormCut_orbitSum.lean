-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.orbitSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:53.564255+00:00
-- url     : https://prove2.me/submissions/8e23d3be-85b9-49f6-a54b-d729107d479d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
namespace Formalism.L2.SG.NormCut
theorem _root_.solution {G C : Type*} [Group G] [Fintype G] [Fintype C] (A U : Set G) (s : C → G)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : G) * s x.2.1 * (x.2.2 : G))) (f : G → ℂ)
    (hf : ∀ x, ∀ a ∈ A, ∀ w ∈ U, f (a * x * w) = f x) :
    ∑ x : G, f x = (Nat.card A : ℂ) * (Nat.card U : ℂ) * ∑ c : C, f (s c) := by
  rw [← Function.Bijective.sum_comp hb f]
  simp only [Fintype.sum_prod_type]
  have h1 : ∀ (a : A) (c : C) (w : U), f ((a : G) * s c * (w : G)) = f (s c) :=
    fun a c w => hf (s c) a a.2 w w.2
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
end Formalism.L2.SG.NormCut
