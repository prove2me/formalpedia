-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusScale_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:58.238862+00:00
-- url     : https://prove2.me/submissions/f5dc1f31-aad5-4a99-b3da-7e2cac55e1fe

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_mem_one_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (s : Set V)
    (hs : ∀ a ∈ s, ∀ b ∈ s, c * h a b ∈ (1 : Submodule R K)) :
    ∀ x ∈ Submodule.span R s, ∀ y ∈ Submodule.span R s, c * h x y ∈ (1 : Submodule R K) := by
  have key : ∀ a ∈ s, ∀ y ∈ Submodule.span R s, c * h a y ∈ (1 : Submodule R K) := by
    intro a ha y hy
    induction hy using Submodule.span_induction with
    | mem b hb => exact hs a ha b hb
    | zero => simp
    | add u w _ _ hu hw =>
        rw [map_add, mul_add]
        exact add_mem hu hw
    | smul r u _ hu =>
        rw [genusBasic_hsmul_right, mul_left_comm]
        exact genusBasic_mem_one_mul _ hu r
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem a ha => exact key a ha y hy
  | zero => simp
  | add u w _ _ hu hw =>
      rw [map_add, LinearMap.add_apply, mul_add]
      exact add_mem hu hw
  | smul r u _ hu =>
      rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
      exact genusBasic_mem_one_mul _ hu _
end Formalism.HermitianLatticesTheory
