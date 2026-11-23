-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:33.418801+00:00
-- url     : https://prove2.me/submissions/a14bb36e-23a8-4c8e-8910-24fac8827e12

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (ι H X : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] (hfree : ∀ (g : ι → H) (x : X), g • x = x → g = 1) :
    ∃ (Q : Type) (_ : Fintype Q) (e : Q × (ι → H) ≃ X),
      ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g) := by
  classical
  let Q := MulAction.orbitRel.Quotient (ι → H) X
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → X := fun ω => Quotient.out ω
  have hrep : ∀ ω : Q, Quotient.mk (MulAction.orbitRel (ι → H) X) (rep ω) = ω :=
    fun ω => Quotient.out_eq ω
  let f : Q × (ι → H) → X := fun p => p.2 • rep p.1
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨ω, g⟩ ⟨ω', g'⟩ h
      change g • rep ω = g' • rep ω' at h
      have hω : ω = ω' := by
        rw [← hrep ω, ← hrep ω']
        apply Quotient.sound
        show rep ω ∈ MulAction.orbit (ι → H) (rep ω')
        refine ⟨g⁻¹ * g', ?_⟩
        show (g⁻¹ * g') • rep ω' = rep ω
        rw [mul_smul, ← h, inv_smul_smul]
      subst hω
      have hfix : (g'⁻¹ * g) • rep ω = rep ω := by rw [mul_smul, h, inv_smul_smul]
      have hg := hfree _ _ hfix
      rw [inv_mul_eq_one] at hg
      rw [hg]
    · intro x
      have hx : rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) ∈ MulAction.orbit (ι → H) x :=
        Quotient.exact (hrep _)
      obtain ⟨g, hg⟩ := hx
      refine ⟨(Quotient.mk (MulAction.orbitRel (ι → H) X) x, g⁻¹), ?_⟩
      show g⁻¹ • rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) = x
      rw [← hg, inv_smul_smul]
  refine ⟨Q, inferInstance, Equiv.ofBijective f hf, ?_⟩
  intro m ω g
  show (m * g) • rep ω = m • (g • rep ω)
  rw [mul_smul]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
