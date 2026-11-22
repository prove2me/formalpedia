-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.lg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:59.878887+00:00
-- url     : https://prove2.me/submissions/84b79b46-6ace-425b-b3c5-d52f901a53bf

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution (hR : ¬ IsField R) (A : Submodule R V) (x : V)
    (hx : ∀ w : HeightOneSpectrum R, x ∈ localization₂ w.asIdeal A) : x ∈ A := by
  let I : Ideal R :=
    { carrier := {r | r • x ∈ A}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, add_smul] at *
        exact A.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c r hr => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul] at *
        exact A.smul_mem c hr }
  by_contra hxA
  have hI : I ≠ ⊤ := fun h => hxA (by
    have h1 : (1 : R) ∈ I := h ▸ Submodule.mem_top
    simpa [I] using h1)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hM0 : M ≠ ⊥ := fun h => hR (Ring.isField_iff_maximal_bot.2 (h ▸ hM))
  let w : HeightOneSpectrum R := ⟨M, hM.isPrime, hM0⟩
  obtain ⟨s, hs, hsx⟩ := hx w
  exact hs (hIM hsx)
end Formalism.DivisionValues.GluingInclusion
