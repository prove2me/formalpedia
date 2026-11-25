-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.stab_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:16:36.516482+00:00
-- url     : https://prove2.me/submissions/921d9e13-5fc4-439e-b2ce-02cd52975248

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecomp
import Theorems.Thm_Formalism_FrobeniusOrbits_liesOver_span_of_natCast_mem_frobenius_orbits
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
open NumberField IntermediateField Ideal
open scoped Pointwise
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
theorem _root_.solution (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b) (r : ℕ) (hr : r = 2 ∨ r = q)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : σ • P = P) : galE e ζ a b σ ∈ Psi e := by
  have hq2 : Nat.Coprime q (2 ^ (e + 2)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right, Nat.odd_iff]
    have := hH.2.2.1; omega
  have hd2 : Nat.Coprime d (2 ^ (e + 2)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right, Nat.odd_iff]
    have := hH.2.2.2.1; omega
  have hD := hostDecomp e q d hH L ζ a b h (ZMod.unitOfCoprime q hq2) (ZMod.unitOfCoprime d hd2)
    (by simp) (by simp) σ
  have hst : σ ∈ MulAction.stabilizer _ P := hσ
  rcases hr with rfl | rfl
  · have : P.LiesOver (span {(2 : ℤ)}) := by
      have := liesOver_span_of_natCast_mem_frobenius_orbits P 2 Nat.prime_two hm
      simpa using this
    exact (hD.1 P).mp hst
  · have : P.LiesOver (span {(r : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P r hH.1 hm
    rw [mem_Psi_iff]
    exact ((hD.2.1 P).mp hst).1
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
