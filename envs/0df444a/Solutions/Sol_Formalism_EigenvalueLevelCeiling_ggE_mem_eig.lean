-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ggE_mem_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:03.877368+00:00
-- url     : https://prove2.me/submissions/a4d10253-8098-47b1-ad5b-3a611232ef62

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ggE_apply
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_mem_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K) (hMk : IsMackey U ψ) (x : Z) : ggE ρ U ψ x ∈ eig ρ U ψ := by
  obtain ⟨hone, hmul, -⟩ := hMk
  rw [gg_mem_eig]
  intro u0
  rw [ggE_apply, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft u0) _ _ (fun u => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_inv_rev]
  rw [map_smul, hmul _ (U.inv_mem u.2) _ (U.inv_mem u0.2), smul_smul, map_mul,
    Module.End.mul_apply]
  congr 1
  have h1 : ψ (u0 : P)⁻¹ * ψ (u0 : P) = 1 := by
    rw [← hmul _ (U.inv_mem u0.2) _ u0.2, inv_mul_cancel, hone]
  rw [← map_mul, mul_comm, mul_assoc, h1, mul_one]
end Formalism.EigenvalueLevelCeiling
