-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ggE_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:03.621619+00:00
-- url     : https://prove2.me/submissions/c0d33b3e-4699-4712-b74e-a03f2af3efcb

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
    (ψ : P → 𝓞 K) (hMk : IsMackey U ψ) (z : Z) (hz : z ∈ eig ρ U ψ) :
    ggE ρ U ψ z = ((Fintype.card U : ℕ) : K) • z := by
  obtain ⟨hone, hmul, -⟩ := hMk
  rw [ggE_apply]
  have : ∀ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) z = z := by
    intro u
    rw [(gg_mem_eig ρ U ψ z).mp hz u, smul_smul, ← map_mul, ← hmul _ (U.inv_mem u.2) _ u.2,
      inv_mul_cancel, hone, map_one, one_smul]
  rw [Finset.sum_congr rfl (fun u _ => this u)]
  simp [Nat.cast_smul_eq_nsmul]
end Formalism.EigenvalueLevelCeiling
