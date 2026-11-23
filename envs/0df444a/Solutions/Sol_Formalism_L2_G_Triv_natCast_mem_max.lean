-- Prove2me | solution 1 for Formalism.L2.G.Triv.natCast_mem_max
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:25.565356+00:00
-- url     : https://prove2.me/submissions/ce4ce97e-ef99-4f05-8aab-a7cea7c960be

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F : Type} [Field F] [NumberField F] {k : ℕ}
namespace Formalism.L2.G.Triv
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) :
    (g : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  have h1 : Valued.v ((g : v.adicCompletion F)) * Valued.v (u : v.adicCompletion F) = 1 := by
    rw [← map_mul]
    have := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hu
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    have e : (((g : v.adicCompletionIntegers F)) : v.adicCompletion F) = (g : v.adicCompletion F) := by simp
    rw [e] at this
    rw [this, map_one]
  have h2 : Valued.v ((g : v.adicCompletion F)) < 1 := by
    have e : (g : v.adicCompletion F) = ((algebraMap (𝓞 F) F (g : 𝓞 F) : F) : v.adicCompletion F) := by
      rw [map_natCast]
      exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
    rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hg
  have h3 : Valued.v (u : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 u.2
  have h4 : Valued.v ((g : v.adicCompletion F)) * Valued.v (u : v.adicCompletion F) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h3) h2
  rw [h1] at h4
  exact lt_irrefl _ h4
end Formalism.L2.G.Triv
