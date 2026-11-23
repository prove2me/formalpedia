-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:29.46364+00:00
-- url     : https://prove2.me/submissions/58cbb86b-3887-46b5-868e-119ba32aab95

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K)) (hM : M.FG) :
    ∃ a ∈ (𝓞 K)⁰, ∀ x ∈ M, ∀ i, IsLocalization.IsInteger (𝓞 K) (a • x i) := by
  have hc : ∀ i : Fin m, ∃ a ∈ (𝓞 K)⁰, ∀ b ∈ M.map (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K),
      IsLocalization.IsInteger (𝓞 K) (a • b) :=
    fun i => FractionalIdeal.isFractional_of_fg (hM.map _)
  choose a ha hb using hc
  refine ⟨∏ i, a i, prod_mem fun i _ => ha i, fun x hx i => ?_⟩
  have hxi := hb i (x i) (Submodule.mem_map_of_mem (f := (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K)) hx)
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
  exact IsLocalization.isInteger_smul hxi
end Formalism.L2.LamCM.A2
