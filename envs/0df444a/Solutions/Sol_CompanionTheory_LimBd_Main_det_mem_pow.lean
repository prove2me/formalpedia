-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.det_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:42.760185+00:00
-- url     : https://prove2.me/submissions/7886995c-17c8-4732-a3b6-20fb977c6047

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_GeneratingFunctionPolynomial
import Theorems.Thm_CompanionTheory_LimBd_Main_prod_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix
open scoped ComplexConjugate
variable {k r : ℕ}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution {m : ℕ} (Z : B.Mat k r → Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ a b, (fun g => Z g a b) ∈ Letters k r) : (fun g => (Z g).det) ∈ Letters k r ^ m := by
  have e : (fun g => (Z g).det) =
      ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∏ i, fun g => Z g (σ i) i := by
    funext g
    simp [Matrix.det_apply', Finset.prod_apply]
  rw [e]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ ?_
  simpa using prod_mem_pow Finset.univ (fun i g => Z g (σ i) i) fun i _ => h _ _
end CompanionTheory.LimBd.Main
