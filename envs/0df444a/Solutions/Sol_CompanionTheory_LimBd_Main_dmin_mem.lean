-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.dmin_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:09:03.135798+00:00
-- url     : https://prove2.me/submissions/1d45b6d7-5728-46c0-b2d0-ce88d54184c1

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_GeneratingFunctionPolynomial
import Theorems.Thm_CompanionTheory_LimBd_Main_letters_pow_mono
import Theorems.Thm_CompanionTheory_LimBd_Main_det_mem_pow
import Theorems.Thm_CompanionTheory_LimBd_Main_herm_letter
import Theorems.Thm_CompanionTheory_LimBd_Main_herm_conj_letter

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
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    (fun g : B.Mat k r => ((Complex.normSq (Formalism.QuantumDeterminants.Dmin k r z z' g l) : ℝ) : ℂ)) ∈ Letters k r ^ (2 * r + 2) := by
  have hl : (l : ℕ) ≤ r + 1 := Nat.le_of_lt_succ l.isLt
  have h1 : (fun g : B.Mat k r => Formalism.QuantumDeterminants.Dmin k r z z' g l) ∈ Letters k r ^ (r + 1) :=
    letters_pow_mono hl (det_mem_pow _ fun a b => herm_letter _ _)
  have h2 : (fun g : B.Mat k r => conj (Formalism.QuantumDeterminants.Dmin k r z z' g l)) ∈ Letters k r ^ (r + 1) := by
    have := det_mem_pow (k := k) (r := r) (fun g => ((Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix
      (Fin.castLE hl) (Fin.castLE hl))ᴴ) fun a b => herm_conj_letter _ _
    simp only [Matrix.det_conjTranspose] at this
    exact letters_pow_mono hl this
  have := Submodule.mul_mem_mul h1 h2
  rw [← pow_add, show r + 1 + (r + 1) = 2 * r + 2 by ring] at this
  convert this using 1
  funext g
  simp [Complex.mul_conj]
end CompanionTheory.LimBd.Main
