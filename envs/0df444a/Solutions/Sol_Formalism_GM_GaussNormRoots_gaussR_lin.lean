-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.gaussR_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:53.664337+00:00
-- url     : https://prove2.me/submissions/c5fe0602-a96a-463d-8689-f5919bcb8169

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
import Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_eq_sup_of_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
open Formalism.GM.GaussNormRoots
variable {K : Type} [NormedField K]
namespace Formalism.GM.GaussNormRoots
theorem _root_.solution (ρ : NNReal) (q a : K) :
    gaussR ρ (Polynomial.C q * X + Polynomial.C a) = max ‖a‖₊ (‖q‖₊ * ρ) := by
  have hs : (Polynomial.C q * X + Polynomial.C a).support ⊆ {0, 1} := by
    intro k hk
    rw [Polynomial.mem_support_iff] at hk
    rcases k with _ | _ | k <;> simp_all [Polynomial.coeff_C, Polynomial.coeff_X]
  rw [gaussR_eq_sup_of_subset ρ _ _ hs]
  simp [Polynomial.coeff_C, Polynomial.coeff_X, max_comm]
end Formalism.GM.GaussNormRoots
