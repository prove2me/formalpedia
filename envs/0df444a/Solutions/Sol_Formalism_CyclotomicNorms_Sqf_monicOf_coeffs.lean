-- Prove2me | solution 1 for Formalism.CyclotomicNorms.Sqf.monicOf_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:22.733805+00:00
-- url     : https://prove2.me/submissions/278f3fca-85e0-4ec9-a239-256e5bbde98a

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
import Theorems.Thm_Formalism_CyclotomicNorms_Sqf_coeff_monicOf_lt
import Theorems.Thm_Formalism_CyclotomicNorms_Sqf_coeff_monicOf_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.Sqf
variable {K : Type} [Field K]
namespace Formalism.CyclotomicNorms.Sqf
theorem _root_.solution (p : K[X]) (hp : p.Monic) {m : ℕ} (hd : p.natDegree = m) :
    monicOf (fun i : Fin m => p.coeff i) = p := by
  ext n
  rcases lt_or_ge n m with h | h
  · exact coeff_monicOf_lt (fun i : Fin m => p.coeff i) ⟨n, h⟩
  · rw [coeff_monicOf_ge _ n h]
    split_ifs with hn
    · subst hn
      rw [← hd]
      exact hp.coeff_natDegree.symm
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
end Formalism.CyclotomicNorms.Sqf
