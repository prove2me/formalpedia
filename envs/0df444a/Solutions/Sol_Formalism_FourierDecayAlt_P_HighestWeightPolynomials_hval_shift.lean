-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hval_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:51:43.441979+00:00
-- url     : https://prove2.me/submissions/d33a670e-20a8-4c1f-9352-3ac074de8b4f

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HighestWeightPolynomials
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials
theorem _root_.solution {n : ℕ} (ν : Fin n → ℂ) (a b : Fin n) :
    hval (fun c => ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  unfold hval
  have h : ∀ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) *
      (ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℂ).re =
      ((n : ℝ) - ((c : ℕ) : ℝ)) * (ν c).re + (if c = a then ((n : ℝ) - ((c : ℕ) : ℝ)) else 0) -
        (if c = b then ((n : ℝ) - ((c : ℕ) : ℝ)) else 0) := by
    intro c
    split_ifs <;> simp <;> ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring
end Formalism.FourierDecayAlt.P.HighestWeightPolynomials
