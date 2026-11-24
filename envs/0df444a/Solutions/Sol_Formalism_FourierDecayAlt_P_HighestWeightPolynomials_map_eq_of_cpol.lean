-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HighestWeightPolynomials.map_eq_of_cpol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:33:44.945317+00:00
-- url     : https://prove2.me/submissions/9ee781a2-91ea-4f8d-88af-6e676a2f9e82

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution {n : ℕ} (m m' : Fin n → ℂ) (h : ∀ w, cpol m w = cpol m' w) :
    Multiset.map m univ.val = Multiset.map m' univ.val := by
  have key : ∀ (f : Fin n → ℂ) (w : ℂ), cpol f w = Polynomial.eval w
      ((Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - f j) univ.val)).prod) := by
    intro f w
    rw [Multiset.map_map, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp [cpol, Finset.prod, Function.comp_def]
  have hp : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - m j) univ.val)).prod =
      (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - m' j) univ.val)).prod :=
    Polynomial.funext (fun w => by rw [← key, ← key, h])
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  have h2 := congrArg (Multiset.map (fun z : ℂ => -z)) hr
  simpa [Multiset.map_map, Function.comp_def] using h2
end Formalism.FourierDecayAlt.P.HighestWeightPolynomials
