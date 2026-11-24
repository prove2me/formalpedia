-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.gaussR_multiset_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:53.674542+00:00
-- url     : https://prove2.me/submissions/186ee3fd-ce54-441d-bdaa-2c7814dcff02

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
import Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_C

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
theorem _root_.solution (hG : GaussMulRad) [IsUltrametricDist K] (ρ : NNReal) (hρ : 0 < ρ)
    (m : Multiset K) (f : K → K[X]) :
    gaussR ρ (m.map f).prod = (m.map (fun ζ => gaussR ρ (f ζ))).prod := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [← Polynomial.C_1, gaussR_C]
    simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [hG K ρ _ _ hρ, ih]
end Formalism.GM.GaussNormRoots
