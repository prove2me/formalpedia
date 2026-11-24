-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.fock_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:34.294811+00:00
-- url     : https://prove2.me/submissions/6e3de61b-2722-4442-8937-dc2bc4b4efe1

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {σ τ : Type} (ι : σ → τ) (hι : Function.Injective ι) (F F' : MvPolynomial σ ℚ_[p]) :
    fock p (rename ι F) (rename ι F') = fock p F F' := by
  classical
  unfold fock
  rw [support_rename_of_injective hι, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hι h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain ι hι, coeff_rename_mapDomain ι hι, Finsupp.prod_mapDomain_index_inj hι]
end Formalism.CountingSumsFrames.TO
