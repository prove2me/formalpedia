-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.div_fold_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:10.659519+00:00
-- url     : https://prove2.me/submissions/12f55bc5-c4f9-47db-a84a-b523d7519f70

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Theorems.Thm_Formalism_L2_Pj_Crude_div_iter_pderiv_monomial
import Theorems.Thm_Formalism_L2_Pj_Crude_div_listSum_apply_of_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {ι : Type} [DecidableEq ι] (a : ι →₀ ℕ) (L : List ι) (hL : L.Nodup) (s : ι →₀ ℕ)
    (c : k) :
    L.foldr (fun l g => (MvPolynomial.pderiv l)^[a l] g) (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - (L.map fun l => Finsupp.single l (a l)).sum)
        (c * (L.map fun l => ((s l).descFactorial (a l) : k)).prod) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    rw [List.foldr_cons, ih hL.2, div_iter_pderiv_monomial]
    have hx : (s - (L.map fun l => Finsupp.single l (a l)).sum) x = s x := by
      rw [Finsupp.tsub_apply, div_listSum_apply_of_notMem a L x hL.1, Nat.sub_zero]
    simp only [List.map_cons, List.sum_cons, List.prod_cons, hx]
    congr 1
    · rw [tsub_tsub, add_comm]
    · ring
end Formalism.L2.Pj.Crude
