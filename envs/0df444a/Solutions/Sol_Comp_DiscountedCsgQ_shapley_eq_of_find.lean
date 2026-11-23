-- Prove2me | solution 1 for Comp.DiscountedCsgQ.shapley_eq_of_find
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:24:17.722052+00:00
-- url     : https://prove2.me/submissions/596eaddc-cbea-4d09-9ded-6538cd7b6021

import Definitions.Def_Comp_Search
import Definitions.Def_Comp_Shapley
import Theorems.Thm_Comp_DiscountedCsgQ_shapleyGameQ_value
import Theorems.Thm_Comp_MatrixGameQ_value_eq_of_find


set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.DiscountedCsgQ
theorem _root_.solution (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {As1 : List A1} {As2 : List A2} {v : S → ℚ} {s : S}
    {t : ℚ} {p : A1 → ℚ} {q : A2 → ℚ}
    (hf : (G.shapleyGameQ s v).findValueCert As1 As2 = some (t, p, q)) :
    (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s = ((t : ℚ) : ℝ) := by
  change ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).value = ((t : ℚ) : ℝ)
  rw [shapleyGameQ_value G h s v]
  exact MatrixGameQ.value_eq_of_find hf
end Comp.DiscountedCsgQ
