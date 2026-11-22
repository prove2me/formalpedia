-- Prove2me | solution 1 for Comp.DiscountedCsgQ.shapley_eq_of_valueCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:34:49.984552+00:00
-- url     : https://prove2.me/submissions/acc946f1-56dc-450d-8437-356d9ce349fa

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate
import Theorems.Thm_Comp_DiscountedCsgQ_shapleyGameQ_value
import Theorems.Thm_Comp_MatrixGameQ_value_eq_of_valueCert


set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.DiscountedCsgQ
theorem _root_.solution (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {v : S → ℚ} {s : S} {t : ℚ} {p : A1 → ℚ} {q : A2 → ℚ}
    (hc : (G.shapleyGameQ s v).ValueCert t p q) :
    (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s = ((t : ℚ) : ℝ) := by
  change ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).value = ((t : ℚ) : ℝ)
  rw [shapleyGameQ_value G h s v]
  exact MatrixGameQ.value_eq_of_valueCert hc
end Comp.DiscountedCsgQ
