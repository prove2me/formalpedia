-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiberIntegrable_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:09.36997+00:00
-- url     : https://prove2.me/submissions/e0297420-6dfb-486d-bd0f-5dd64261c7de

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeFiberIntegrable choices 0
      F pref prefixTs top ρ :=
  trivial
end BKAR.Forest
