-- Prove2me | solution 1 for Formalism.L2.PjFree.isCombAt_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:59.001682+00:00
-- url     : https://prove2.me/submissions/6ec8d7ff-b528-4411-9e9d-2e76927d445e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Theorems.Thm_Formalism_L2_PjFree_isCombAt_epsPt
import Theorems.Thm_Formalism_L2_PjFree_epsPt_zero
import Theorems.Thm_Formalism_L2_PjFree_epsPt_one_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace Formalism.L2.PjFree
theorem _root_.solution {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) (j : Fin m) :
    IsCombAt x v (Pi.single j 1) (v j) := by
  have h := isCombAt_epsPt hv (Pi.single j 1)
  suffices e : (List.ofFn fun i => epsPt (hv i) ((Pi.single j 1 : Fin m → S) i)).prod.left = v j by
    rw [e] at h; exact h
  rw [List.prod_ofFn, Finset.prod_eq_single j]
  · simp only [Pi.single_eq_same]
    exact epsPt_one_left (hv j)
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    exact epsPt_zero (hv i)
  · intro h; exact absurd (Finset.mem_univ j) h
end Formalism.L2.PjFree
