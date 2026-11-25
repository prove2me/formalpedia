-- Prove2me | solution 1 for Formalism.L2.G.Cmp.Fib.cls_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:54.706803+00:00
-- url     : https://prove2.me/submissions/fca08f9e-c167-4d8b-baa4-f540a7affaec

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsFib
import Theorems.Thm_Formalism_L2_G_Cmp_Fib_mk_eq_iff
import Theorems.Thm_P2M_Formalism_L2_G_Cmp_Fib_K__split_0aa688ac5c40

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.UG
open Formalism.L2.G.Cmp.Fib
variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)
variable (y : ClassSet H K' → G) (hy : ∀ i, mkC H K' (y i) = i) (hp : ∀ i, X.pr (y i) = 1)
include hy
namespace Formalism.L2.G.Cmp.Fib
theorem _root_.solution (x : G) : ∃ i g, mkC H K (y i * X.j g) = mkC H K x := by
  obtain ⟨h, hh, κ, hκ, he⟩ := (mk_eq_iff H K' (y (mkC H K' x)) x).1 (hy _)
  refine ⟨mkC H K' x, X.pr κ, (mk_eq_iff H K _ _).2
    ⟨h, hh, (X.j (X.pr κ))⁻¹ * κ, X.K'_split κ hκ, ?_⟩⟩
  conv_lhs => rw [he]
  group
end Formalism.L2.G.Cmp.Fib
