-- Prove2me | solution 1 for Eden.integerGrowthValues_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:14.351444+00:00
-- url     : https://prove2.me/submissions/1ea4f788-01a3-46f8-b889-df042a139c34

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_attractor_nonempty


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (k : ℕ) (t : ℝ) :
    (integerGrowthValues c k t).Nonempty := attractor_nonempty.image _
end Eden
