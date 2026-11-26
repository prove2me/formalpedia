-- Prove2me | solution 1 for EdenVerified.p22_lipschitzWith_descending
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:31:58.775275+00:00
-- url     : https://prove2.me/submissions/b2b23808-6901-45ca-b495-f592f0025932

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_lipschitzWith_descending


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (n : ℕ),
    LipschitzWith 1 (descending : (Fin n → ℝ) → (Fin n → ℝ)) :=
  @Eden.lipschitzWith_descending
end EdenVerified
