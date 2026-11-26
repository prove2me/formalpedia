-- Prove2me | solution 1 for Eden.multiset_lyapunovExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:05.454176+00:00
-- url     : https://prove2.me/submissions/d230c70b-6118-4127-a735-95ea5324fb12

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
import Theorems.Thm_Eden_lyapunovExponent_eq_descending
import Theorems.Thm_Eden_multiset_descending


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    Finset.univ.val.map (lyapunovExponent c p) = Finset.univ.val.map (factorExponents c p) := by
  have heq : lyapunovExponent c p = descending (factorExponents c p) :=
    funext (lyapunovExponent_eq_descending c p)
  rw [heq]
  exact multiset_descending (factorExponents c p)
end Eden
