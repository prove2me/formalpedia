-- Prove2me | solution 1 for Eden.antitone_eq_of_multiset_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:42.239268+00:00
-- url     : https://prove2.me/submissions/0d9da368-45ca-4687-8dd3-fecf91321656

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_SingularValues
import Mathlib.Data.List.Sort
import Mathlib.Order.Fin.Basic
import Definitions.Def_Eden_OrderedStationarySpectrum

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {n : ℕ} {a b : Fin n → ℝ}
    (ha : Antitone a) (hb : Antitone b)
    (hm : Finset.univ.val.map a = Finset.univ.val.map b) : a = b := by
  rw [Fin.univ_val_map, Fin.univ_val_map] at hm
  apply List.ofFn_injective
  exact (Multiset.coe_eq_coe.mp hm).eq_of_sortedGE ha.sortedGE_ofFn hb.sortedGE_ofFn
end Eden
