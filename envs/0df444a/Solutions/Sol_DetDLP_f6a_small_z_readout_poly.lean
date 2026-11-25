-- Prove2me | solution 1 for DetDLP.f6a_small_z_readout_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:14:29.269869+00:00
-- url     : https://prove2.me/submissions/7e0e88e7-74c0-48be-acb4-924df6751f8d

import Mathlib
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_DetDLP_F6AReadout
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_Unary_of_length

open DetDLP Groundwork Groundwork.PolyT DetDLP.F6AReadout
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] Groundwork.PolyT.fst Groundwork.PolyT.snd
  Groundwork.PolyT.div_pow Groundwork.PolyT.mod P2M_Groundwork_PolyT_id__1c5d0f44cc8f

theorem solution : PolyT readout ∧ ∀ (z w P : ℕ) (u : List Bool),
    readout (z.bits, (2^w : ℕ).bits, (2^P : ℕ).bits, u) =
      encodeNatListBin (List.ofFn fun i : Fin u.length => z / (2^w)^i.val % (2^w) % (2^P)) := by
  constructor
  · unfold readout
    apply DetDLP.w5_M6Sort.encode_poly
    apply PolyT.map (f := fun (x : Input) (i : ℕ) => bval x.1 / (bval x.2.1)^i % bval x.2.1 % bval x.2.2.1)
    · fun_prop
    · exact PolyT.range (Unary.of_length (by fun_prop))
  · intro z w P u
    simp only [readout, bval_bits]
    congr 1
    apply List.ext_getElem <;> simp
