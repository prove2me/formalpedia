-- Prove2me | solution 1 for DetDLP.m3b_ec_decoded_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T22:12:32.459978+00:00
-- url     : https://prove2.me/submissions/c54580fd-4a2a-4ab6-a97b-6fca45fbe09d

import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_W3C_BlockLookup
import Definitions.Def_DetDLP_W3_Separator

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP DetDLP.M3B.ECPolyDefs OAI.Algorithms.SubexponentialSAT
private theorem parsed (l : List W) : frames (Encoding.encodeList id l) = l := W3C.BlockLookup.decodeFrames_correct l

theorem solution (q : w3_Query) (hq : w3_ecQueries q) :
    let t := dimensions q.input
    t.1 = q.b ∧ t.2.1 = q.m ∧ t.2.2.1 = q.k ∧ t.2.2.2.2.1 = w3_precision q ∧ t.2.2.2.2.2 = w3_len q := by
  obtain ⟨p,ip,E,hE,_,_,_,_,_,_,_,s,F,hF,P,y,pre,rfl⟩ := hq
  letI := ecPointFintype E
  let g := Fintype.card E.toAffine.Point
  let m := blockCount (bitLen p)
  let T := hashThreshold p (g-1) m g
  let ss := (List.finRange m).flatMap fun i => [(s i false).1.val+1,(s i false).2.val,(s i true).1.val+1,(s i true).2.val]
  let d := [encodeCurveInput p E,encodeNatListBin (pointCoords P),encodeNatListBin [g,T],encodeNatListBin ss,encodeECFactorBlocks F,encodeNatListBin (List.ofFn fun j => (y j).val),pre]
  let u := dimensions (Encoding.encodeList id d)
  change u.1 = bitLen p ∧ u.2.1=m ∧ u.2.2.1=Nat.clog 2 (2*T) ∧ u.2.2.2.2.1 = 2+4*m*Nat.clog 2 (2*T)+dFilt (2*m)*Nat.clog 2 (2*(2*m)*g+2) ∧ u.2.2.2.2.2=dFilt (2*m)+1
  have l : ss.length = 4*m := by simp [ss,List.length_flatMap,Nat.mul_comm]
  simp only [u,dimensions,parsed,d,List.getD_cons_zero,List.getD_cons_succ,encodeCurveInput,w5_M6Sort.decode_encode,l,Nat.mul_div_cancel_left _ (by decide : 0 < 4),dFilt]
  norm_num [List.getD] <;> ring_nf <;> trivial
