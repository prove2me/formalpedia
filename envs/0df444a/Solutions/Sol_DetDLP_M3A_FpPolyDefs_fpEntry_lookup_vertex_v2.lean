-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.fpEntry_lookup_vertex_v2
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T05:23:21.264348+00:00
-- url     : https://prove2.me/submissions/de90f31d-6546-4389-a560-1bb22702b570

import Theorems.Thm_DetDLP_M3A_FpPolyDefs_coeff_spec
import Definitions.Def_DetDLP_W3_IncQueryBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [-simp] Fin.natAdd_eq_addNat
open DetDLP DetDLP.M3A DetDLP.M3A.FpPolyDefs S8J S8H.PointAddresses Groundwork DetDLP.w4_M5Network

namespace DetDLP.M3A.FpPolyDefs

private theorem lookup_bin_spec (q : w3_Query) (pos : Bool) (z : ℕ) :
    EncodesTruncPoly (w3_precision q) (w3_len q)
      (encodeNatListBin ((List.range (w3_len q)).map (coeff pos z (2^w3_precision q))))
      (w3_binWord q (if pos then (z:ℤ) else -(z:ℤ))) := by
  let c (i : Fin (w3_len q)) := coeff pos z (2^w3_precision q) i.val
  refine ⟨c,fun i => ?_,?_,?_⟩
  · unfold c; rw [coeff_spec]; exact ZMod.val_lt _
  · congr 1
    rw [List.ofFn_eq_map, show List.range (w3_len q) = (List.finRange (w3_len q)).map Fin.val by simp,List.map_map]
    rfl
  · simp only [w3_binWord,truncPolyOfCoeffs,c,coeff_spec,ZMod.natCast_zmod_val]

private theorem lookup_miss (q : w3_Query) : EncodesTruncPoly (w3_precision q) (w3_len q)
    (indicator (w3_len q) false) 0 := by
  refine ⟨fun _ => 0,fun _ => Nat.two_pow_pos _,?_,?_⟩
  · unfold indicator; congr 1
    rw [List.ofFn_eq_map,show List.range (w3_len q) = (List.finRange (w3_len q)).map Fin.val by simp,List.map_map]
    simp [Function.comp_def]
  · simp [truncPolyOfCoeffs]

private theorem bval_ofFn_bitsToNat {d : ℕ} (a : Fin d → Bool) :
    PolyT.bval (List.ofFn a) = bitsToNat a := by
  induction d with
  | zero => simp [PolyT.bval, bitsToNat]
  | succ d ih =>
    rw [List.ofFn_succ, PolyT.bval_cons]
    rw [bitsToNat, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [ih (fun i => a i.succ)]
    simp only [← Nat.mul_assoc, ← Finset.sum_mul, bitsToNat]
    cases h : a 0 <;> simp [Nat.mul_comm, Nat.add_comm]

private theorem lookup_scan_inline (q : w3_Query) (w : W) (s : ℕ) (a : W) (i : Fin q.m)
    (hs : s%m w=i.val) (hp : prec w=w3_precision q) (hn : len w=w3_len q)
    (hl : ((blocks w).getD i.val []).length=(q.FB.blocks i).length)
    (hash : ℕ → ℕ)
    (hc : ∀ x, hash x = ((nums (field w 1)).getD (2*i.val) 0*x+(nums (field w 1)).getD (2*i.val+1) 0)%prime w)
    (ha : ∀ r : Fin (q.FB.blocks i).length,
      hash (((blocks w).getD i.val []).getD r.val 0) = q.addr i r)
    (hy : ∀ r : Fin (q.FB.blocks i).length,
      num (field w 3) ((((blocks w).take i.val).map List.length).sum+r.val) = (q.y (q.FB.coordOf i r)).val)
    (inj : Function.Injective (q.addr i)) :
    EncodesTruncPoly (w3_precision q) (w3_len q) (lookup w s a)
      (w3_addressWeight q i (decide (2*m w ≤ s)) (PolyT.bval a)) := by
  let l := (blocks w).getD i.val []
  let f (x : ℕ) := decide (hash x = PolyT.bval a)
  let u := l.findIdx f
  unfold lookup
  simp only [hs,← hc]
  change EncodesTruncPoly _ _ (if u<l.length then _ else _) _
  by_cases h : u<l.length
  · let r : Fin (q.FB.blocks i).length := ⟨u,hl ▸ h⟩
    have hget : l.getD r.val 0 = l[u] := List.getD_eq_getElem _ _ h
    have hh : hash l[u] = PolyT.bval a := of_decide_eq_true (List.findIdx_getElem (p:=f) (w:=h))
    have found := (w3_lookupIndex_eq_some_iff q i inj (PolyT.bval a) r).mpr
      ((ha r).symm.trans ((congrArg hash hget).trans hh))
    rw [if_pos h,w3_addressWeight,found]
    change EncodesTruncPoly _ _ (encodeNatListBin ((List.range (len w)).map (coeff _ (num (field w 3) (_+r.val)) _))) _
    rw [hy r,hp,hn]; exact lookup_bin_spec q _ _
  · have notfound : w3_lookupIndex q i (PolyT.bval a) = none := by
      cases he : w3_lookupIndex q i (PolyT.bval a) with
      | none => rfl
      | some r =>
        have hh := (w3_lookupIndex_eq_some_iff q i inj _ r).mp he
        have hr : r.val < l.length := hl.symm ▸ r.isLt
        have hget : l.getD r.val 0 = l[r.val] := List.getD_eq_getElem _ _ hr
        have hit : f l[r.val] = true := decide_eq_true ((congrArg hash hget).symm.trans ((ha r).trans hh))
        exact False.elim (h (List.findIdx_lt_length_of_exists ⟨_,List.getElem_mem hr,hit⟩))
    rw [if_neg h,w3_addressWeight,notfound,hn]; exact lookup_miss q

end DetDLP.M3A.FpPolyDefs

theorem DetDLP.M3A.FpPolyDefs.fpEntry_lookup_vertex_v2
    (q : w3_Query) (w : W) (A : w3_FactorLayout) (bus : Fin (4 * q.m) → Fin q.k → Fin A.nb)
    (t : w3_factorTest A)
    (sl : Fin (M3B.ECLayout.layout A bus).ng ≃ (w3_lookupSlot q ⊕ Fin A.ng))
    (addr : (v : Fin (w3_factorGraph (M3B.ECLayout.layout A bus)).nV) →
      (Fin ((w3_factorGraph (M3B.ECLayout.layout A bus)).deg v) → Bool) → ℕ)
    (hm : m w = q.m) (hp : prec w = w3_precision q) (hn : len w = w3_len q)
    (hng : (whole (m w) (d w) (k w) (pre w).length).ng = A.ng + 4 * q.m)
    (s : Fin (4 * q.m)) (blk : Fin q.m) (crd : Fin 2)
    (hblk : s.val % q.m = blk.val)
    (hsl : sl (Fin.natAdd A.ng s) = .inl (blk, crd, decide (2 * q.m ≤ s.val)))
    (haddr : ∀ values, addr (M3B.ECLayout.vertex A bus s) values =
      bitsToNat (fun j : Fin q.k => values (M3B.ECLayout.port A bus s j)))
    (hl : ((blocks w).getD blk.val []).length = (q.FB.blocks blk).length)
    (hash : ℕ → ℕ)
    (hc : ∀ x, hash x = ((nums (field w 1)).getD (2 * blk.val) 0 * x + (nums (field w 1)).getD (2 * blk.val + 1) 0) % prime w)
    (ha : ∀ r : Fin (q.FB.blocks blk).length,
      hash (((blocks w).getD blk.val []).getD r.val 0) = q.addr blk r)
    (hy : ∀ r : Fin (q.FB.blocks blk).length,
      num (field w 3) ((((blocks w).take blk.val).map List.length).sum + r.val) = (q.y (q.FB.coordOf blk r)).val)
    (inj : Function.Injective (q.addr blk))
    (a : Fin ((w3_factorGraph (M3B.ECLayout.layout A bus)).subdivision.deg
      ((w3_factorGraph (M3B.ECLayout.layout A bus)).oldVertex (M3B.ECLayout.vertex A bus s))) → Bool) :
    let G := w3_factorGraph (M3B.ECLayout.layout A bus)
    let v := G.oldVertex (M3B.ECLayout.vertex A bus s)
    EncodesTruncPoly (w3_precision q) (w3_len q) (fpEntry (encodePortQuery w v.val (List.ofFn a)))
      (w3_liftTensor G (w3_gateWeight (w3_incSlot (M3B.ECLayout.layout A bus) sl) addr
        (w3_factorChecks _ (M3B.ECLayout.test A bus t))) v a) := by
  let G := w3_factorGraph (M3B.ECLayout.layout A bus)
  let u := M3B.ECLayout.vertex A bus s
  let v := G.oldVertex u
  let localbits : Fin (G.deg u) → Bool := fun j => a (G.oldPort u j)
  have hslt : s.val < 4 * q.m := s.isLt
  have hmpos : 0 < q.m := by omega
  have hindex : v.val - ((whole (m w) (d w) (k w) (pre w).length).ng - 4*m w) = s.val := by
    change (↑(Fin.castAdd G.nE (Fin.castAdd A.nb (Fin.natAdd A.ng s))) -
      ((whole (m w) (d w) (k w) (pre w).length).ng - 4*m w)) = s.val
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    rw [hng, hm]
    omega
  have hbval : PolyT.bval (List.ofFn a) = bitsToNat (fun j : Fin q.k => localbits (M3B.ECLayout.port A bus s j)) := by
    rw [bval_ofFn_bitsToNat]
    have hd : G.subdivision.deg v = q.k := (G.subdivision_deg_oldVertex u).trans (M3B.ECLayout.lookup_degree A bus s)
    let idx (j : Fin q.k) := G.oldPort u (M3B.ECLayout.port A bus s j)
    let es := G.subdivision.ports v
    have sorted : es.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
    have getE (j : Fin q.k) : es.get (idx j) = G.leftHalf (M3B.ECLayout.edge A bus s j) := by
      change (G.subdivision.ports (G.oldVertex u)).get (G.oldPort u _) = _
      rw [G.get_oldPort, show (G.ports u).get (M3B.ECLayout.port A bus s j) = M3B.ECLayout.edge A bus s j from G.get_portIndex ..]
      apply if_pos
      apply congrArg (Fin.castAdd A.nb)
      simp [M3B.ECLayout.edge, M3B.ECLayout.layout, splitMap, M3B.ECLayout.row]
    have strict : StrictMono (fun j => Fin.cast hd (idx j)) := by
      intro i j hij
      change idx i < idx j
      apply (show StrictMono es.get from fun _ _ h => List.pairwise_iff_get.mp sorted _ _ h).lt_iff_lt.mp
      rw [getE, getE]
      change A.ne + (i.val + q.k * s.val) < A.ne + (j.val + q.k * s.val)
      exact Nat.add_lt_add_left (Nat.add_lt_add_right hij _) _
    have eqidx (j : Fin q.k) : idx j = Fin.cast hd.symm j := Fin.ext (congrArg (fun x : Fin q.k => x.val) (strict.apply_eq (x:=j)))
    change bitsToNat a = bitsToNat (fun j => a (idx j))
    simp_rw [eqidx]
    exact (show ∀ {b c : ℕ} (h : b = c) (f : Fin b → Bool), bitsToNat f = bitsToNat (fun j => f (Fin.cast h.symm j)) by intros b c h f; subst c; rfl) hd a
  have haddr' : addr u localbits = PolyT.bval (List.ofFn a) := by
    rw [haddr, hbval]
  have hslot : w3_incSlot (M3B.ECLayout.layout A bus) sl u = .inl (blk, crd, decide (2*q.m ≤ s.val)) := by
    change (w3_incSlot (M3B.ECLayout.layout A bus) sl) (Fin.castAdd A.nb (Fin.natAdd A.ng s)) = _
    simp [w3_incSlot, Equiv.trans_apply]
    erw [finSumFinEquiv_symm_apply_castAdd]
    simp [hsl]
  have htest : w3_factorChecks (M3B.ECLayout.layout A bus) (M3B.ECLayout.test A bus t) u localbits = true := by
    unfold w3_factorChecks u M3B.ECLayout.vertex
    erw [Fin.addCases_left]
    unfold M3B.ECLayout.test
    erw [Fin.addCases_right]
  have hweight : w3_liftTensor G
      (w3_gateWeight (w3_incSlot (M3B.ECLayout.layout A bus) sl) addr
        (w3_factorChecks _ (M3B.ECLayout.test A bus t))) v a =
      w3_addressWeight q blk (decide (2*q.m ≤ s.val)) (PolyT.bval (List.ofFn a)) := by
    unfold w3_liftTensor w4_M5Network.WireGraph.oldVertex
    erw [Fin.addCases_left]
    unfold w3_gateWeight
    rw [htest, if_pos rfl, hslot, haddr'] <;> rfl
  have hscan := DetDLP.M3A.FpPolyDefs.lookup_scan_inline q w s.val (List.ofFn a) blk
    (by rwa [hm]) hp hn hl hash hc ha hy inj
  dsimp only
  change EncodesTruncPoly (w3_precision q) (w3_len q)
    (fpEntry (encodePortQuery w v.val (List.ofFn a))) _
  have entry : fpEntry (encodePortQuery w v.val (List.ofFn a)) = lookup w s.val (List.ofFn a) := by
    change fpEntry (encodePortQuery w (A.ng + s.val) (List.ofFn a)) = _
    have hlt : A.ng + s.val < A.ng + 4*q.m := by omega
    have hcng := hng
    rw [hm] at hcng
    simp [fpEntry, encodePortQuery, DetDLP_W1_Queries.second, DetDLP_W1_Queries.third, hcng, hm, hlt]
  rw [entry, hweight]
  simpa [hm] using hscan

abbrev solution := @DetDLP.M3A.FpPolyDefs.fpEntry_lookup_vertex_v2
