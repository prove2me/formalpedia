-- Prove2me | solution 1 for DetDLP.w3_compile_wire_separator
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T21:38:10.022586+00:00
-- url     : https://prove2.me/submissions/6eb3d4c3-1d82-446e-a23d-e49316b791de

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_PolyTBridge
import Theorems.Thm_DetDLP_w3_m5_lookup_subdivision
import Theorems.Thm_DetDLP_w3_separator_nowrap
import Theorems.Thm_DetDLP_w3_separator_newton_readout

set_option autoImplicit false
open DetDLP DetDLP.w4_M5Network

private theorem w3_at_old {R : Type} [Zero R] [One R] (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) (v : Fin G.nV)
    (a : Fin (G.subdivision.deg (G.oldVertex v)) → Bool) :
    w3_liftTensor G T (G.oldVertex v) a = T v (fun j => a (G.oldPort v j)) := by
  simp only [w3_liftTensor,WireGraph.oldVertex,Fin.addCases_left]

private theorem w3_at_eq {R : Type} [Zero R] [One R] (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) (e : Fin G.nE)
    (a : Fin (G.subdivision.deg (G.equalityVertex e)) → Bool) :
    w3_liftTensor G T (G.equalityVertex e) a =
      (if a (G.equalityLeftPort e) = a (G.equalityRightPort e) then 1 else 0) := by
  simp only [w3_liftTensor,WireGraph.equalityVertex,Fin.addCases_right]

private theorem w3_weight_split {R : Type} [CommSemiring R] (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) (y : Fin G.subdivision.nE → Bool) :
    (∏ v, w3_liftTensor G T v (fun j => y ((G.subdivision.ports v).get j))) =
      (∏ v, T v (fun j => y (G.incidentHalf v ((G.ports v).get j)))) *
      ∏ e : Fin G.nE, (if y (G.leftHalf e) = y (G.rightHalf e) then (1:R) else 0) := by
  let f := fun v : Fin (G.nV+G.nE) => w3_liftTensor G T v (fun j => y ((G.subdivision.ports v).get j))
  change (∏ v, f v) = _
  rw [Fin.prod_univ_add f]
  congr 1
  · apply Finset.prod_congr rfl; intro v _
    change w3_liftTensor G T (G.oldVertex v) _ = _
    exact (w3_at_old G T v (fun j => y ((G.subdivision.ports (G.oldVertex v)).get j))).trans
      (congrArg (T v) (funext fun i => congrArg y (G.get_oldPort v i)))
  · apply Finset.prod_congr rfl; intro e _
    change w3_liftTensor G T (G.equalityVertex e) _ = _
    apply (w3_at_eq G T e (fun j => y ((G.subdivision.ports (G.equalityVertex e)).get j))).trans
    rw [G.get_equalityLeftPort,G.get_equalityRightPort]

private theorem w3_lifted_weight {R : Type} [CommSemiring R] (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) (x : Fin G.nE → Bool) :
    (∏ v, w3_liftTensor G T v (fun j => G.liftAssignment x ((G.subdivision.ports v).get j))) =
      (∏ v, T v (fun j => x ((G.ports v).get j))) := by
  rw [w3_weight_split]; simp only [G.lift_incidentHalf,G.lift_leftHalf,G.lift_rightHalf,if_true,Finset.prod_const_one,mul_one]

private theorem w3_mismatch {R : Type} [CommSemiring R] (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) {y : Fin G.subdivision.nE → Bool}
    (h : ¬∀ e, y (G.leftHalf e) = y (G.rightHalf e)) :
    (∏ v, w3_liftTensor G T v (fun j => y ((G.subdivision.ports v).get j))) = 0 := by
  classical
  push Not at h; obtain ⟨e,he⟩ := h
  rw [w3_weight_split]; apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he)

private theorem w3_pack_net (q : w3_Query) (C : ℕ) (W : w3_WireCore q C) (hm : 2 ≤ q.m) (hM : 2 ≤ q.M)
    (width : ∀ i : Fin q.m, (q.FB.blocks i).length ≤ 2^q.k) : ∃ n : w3_Net q C,
    n.S = W.S ∧ n.desc = W.desc ∧ n.G = W.G.subdivision ∧
    w3_packet n = w3_wirePacket W ∧
    ∀ (f : List Bool → List Bool),
      (∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
        EncodesTruncPoly (w3_precision q) (w3_len q) (f (encodePortQuery W.desc v.val (List.ofFn a))) (w3_liftTensor W.G W.T v a)) →
      ∀ (v : Fin n.G.nV) (a : Fin (n.G.deg v) → Bool),
        EncodesTruncPoly (w3_precision q) (w3_len q) (f (encodePortQuery n.desc v.val (List.ofFn a))) (n.T v a) := by
  classical
  obtain ⟨spec,hL,_⟩ := w3_m5_lookup_subdivision W.G W.L q.m q.k W.S _ W.lookup_count W.lookup_degrees W.orientation W.core_edges W.core_degrees W.equality_degree
  let ok := W.G.SubdivisionSatisfies W.checks
  let E : {y // ok y} ≃ {x // W.G.Satisfies W.checks x} :=
    { toFun := fun y => ⟨fun e => y.val (W.G.leftHalf e),((W.G.subdivisionSatisfies_iff W.checks y.val).1 y.property).2⟩,
      invFun := fun x => ⟨W.G.liftAssignment x.val,(W.G.lift_satisfies_iff W.checks x.val).2 x.property⟩,
      left_inv := fun y => Subtype.ext (W.G.lift_restrict_of_satisfies W.checks y.property),
      right_inv := fun x => Subtype.ext (funext (W.G.lift_leftHalf x.val)) }
  let e := E.trans W.decode
  have live (a : {y // ok y}) : (∏ v, w3_liftTensor W.G W.T v (fun j => a.val ((W.G.subdivision.ports v).get j))) = w3_pairWeight q (e a).val := by
    calc _ = ∏ v, w3_liftTensor W.G W.T v (fun j => W.G.liftAssignment (E a).val ((W.G.subdivision.ports v).get j)) := by
                      rw [show W.G.liftAssignment (E a).val = a.val from W.G.lift_restrict_of_satisfies W.checks a.property]
         _ = _ := (w3_lifted_weight W.G W.T (E a).val).trans (W.live (E a))
  have dead (a : Fin W.G.subdivision.nE → Bool) (ha : ¬ok a) : (∏ v, w3_liftTensor W.G W.T v (fun j => a ((W.G.subdivision.ports v).get j))) = 0 := by
    by_cases h : ∀ e, a (W.G.leftHalf e) = a (W.G.rightHalf e)
    · let x := fun e => a (W.G.leftHalf e)
      have he : W.G.liftAssignment x = a := by
        funext f; refine Fin.addCases (motive := fun f => W.G.liftAssignment x f = a f) (fun j => W.G.lift_leftHalf x j) (fun j => ?_) f
        exact (W.G.lift_rightHalf x j).trans (h j)
      have hn : ¬W.G.Satisfies W.checks x := fun hx => ha ((W.G.subdivisionSatisfies_iff W.checks a).2 ⟨h,hx⟩)
      exact he ▸ (w3_lifted_weight W.G W.T x).trans (W.dead x hn)
    · exact w3_mismatch W.G W.T h
  have hb := w3_separator_nowrap q width
  let n : w3_Net q C :=
    { G := W.G.subdivision, S := W.S, desc := W.desc, T := w3_liftTensor W.G W.T
      spec := spec, shape := W.shape, coreOK := ok, decode := e, live_weight := live, dead_weight := dead
      nowrap := hb, readout := fun c _ => w3_separator_newton_readout q hm hM _ _ ok e live dead hb c }
  exact ⟨n,rfl,rfl,rfl,by simp only [w3_packet,w3_wirePacket,n,hL],fun _ hf => hf⟩

private theorem w3_absorb {n s c t K : ℕ} (hlen : n+1 ≤ (s+1)^c) (ht : t ≤ K) (hk : c*t ≤ K) : polyBound t n ≤ polyBound K s := by
  have h : (n:ℝ)+1 ≤ ((s:ℝ)+1)^c := by exact_mod_cast hlen
  have hh : 1 ≤ (s:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) s]
  calc polyBound t n ≤ (t:ℝ)*(((s:ℝ)+1)^c)^t := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h t) (by positivity)
       _ ≤ polyBound K s := by rw [← pow_mul]; exact mul_le_mul (by exact_mod_cast ht) (pow_le_pow_right₀ hh hk) (by positivity) (by positivity)

theorem solution (fam : w3_Query → Prop)
    (params : ∀ q, fam q → 2 ≤ q.m ∧ 2 ≤ q.M ∧ ∀ i, (q.FB.blocks i).length ≤ 2^q.k)
    (raw : w3_polyWireFamily fam) : w3_Separator fam := by
  classical
  obtain ⟨C,c,build,entry,hC,hc,hb,he,H⟩ := raw
  obtain ⟨B,ob,b,runb⟩ := PolyTBridge.polyT_listBool_runsWithin build hb
  obtain ⟨A,oa,t,rune⟩ := PolyTBridge.polyT_listBool_runsWithin entry he
  let K := c+b+t+c*t
  refine ⟨C,K,B,ob,A,oa,hC,by dsimp [K]; omega,?_⟩
  intro q hq
  obtain ⟨W,hpacket,hV,heval⟩ := H q hq
  obtain ⟨hm,hM,hw⟩ := params q hq
  obtain ⟨n,hS,hd,hG,hpkt,he'⟩ := w3_pack_net q C W hm hM hw
  refine ⟨n,?_,?_,?_⟩
  · rw [hG,hS,hd]; exact hV.trans (Nat.pow_le_pow_right (by omega) (by dsimp [K]; omega))
  · have hsize : polyBound b q.input.length ≤ polyBound K q.input.length := w3_absorb (c:=1) (by simp) (by dsimp [K]; omega) (by dsimp [K]; omega)
    rw [hpkt,←hpacket]; exact PolyTBridge.runsWithin_mono_local (runb q.input) hsize hsize
  · intro v a
    let inp := encodePortQuery n.desc v.val (List.ofFn a)
    refine ⟨entry inp,he' entry (fun v a => (heval v a).2) v a,?_⟩
    have htt : ∀ (v : Fin n.G.nV) (a : Fin (n.G.deg v) → Bool),
        (encodePortQuery n.desc v.val (List.ofFn a)).length+1 ≤ (n.S+n.desc.length+1)^c := by
      rw [hG,hS,hd]; exact fun v a => (heval v a).1
    have hh : polyBound t inp.length ≤ polyBound K (n.S+n.desc.length) :=
      w3_absorb (htt v a) (by dsimp [K]; omega) (by dsimp [K]; omega)
    exact PolyTBridge.runsWithin_mono_local (rune inp) hh hh
