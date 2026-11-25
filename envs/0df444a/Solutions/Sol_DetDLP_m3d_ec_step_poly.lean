-- Prove2me | solution 1 for DetDLP.m3d_ec_step_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:35:03.075813+00:00
-- url     : https://prove2.me/submissions/9a01a105-c376-44e9-8f72-27006184465d

import Definitions.Def_DetDLP_M3D_ECFastDefs
import Definitions.Def_DetDLP_W3C_BlockLookup
import Definitions.Def_DetDLP_W3C_NewtonPoly
import Definitions.Def_DetDLP_W3C_NineOracleLoop
import Definitions.Def_DetDLP_M3D_OrderEntry
import Definitions.Def_DetDLP_M3D_ECQueryOps

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DetDLP.M3D.Fast.ECStep
open Groundwork DetDLP.M3D.Fast.BlockLookup DetDLP.M3D.Fast.NineOracleLoop
open DetDLP.M3D.Fast.ECQueries DetDLP.M3D.Fast.ECQueryOps
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP_W1_Queries

variable {α : Type} [Enc α]

@[local fun_prop] theorem decodeFrames_poly_fast {f : α → Wd} (hf : PolyT f) :
    PolyT fun x => BlockLookup.decodeFrames (f x) := by
  change PolyT (fun x => DetDLP.W3C.BlockLookup.decodeFrames (f x))
  exact DetDLP.W3C.BlockLookup.decodeFrames_poly hf
@[local fun_prop] theorem decodeBlocks_poly_fast {f : α → Wd} (hf : PolyT f) :
    PolyT fun x => BlockLookup.decodeBlocks (f x) := by
  change PolyT (fun x => DetDLP.W3C.BlockLookup.decodeBlocks (f x))
  exact DetDLP.W3C.BlockLookup.decodeBlocks_poly hf
@[local fun_prop] theorem initRowCounts_poly_fast {b : α → Blocks} {u : α → List Wd} {j : α → ℕ}
    (hb : PolyT b) (hu : PolyT u) (hj : PolyT j) :
    PolyT fun x => BlockLookup.initRowCounts (b x) (u x) (j x) := by
  change PolyT (fun x => DetDLP.W3C.BlockLookup.initRowCounts (b x) (u x) (j x))
  exact DetDLP.W3C.BlockLookup.initRowCounts_poly hb hu hj
@[local fun_prop] theorem shiftRowCounts_poly_fast {b : α → Blocks} {x y : α → List Wd}
    (hb : PolyT b) (hx : PolyT x) (hy : PolyT y) :
    PolyT fun t => BlockLookup.shiftRowCounts (b t) (x t) (y t) := by
  change PolyT (fun t => DetDLP.W3C.BlockLookup.shiftRowCounts (b t) (x t) (y t))
  exact DetDLP.W3C.BlockLookup.shiftRowCounts_poly hb hx hy
@[local fun_prop] theorem largeCheck_poly_fast {p M : α → ℕ} (hp : PolyT p) (hM : PolyT M) :
    PolyT fun x => NewtonPoly.largeCheck (p x) (M x) := by
  change PolyT (fun x => DetDLP.W3C.NewtonPoly.largeCheck (p x) (M x))
  exact DetDLP.W3C.NewtonPoly.largeCheck_poly hp hM
@[local fun_prop] theorem massPosWord_poly_fast {m M p : α → ℕ} {w : α → Wd}
    (hm : PolyT m) (hM : PolyT M) (hp : PolyT p) (hw : PolyT w) :
    PolyT fun x => NewtonPoly.massPosWord (m x) (M x) (p x) (w x) := by
  change PolyT (fun x => DetDLP.W3C.NewtonPoly.massPosWord (m x) (M x) (p x) (w x))
  exact DetDLP.W3C.NewtonPoly.massPosWord_poly hm hM hp hw
@[local fun_prop] theorem updateWord_poly_fast {M N rhs : α → ℕ} {rep : α → Wd} {row : α → List ℕ}
    (hm : PolyT M) (hn : PolyT N) (hr : PolyT rep) (ha : PolyT row) (hb : PolyT rhs) :
    PolyT fun x => NewtonPoly.updateWord (M x) (N x) (rep x) (row x) (rhs x) := by
  change PolyT (fun x => DetDLP.W3C.NewtonPoly.updateWord (M x) (N x) (rep x) (row x) (rhs x))
  exact DetDLP.W3C.NewtonPoly.updateWord_poly hm hn hr ha hb
@[local fun_prop] theorem repLabels_poly_fast {r : α → Wd} (hr : PolyT r) :
    PolyT fun x => NewtonPoly.repLabels (r x) := by
  change PolyT (fun x => DetDLP.W3C.NewtonPoly.repLabels (r x))
  exact DetDLP.W3C.NewtonPoly.repLabels_poly hr
@[local fun_prop] theorem tag9_poly_fast (j : Fin 9) : PolyT (NineOracleLoop.tag9 j) := by
  change PolyT (DetDLP.W3C.NineOracleLoop.tag9 j)
  exact DetDLP.W3C.NineOracleLoop.tag9_poly j
@[local fun_prop] theorem planWord_poly_fast {w : α → Wd} (hw : PolyT w) :
    PolyT fun x => ECQueryOps.planWord (w x) := by
  change PolyT (fun x => DetDLP.M3D.ECQueryOps.planWord (w x))
  exact DetDLP.M3D.ECQueryOps.planWord_poly hw
@[local fun_prop] theorem primeField_poly_fast : PolyT ECQueries.primeField := by
  change PolyT DetDLP.M3D.ECQueries.primeField
  exact DetDLP.M3D.ECQueries.primeField_poly
@[local fun_prop] theorem curveWord_poly_fast : PolyT ECQueries.curveWord := by
  change PolyT DetDLP.M3D.ECQueries.curveWord
  exact DetDLP.M3D.ECQueries.curveWord_poly
@[local fun_prop] theorem elemWord_poly_fast {w : α → Wd} {bs : α → Blocks} {j : α → ℕ}
    (hw : PolyT w) (hb : PolyT bs) (hj : PolyT j) :
    PolyT fun x => ECQueryOps.elemWord (w x) (bs x) (j x) := by
  change PolyT (fun x => DetDLP.M3D.ECQueryOps.elemWord (w x) (bs x) (j x))
  exact DetDLP.M3D.ECQueryOps.elemWord_poly hw hb hj
@[local fun_prop] theorem unitGenRow_poly_fast {bs : α → Blocks} (hb : PolyT bs) :
    PolyT fun x => ECQueryOps.unitGenRow (bs x) := by
  change PolyT (fun x => DetDLP.M3D.ECQueryOps.unitGenRow (bs x))
  exact DetDLP.M3D.ECQueryOps.unitGenRow_poly hb
@[local fun_prop] theorem prefixToTupleWords_poly_fast {b m : α → ℕ} {s : α → Wd}
    (hb : PolyT b) (hm : Unary (fun x => 2*m x)) (hmp : PolyT m) (hs : PolyT s) :
    PolyT fun x => ECQueryOps.prefixToTupleWords (b x) (m x) (s x) := by
  change PolyT (fun x => DetDLP.M3D.ECQueryOps.prefixToTupleWords (b x) (m x) (s x))
  exact DetDLP.M3D.ECQueryOps.prefixToTupleWords_poly hb hm hmp hs
@[local fun_prop] theorem nativePayload_poly_fast {b m M : α → ℕ} {inp plan blk rep pre : α → Wd}
    (hb : PolyT b) (hm : Unary m) (hM : PolyT M) (hi : PolyT inp) (hp : PolyT plan)
    (hk : PolyT blk) (hr : PolyT rep) (hf : PolyT pre) :
    PolyT fun x => ECQueryOps.nativePayload (b x) (m x) (M x) (inp x) (plan x) (blk x) (rep x) (pre x) := by
  change PolyT (fun x => DetDLP.M3D.ECQueryOps.nativePayload (b x) (m x) (M x) (inp x) (plan x) (blk x) (rep x) (pre x))
  exact DetDLP.M3D.ECQueryOps.nativePayload_poly hb hm hM hi hp hk hr hf
@[local fun_prop] theorem scalar_poly_fast : PolyT DetDLP_M3D_scalar := by
  change PolyT DetDLP.DetDLP_M3D_scalar
  exact DetDLP.m3d_scalar_poly
@[local fun_prop] theorem orderQuery_poly_fast : PolyT DetDLP_M3D_orderQuery := by
  change PolyT DetDLP.DetDLP_M3D_orderQuery
  exact DetDLP.m3d_orderQuery_poly

attribute [local fun_prop] PolyT.comp PolyT.fst PolyT.snd PolyT.prodMk PolyT.const PolyT.map
  PolyT.flatMap PolyT.append PolyT.length PolyT.getD PolyT.tail PolyT.headD PolyT.bval' PolyT.mod
  PolyT.mul PolyT.decide_eq PolyT.decide_lt PolyT.ite' PolyT.flatten PolyT.reverse PolyT.take
  frame_poly first_poly more_poly w5_M6Sort.cw_poly w5_M6Sort.encode_poly
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_ite__226169acf219 scalar_poly_fast orderQuery_poly_fast S8G.FpMoment.Code.width_poly

@[local fun_prop] theorem frP {f : α → St} (h : PolyT f) : PolyT fun x => fr (f x) := by
  have he (l : St) : fr l = l.flatMap (fun u => true :: frame u) ++ [false] := by
    induction l with
    | nil => rfl
    | cons w l ih => change true :: (Encoding.frame w ++ fr l) = _; simp [ih,List.flatMap,List.append_assoc]
  simp only [he]; fun_prop
@[local fun_prop] theorem packP {ph j : α → ℕ} {i o p k r f a : α → Wd}
    (h₁ : PolyT ph) (h₂ : PolyT j) (h₃ : PolyT i) (h₄ : PolyT o) (h₅ : PolyT p)
    (h₆ : PolyT k) (h₇ : PolyT r) (h₈ : PolyT f) (h₉ : PolyT a) :
    PolyT fun x => packState (ph x) (j x) (i x) (o x) (p x) (k x) (r x) (f x) (a x) := by
  unfold packState; exact P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const false) (frP (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly h₁) (P2M_Groundwork_PolyT_cons__3a60f43a3b86 h₃ (P2M_Groundwork_PolyT_cons__3a60f43a3b86 h₄ (P2M_Groundwork_PolyT_cons__3a60f43a3b86 h₅ (P2M_Groundwork_PolyT_cons__3a60f43a3b86 h₆ (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly h₂) (P2M_Groundwork_PolyT_cons__3a60f43a3b86 h₇ (P2M_Groundwork_PolyT_cons__3a60f43a3b86 h₈ (P2M_Groundwork_PolyT_cons__3a60f43a3b86 h₉ (PolyT.const [])))))))))))
@[local fun_prop] theorem sendP {s q : α → Wd} (j : Fin 9) (hs : PolyT s) (hq : PolyT q) :
    PolyT fun x => send j (s x) (q x) := by
  have ht := (tag9_poly_fast j).comp hq
  unfold send pairWord; fun_prop
@[local fun_prop] theorem intsP {M : α → ℕ} {r : α → List ℤ} (hm : PolyT M) (hr : PolyT r) :
    PolyT fun x => ints (M x) (r x) := by unfold ints; fun_prop
@[local fun_prop] theorem idRepP {bs : α → Blocks} (h : PolyT bs) : PolyT fun x => idRep (bs x) := by
  have hr : PolyT fun x => inds (bs x) := PolyT.range (Unary.of_length (by fun_prop : PolyT fun x => [] :: [] :: (bs x).flatten))
  unfold idRep; fun_prop
@[local fun_prop] theorem getP {s : α → St} (i : ℕ) (h : PolyT s) : PolyT fun x => get (s x) i := by unfold get; fun_prop
@[local fun_prop] theorem field_inp {s : α → St} (h : PolyT s) : PolyT fun x => inp (s x) := by unfold inp; fun_prop
@[local fun_prop] theorem field_ord {s : α → St} (h : PolyT s) : PolyT fun x => ord (s x) := by unfold ord; fun_prop
@[local fun_prop] theorem field_plan {s : α → St} (h : PolyT s) : PolyT fun x => plan (s x) := by unfold plan; fun_prop
@[local fun_prop] theorem field_blk {s : α → St} (h : PolyT s) : PolyT fun x => blk (s x) := by unfold blk; fun_prop
@[local fun_prop] theorem field_idx {s : α → St} (h : PolyT s) : PolyT fun x => idx (s x) := by unfold idx; fun_prop
@[local fun_prop] theorem field_rep {s : α → St} (h : PolyT s) : PolyT fun x => rep (s x) := by unfold rep; fun_prop
@[local fun_prop] theorem field_pre {s : α → St} (h : PolyT s) : PolyT fun x => pre (s x) := by unfold pre; fun_prop
@[local fun_prop] theorem field_aux {s : α → St} (h : PolyT s) : PolyT fun x => aux (s x) := by unfold aux; fun_prop
@[local fun_prop] theorem field_bs {s : α → St} (h : PolyT s) : PolyT fun x => bs (s x) := by unfold bs; fun_prop
@[local fun_prop] theorem field_M {s : α → St} (h : PolyT s) : PolyT fun x => M (s x) := by unfold M; fun_prop
@[local fun_prop] theorem field_n {s : α → St} (h : PolyT s) : PolyT fun x => n (s x) := by unfold n; fun_prop
@[local fun_prop] theorem mP {s : α → St} (h : PolyT s) : PolyT fun x => m (s x) := by unfold m bs blk get; fun_prop
@[local fun_prop] theorem bP {s : α → St} (h : PolyT s) : PolyT fun x => b (s x) := by unfold b inp get; fun_prop
@[local fun_prop] theorem payloadP {s : α → St} {r f : α → Wd} (h : PolyT s) (hr : PolyT r) (hf : PolyT f) :
    PolyT fun x => payload (s x) (r x) (f x) := by
  have hbs : PolyT fun x => bs (s x) := by unfold bs blk get; fun_prop
  exact nativePayload_poly_fast (bP h) (Unary.of_length hbs) (scalar_poly_fast.comp (by fun_prop : PolyT fun x => ord (s x)))
    (by fun_prop) (by fun_prop) (by fun_prop) hr hf
@[local fun_prop] theorem beginP {s : α → St} {r : α → Wd} (h : PolyT s) (hr : PolyT r) :
    PolyT fun x => beginRoot (s x) (r x) := by unfold beginRoot; fun_prop
@[local fun_prop] theorem decompP {s : α → St} {j : α → ℕ} {r : α → Wd} (h : PolyT s) (hj : PolyT j) (hr : PolyT r) :
    PolyT fun x => decompose (s x) (j x) (r x) := by unfold decompose; fun_prop
@[local fun_prop] theorem cutP {s : α → St} {f : α → Wd} (h : PolyT s) (hf : PolyT f) :
    PolyT fun x => cutOrChild (s x) (f x) := by
  have hh : PolyT fun x => bs (s x) ++ bs (s x) := by unfold bs blk get; fun_prop
  have hu : Unary (fun x => 2*m (s x)) := by simpa only [List.length_append,two_mul,m] using Unary.of_length hh
  have xy : PolyT fun x => prefixToTupleWords (b (s x)) (m (s x)) (f x) := prefixToTupleWords_poly_fast (bP h) hu (mP h) hf
  have hbs : PolyT fun x => bs (s x) := by unfold bs blk get; fun_prop
  have hM : PolyT fun x => M (s x) := scalar_poly_fast.comp (by fun_prop : PolyT fun x => ord (s x))
  have hrow := intsP hM (shiftRowCounts_poly_fast hbs (PolyT.fst xy) (PolyT.snd xy))
  have hlim := PolyT.mul (PolyT.mul (PolyT.const (α := α) 4) (mP h)) (PolyT.mul (PolyT.const 3) (bP h))
  unfold cutOrChild; dsimp only; apply P2M_Groundwork_PolyT_ite__226169acf219
  · exact PolyT.decide_lt (PolyT.length hf) hlim
  · apply sendP <;> fun_prop
  · apply sendP
    · apply packP <;> fun_prop
    · exact updateWord_poly_fast hM (field_n h) (field_rep h) hrow (PolyT.const 1)
@[local fun_prop] theorem massP {s : α → St} {a : α → Wd} (h : PolyT s) (ha : PolyT a) :
    PolyT fun x => massPhase (s x) (a x) := by
  have hp : PolyT fun x => NewtonPoly.massPosWord (m (s x)) (M (s x))
      (PolyT.bval ((decodeFrames (aux (s x))).getD 6 [])) (a x) := by
    exact massPosWord_poly_fast (mP h) (field_M h) (by fun_prop) ha
  have hchosen : PolyT fun x => pre (s x) ++ [!NewtonPoly.massPosWord (m (s x)) (M (s x))
      (PolyT.bval ((decodeFrames (aux (s x))).getD 6 [])) (a x)] := by fun_prop
  have hcut : PolyT fun x => cutOrChild (s x)
      (pre (s x) ++ [!NewtonPoly.massPosWord (m (s x)) (M (s x))
        (PolyT.bval ((decodeFrames (aux (s x))).getD 6 [])) (a x)]) := cutP h hchosen
  unfold massPhase; dsimp only; fun_prop

@[local fun_prop] theorem case0P {s : α → St} {a : α → Wd} (h : PolyT s) (ha : PolyT a) :
    PolyT fun x => case0 (s x) (a x) := by
  have hd : PolyT fun x => DetDLP_M3D_dispatch (inp (s x)) (a x) :=
    largeCheck_poly_fast (scalar_poly_fast.comp (field_inp h)) (scalar_poly_fast.comp ha)
  unfold case0; fun_prop
@[local fun_prop] theorem case1P {s : α → St} {a : α → Wd} (_h : PolyT s) (ha : PolyT a) :
    PolyT fun x => case1 (s x) (a x) := by unfold case1; fun_prop
@[local fun_prop] theorem case2P {s : α → St} {a : α → Wd} (_h : PolyT s) (ha : PolyT a) :
    PolyT fun x => case2 (s x) (a x) := by unfold case2; fun_prop
@[local fun_prop] theorem case3P {s : α → St} {a : α → Wd} (h : PolyT s) (ha : PolyT a) :
    PolyT fun x => case3 (s x) (a x) := by unfold case3; fun_prop
@[local fun_prop] theorem case4P {s : α → St} {a : α → Wd} (h : PolyT s) (ha : PolyT a) :
    PolyT fun x => case4 (s x) (a x) := by unfold case4; fun_prop
@[local fun_prop] theorem case6P {s : α → St} {a : α → Wd} (h : PolyT s) (ha : PolyT a) :
    PolyT fun x => case6 (s x) (a x) := by unfold case6; fun_prop
@[local fun_prop] theorem case7P {s : α → St} {a : α → Wd} (h : PolyT s) (ha : PolyT a) :
    PolyT fun x => case7 (s x) (a x) := by unfold case7; fun_prop
@[local fun_prop] theorem case8P {s : α → St} {a : α → Wd} (h : PolyT s) (ha : PolyT a) :
    PolyT fun x => case8 (s x) (a x) := by unfold case8; fun_prop
@[local fun_prop] theorem case9P {s : α → St} {a : α → Wd} (h : PolyT s) (ha : PolyT a) :
    PolyT fun x => case9 (s x) (a x) := by unfold case9; fun_prop
@[local fun_prop] theorem roundP {s : α → St} {a : α → Wd} (h : PolyT s) (ha : PolyT a) :
    PolyT fun x => round (s x) (a x) := by
  have hph : PolyT fun x => PolyT.bval (get (s x) 0) := by fun_prop
  exact P2M_Groundwork_PolyT_ite__226169acf219
    (PolyT.decide_eq hph (PolyT.const 0)) (case0P h ha) <|
    P2M_Groundwork_PolyT_ite__226169acf219
      (PolyT.decide_eq hph (PolyT.const 1)) (case1P h ha) <|
    P2M_Groundwork_PolyT_ite__226169acf219
      (PolyT.decide_eq hph (PolyT.const 2)) (case2P h ha) <|
    P2M_Groundwork_PolyT_ite__226169acf219
      (PolyT.decide_eq hph (PolyT.const 3)) (case3P h ha) <|
    P2M_Groundwork_PolyT_ite__226169acf219
      (PolyT.decide_eq hph (PolyT.const 4)) (case4P h ha) <|
    P2M_Groundwork_PolyT_ite__226169acf219
      (PolyT.decide_eq hph (PolyT.const 6)) (case6P h ha) <|
    P2M_Groundwork_PolyT_ite__226169acf219
      (PolyT.decide_eq hph (PolyT.const 7)) (case7P h ha) <|
    P2M_Groundwork_PolyT_ite__226169acf219
      (PolyT.decide_eq hph (PolyT.const 8)) (case8P h ha) <|
    P2M_Groundwork_PolyT_ite__226169acf219
      (PolyT.decide_eq hph (PolyT.const 9)) (case9P h ha) (beginP h ha)

theorem ecStep_poly_fast : PolyT ecStep := by
  have he : DetDLP.M3D.Fast.ECStep.ecStep = DetDLP.M3D.Fast.ECStep.ecStep := rfl
  unfold ecStep; fun_prop
end DetDLP.M3D.Fast.ECStep

open DetDLP
theorem solution : Groundwork.PolyT DetDLP.M3D.Fast.ECStep.ecStep := by
  exact DetDLP.M3D.Fast.ECStep.ecStep_poly_fast
