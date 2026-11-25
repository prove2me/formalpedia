-- Prove2me | solution 1 for DetDLP.m3b_ec_body_degree
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:31:27.876497+00:00
-- url     : https://prove2.me/submissions/20974e36-2b4f-4cde-ae41-78d2a80ac57b

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_S8H0_GraphDegree

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP DetDLP.S8H0 DetDLP.M3B RegisterMap NamedBlocks GateRoutes GateSemantics GraphDegree ECChainBlocks

private theorem manyBound {n D l : ℕ} (f : Fin n → B l) (h : ∀ j, good (f j) D) : good (manyB n f) D := by
  induction n with
  | zero => exact fun j => j.elim0
  | succ n ih => exact join_ok _ _ (h 0) (ih _ (fun j => h j.succ))

private theorem hashBound {s : Shape} (p : ℕ) (w : HashRows.Wires (d p) (hd p) s) : good (HashRows.block p w) (cap p) := by
  unfold HashRows.block HashRows.product
  refine join_ok _ _ (join_ok _ _ (join_ok _ _ (mul_ok p w.mul1) ?_) (join_ok _ _ (mul_ok p w.mul2) ?_)) (join_ok _ _ ?_ (join_ok _ _ ?_ ?_))
  all_goals first | exact mono (row_ok _ 2 _ _) (small p 2 (by decide)) | exact mono (add_ok _ _ _ _ _) (small p 5 (by decide))

private theorem mapGate {s : Shape} (p : ℕ) (a x b : HashRows.Word s) (f : Path (ECMapRows.slot (d p) (e p)) s) :
    good (ECMapRows.slotBlock (hd p) p a x b f) (cap p) := by
  simp only [ECMapRows.slotBlock,e,le_refl,if_true]; apply hashBound

private theorem rBound {s : Shape} (p n u : ℕ) (r : Fin n → Fin u → Ref s) (test : Fin n → (Fin u → Bool) → Bool) (h : u ≤ 12) :
    good (rows n u r test) (cap p) := mono (row_ok _ _ _ _) (small _ _ h)
private theorem ck {s : Shape} {n : ℕ} (p : ℕ) (r : Path (triple n) s) : good (RangeRows.checker p r) (cap p) := mono (add_ok _ _ _ _ _) (small _ _ (by decide))
private theorem eqBound {s : Shape} (p n : ℕ) (l r : Fin n → Ref s) : good (eqs n l r) (cap p) := rBound _ _ _ _ _ (by decide)

private theorem mapBound {s : Shape} (p a b c : ℕ) (i : Ref s) (x y : HashRows.Word s) (f : Path (ECMapRows.mapShape (d p) (e p)) s) :
    good (ECMapRows.mapBlock (hd p) p a b c i x y f) (cap p) := by
  unfold ECMapRows.mapBlock
  apply join_ok
  · apply join_ok
    · exact join_ok _ _ (ck _ _) (ck _ _)
    · exact many_ok _ _ fun _ => join_ok _ _ (ck _ _) (ck _ _)
  · exact join_ok _ _ (many_ok _ _ fun _ => mapGate _ _ _ _ _) (join_ok _ _ (eqBound _ _ _ _) (join_ok _ _ (rBound _ _ _ _ _ (by decide)) (rBound _ _ _ _ _ (by decide))))

private theorem addBound {s : Shape} (p a b c t : ℕ) (i j : Ref s) (x y z w : HashRows.Word s) (f : Path (ECAddRows.addShape (d p) (e p)) s) :
    good (ECAddRows.addBlock (hd p) p a b c t i j x y z w f) (cap p) := by
  unfold ECAddRows.addBlock; apply join_ok
  · apply join_ok
    · exact join_ok _ _ (ck _ _) (ck _ _)
    · exact join_ok _ _ (many_ok _ _ fun _ => ck _ _) (many_ok _ _ fun _ => join_ok _ _ (ck _ _) (ck _ _))
  · apply join_ok _ _ (many_ok _ _ fun _ => mapGate _ _ _ _ _)
    repeat' first | apply join_ok | exact rBound _ _ _ _ _ (by decide)

private theorem chainBound {s : Shape} {p n : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (f : Path (Chain p n) s) (input : Fin (n+1) → Wires s) (term : Path (PointCell (d p)) s) : good (chainBlock E f input term) (cap p) := by
  refine join_ok _ _ (manyBound _ (fun _ => mapBound _ _ _ _ _ _ _ _)) (join_ok _ _ (manyBound _ (fun _ => addBound _ _ _ _ _ _ _ _ _ _ _ _)) ?_)
  unfold pointEq tripleEq wordEqB; repeat' first | apply join_ok | exact eqBound _ _ _ _

private theorem bankBound {s : Shape} {n d : ℕ} (p T : ℕ) (I : ECArithNet.Inputs s n d) : good (ECArithNet.bank I T) (cap p) := by
  induction n with
  | zero => exact fun j => j.elim0
  | succ n ih =>
    let tail : ECArithNet.Inputs s n d := ⟨fun j => I.parity j.succ,fun j => I.hash j.succ,fun j => I.selected j.succ,fun j => I.addr j.succ,fun j => I.carry j.succ⟩
    exact join_ok _ _ (join_ok _ _ (rBound _ _ 2 _ _ (by decide)) (mono (add_ok _ _ _ _ _) (small p 5 (by decide)))) (ih tail)

private theorem slotBound {s : Shape} {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m) (b : Fin m) (T : ℕ) (z : ECArithBlock.SlotPath p s) : good (ECArithBlock.slotBlock E seed b T z) (cap p) := by
  apply join_ok _ _ _ (mono (add_ok _ _ _ _ _) (small p 5 (by decide)))
  change good (ECArithBlock.baseBlock E seed b) (cap p)
  refine join_ok _ _ (anchors_ok 1 _ (small p 1 (by decide))) (join_ok _ _ ?_ (join_ok _ _ (rBound p _ 2 _ _ (by decide)) (join_ok _ _ ?_ (eqBound _ _ _ _))))
  · exact join_ok _ _ (join_ok _ _ (ck _ _) (ck _ _)) (many_ok _ _ fun _ => join_ok _ _ (ck _ _) (ck _ _))
  · unfold ECArithBlock.products; apply many_ok; intro j; split <;> exact hashBound _ _

theorem solution {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m) (T : ℕ) (P : E.toAffine.Point) (pre : List Bool) :
    ∀ j, S8J.degreeOf (ECPhysicalNet.body (k:=k) E seed T P pre).core.A.gate j ≤ max 12 ⌈136*((bitLen p:ℝ)+2)^((3:ℝ)/4)⌉₊ := by
  change good (ECPhysicalNet.body (k:=k) E seed T P pre) (cap p)
  apply join_ok
  · exact join_ok _ _ (manyBound _ fun _ => slotBound _ _ _ _ _) (join_ok _ _ (chainBound _ _ _ _) (chainBound _ _ _ _))
  · apply join_ok _ _ (bankBound _ _ _); unfold ECArithNet.prefixBlock; split <;> exact rBound _ _ _ _ _ (by decide)
