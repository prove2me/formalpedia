-- Prove2me | solution 1 for DetDLP.m3b_ec_layout_size
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:19:38.882783+00:00
-- url     : https://prove2.me/submissions/67c7b7b1-fa22-444e-8083-d7b7952c2461

import Definitions.Def_DetDLP_M3B_ECPhysicalNet

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP DetDLP.S8H0 DetDLP.M3B ECPhysicalNet ECChainBlocks RegisterMap GateSemantics

private theorem count {m b k e : ℕ} (hb : 1 ≤ b) (hm : 1 ≤ m) (hk : k ≤ b+1) (he : e ≤ 1100*(b+2)) :
    let d := b+1
    let w := max (b+1) k
    let pt := 1+2*(3*d+1)
    let run := (3*d+1)+((3*d+1)+(d+2*(2*d+e)))+1
    let aux := 2*d+3*(d+1)
    let slot := pt+7*(run+aux)+d+(d+1)+3*w
    let mp := pt+4*(run+aux)
    let ad := pt+2*(1+(3*d+1))+d+15*(run+aux)
    let names := 4*m*slot+2*((2*m+1)*mp+2*m*ad)+pt
    2*(3*(names+1+(4*m*(28*e+400*(d+2))+2*edgeBound d e (2*m)+(4*m*(7*w)+max 1 (4*m*(3*b)))))+4*m*k) ≤ 100000000*m*b := by
  dsimp only; rw [max_eq_left hk, max_eq_right (by nlinarith : 1 ≤ 4*m*(3*b))]
  unfold edgeBound
  have hme := Nat.mul_le_mul_left m he
  have hmk := Nat.mul_le_mul_left m hk
  have hmb := Nat.mul_le_mul_left m hb
  have hbm := Nat.mul_le_mul_right b hm
  nlinarith

theorem solution {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m) (T : ℕ) (P : E.toAffine.Point) (pre : List Bool)
    (hm : 1 ≤ m) (hb : 1 ≤ bitLen p) (hk : k ≤ bitLen p+1) :
    2*(ECPhysicalNet.layout (k:=k) E seed T P pre).ne ≤ 100000000*m*bitLen p := by
  have h := Nat.mul_le_mul_left 2 (layout_edges (k:=k) E seed T P pre)
  apply h.trans
  have he : e p ≤ 1100*(bitLen p+2) := (w4_M5GraphBounds.graph_edge_bound (hd p)).le
  apply le_trans _ (count hb hm hk he)
  simp only [ShapeOf,SlotCell,ECArithBlock.Sh,GateRoutes.S,Chain,Cells,PointCell,ECAddRows.addShape,ECMapRows.mapShape,
    ECMapRows.slot,GateRoutes.auxShape,triple,run,mul,bank,Shape.size,slotBudget,ECPhysicalNet.busWidth,ECAddrGadget.width,d,S8H.ECPointArithmetic.width]
  apply le_of_eq; ring
