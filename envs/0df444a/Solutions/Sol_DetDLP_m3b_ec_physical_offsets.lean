-- Prove2me | solution 1 for DetDLP.m3b_ec_physical_offsets
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T23:59:53.207489+00:00
-- url     : https://prove2.me/submissions/d97d0f8b-a8fb-4737-a5ac-f33fb922e262

import Definitions.Def_DetDLP_M3B_ECPhysicalNet

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP DetDLP.M3B S8H0 RegisterMap GateSemantics ECPhysicalNet ECChainBlocks
private theorem pairVal {n l : ℕ} (i : Fin n) (j : Fin l) : (finProdFinEquiv (i,j)).val = i.val*l+j.val := by change j.val+l*i.val=_; ring

theorem solution (p m k : ℕ) :
    let d := GateSemantics.d p; let e := GateSemantics.e p; let w := busWidth p k
    let tr := 3*d+1; let pt := 1+2*tr; let run := 2*tr+d+2*(2*d+e)+1; let aux := 2*d+3*(d+1)
    let gs := run+aux; let bank := pt+7*run+7*aux; let slot := bank+d+(d+1)+3*w
    (ShapeOf p m k).size = 4*m*slot+2*((2*m+1)*(pt+4*gs)+2*m*(pt+2*(1+tr)+d+15*gs))+pt ∧
     ∀ (i : Fin (4*m)) (l : Fin 3) (j : Fin (busWidth p k)), (busAddr i l j).index.val = i.val*slot+bank+d+(d+1)+l.val*w+j.val := by
  dsimp only; constructor
  · simp only [ECArithBlock.Sh,GateRoutes.S,ECAddRows.addShape,ECMapRows.mapShape,ECMapRows.slot,GateRoutes.auxShape,
      RegisterMap.triple,RegisterMap.run,RegisterMap.mul,RegisterMap.bank,Shape.size]; ring
  · intro i l j
    change ((finProdFinEquiv (i, Fin.natAdd (ECArithBlock.Sh p).size (Fin.natAdd (d p) (Fin.natAdd (d p+1) (finProdFinEquiv (l,j))))))).val = _
    rw [pairVal,Fin.val_natAdd,Fin.val_natAdd,Fin.val_natAdd,pairVal]
    simp only [ECArithBlock.Sh,GateRoutes.S,RegisterMap.bank,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,Shape.size]; ring
