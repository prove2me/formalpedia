-- Prove2me | solution 1 for DetDLP.m3b_ec_top_layout_models
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T05:17:08.000017+00:00
-- url     : https://prove2.me/submissions/8cadbe2b-d69b-4111-b853-2fcc92f0fa77

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECFits
import Theorems.Thm_DetDLP_m3b_ec_physical_offsets

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP DetDLP.M3B S8H0 GateSemantics ECPhysicalNet S8J S8H S8H.PointAddresses

attribute [-simp] Fin.natAdd_eq_addNat

private theorem row_col_vals {n k : ℕ} (u : Fin (n * k)) :
    (ECLayout.row u).val = u.val / k ∧ (ECLayout.column u).val = u.val % k := by
  have hk : 0 < k := by
    by_contra! h
    obtain rfl : k = 0 := by omega
    exact Fin.elim0 (by simpa using u : Fin 0)
  let r := ECLayout.row u
  let c := ECLayout.column u
  have heq : finProdFinEquiv (r, c) = u := finProdFinEquiv.apply_symm_apply u
  have hval : c.val + k * r.val = u.val := congrArg Fin.val heq
  have hc : c.val < k := c.isLt
  constructor
  · rw [← hval, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hc, zero_add]
  · rw [← hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

theorem solution
    {p m k T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (seed : ECSeed p m) (P : E.toAffine.Point) (pre : List Bool)
    (a : ECPolyDefs.N) (hfits : ECFits.FitsCore a (ECPhysicalNet.body (k := k) E seed T P pre)) :
    let L := ECPhysicalNet.layout (k := k) E seed T P pre
    let d := GateSemantics.d p
    let e := GateSemantics.e p
    let n := ECPolyDefs.ne a
    let g := ECPolyDefs.ng a
    let lookup := g + n
    let src := fun i => if i < n then ECPolyDefs.gate a i else if i < 3 * n then g + (i - n) % n else lookup + (i - 3 * n) / k
    let dst := fun i => if i < n then i else if i < 2 * n then i - n else if i < 3 * n then ECPolyDefs.succWire a (i - 2 * n)
      else ECPolyDefs.busOff d e (max d k) ((i - 3 * n) / k) 1 + (i - 3 * n) % k
    L.ng = lookup + 4 * m ∧ L.nb = n ∧ L.ne = 3 * n + 4 * m * k ∧
    (∀ i : Fin L.ne, (L.gate i).val = src i.val ∧ (L.bit i).val = dst i.val) := by
  rcases a with ⟨ga, na, gatea, siga, chka⟩
  have hg : ga = (AnchoredLayout.block (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core ((ShapeOf p m k).size + 1)).A.ng := hfits.g
  have hn : na = (AnchoredLayout.block (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core ((ShapeOf p m k).size + 1)).A.ne := hfits.e
  subst hg hn
  have hgate (j) : gatea j.val = ((AnchoredLayout.block (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core ((ShapeOf p m k).size + 1)).A.gate j).val := hfits.own j
  have hname (j) : siga j.val = ((AnchoredLayout.wiring (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).name).signal j).val := hfits.name j
  have hnext (j : Fin (AnchoredLayout.block (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core ((ShapeOf p m k).size + 1)).A.ne) :
      ECPolyDefs.succWire ((AnchoredLayout.block (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core ((ShapeOf p m k).size + 1)).A.ng,
        (AnchoredLayout.block (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core ((ShapeOf p m k).size + 1)).A.ne, gatea, siga, chka) j.val =
      ((AnchoredLayout.wiring (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).name).next j).val := by
    have h1 := CycleCode.next_eq siga j
    have hfib : NamedWires.fiber (fun z => siga z.val) (siga j.val) =
        NamedWires.fiber (AnchoredLayout.wiring (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).name).signal
          ((AnchoredLayout.wiring (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).name).signal j) := by
      unfold NamedWires.fiber
      apply List.filter_congr; intro z _
      simp [hname z, hname j, Fin.ext_iff]
    refine Eq.trans h1 ?_
    change ((NamedWires.fiber (fun z => siga z.val) (siga j.val)).formPerm j).val =
      ((NamedWires.fiber _ _).formPerm j).val
    rw [hfib]; rfl
  dsimp only [ECPolyDefs.ng, ECPolyDefs.ne, ECPolyDefs.gate, ECPhysicalNet.layout, ECArithNet.withLookups, ECLayout.layout, CircuitRealizes.circuit, CopyCycle.layout]
  refine ⟨rfl, rfl, by omega, ?_⟩
  intro i
  induction i using Fin.addCases with
  | left c =>
    induction c using Fin.addCases with
    | left u =>
      simp only [splitMap, Fin.addCases_left, Fin.val_castAdd, Function.comp_apply, id_eq]
      rw [if_pos u.isLt, if_pos u.isLt, hgate u]
      exact ⟨rfl, rfl⟩
    | right c2 =>
      let N0 := (AnchoredLayout.block (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core ((ShapeOf p m k).size + 1)).A.ne
      induction c2 using Fin.addCases with
      | left u =>
        simp only [splitMap, Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd, Function.comp_apply, id_eq]
        have h1 : ¬ (N0 + u.val < N0) := by omega
        have h2 : N0 + u.val < 3 * N0 := by have := u.isLt; dsimp [N0] at *; omega
        have h2' : N0 + u.val < 2 * N0 := by have := u.isLt; dsimp [N0] at *; omega
        change (_ = if N0 + u.val < N0 then _ else if N0 + u.val < 3 * N0 then _ + (N0 + u.val - N0) % N0 else _) ∧
          (_ = if N0 + u.val < N0 then _ else if N0 + u.val < 2 * N0 then N0 + u.val - N0 else _)
        rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2', Nat.add_sub_cancel_left, Nat.mod_eq_of_lt u.isLt]
        exact ⟨rfl, rfl⟩
      | right u =>
        simp only [splitMap, Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd, Function.comp_apply]
        have h1 : ¬ (N0 + (N0 + u.val) < N0) := by omega
        have h2 : N0 + (N0 + u.val) < 3 * N0 := by have := u.isLt; dsimp [N0] at *; omega
        have h2' : ¬ (N0 + (N0 + u.val) < 2 * N0) := by omega
        have hmod : (N0 + (N0 + u.val) - N0) % N0 = u.val := by
          rw [Nat.add_sub_cancel_left, Nat.add_mod_left, Nat.mod_eq_of_lt u.isLt]
        have hsub : N0 + (N0 + u.val) - 2 * N0 = u.val := by omega
        change (_ = if N0 + (N0 + u.val) < N0 then _ else if N0 + (N0 + u.val) < 3 * N0 then _ + (N0 + (N0 + u.val) - N0) % N0 else _) ∧
          (_ = if N0 + (N0 + u.val) < N0 then _ else if N0 + (N0 + u.val) < 2 * N0 then _ else if N0 + (N0 + u.val) < 3 * N0 then ECPolyDefs.succWire _ (N0 + (N0 + u.val) - 2 * N0) else _)
        rw [if_neg h1, if_pos h2, if_neg h1, if_neg h2', if_pos h2, hmod, hsub, hnext u]
        exact ⟨rfl, rfl⟩
  | right u =>
    let N0 := (AnchoredLayout.block (ECArithNet.body inputs T (arithmetic (k := k) E seed T P) refs pre).core ((ShapeOf p m k).size + 1)).A.ne
    simp only [splitMap, Fin.addCases_right, Fin.val_natAdd, Function.comp_apply, AnchoredLayout.wiring]
    have h1 : ¬ (N0 + (N0 + N0) + u.val < N0) := by omega
    have h2 : ¬ (N0 + (N0 + N0) + u.val < 3 * N0) := by omega
    have h2' : ¬ (N0 + (N0 + N0) + u.val < 2 * N0) := by omega
    have hsub : N0 + (N0 + N0) + u.val - 3 * N0 = u.val := by omega
    obtain ⟨hr, hc⟩ := row_col_vals u
    have hoff := (m3b_ec_physical_offsets p m k).2 (ECLayout.row u) 1 (Fin.castLE (le_max_right _ _) (ECLayout.column u))
    change (_ = if N0 + (N0 + N0) + u.val < N0 then _ else if N0 + (N0 + N0) + u.val < 3 * N0 then _ else _ + (N0 + (N0 + N0) + u.val - 3 * N0) / k) ∧
      (_ = if N0 + (N0 + N0) + u.val < N0 then _ else if N0 + (N0 + N0) + u.val < 2 * N0 then _ else if N0 + (N0 + N0) + u.val < 3 * N0 then _ else ECPolyDefs.busOff (d p) (e p) (max (d p) k) ((N0 + (N0 + N0) + u.val - 3 * N0) / k) 1 + (N0 + (N0 + N0) + u.val - 3 * N0) % k)
    rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2', if_neg h2, hsub, hr]
    refine ⟨rfl, ?_⟩
    erw [Fin.addCases_right]
    change (busAddr (ECLayout.row u) 1 (Fin.castLE (le_max_right _ _) (ECLayout.column u))).index.val = _
    rw [hoff, hr]
    simp only [Fin.val_one, Fin.coe_castLE, hc, ECPolyDefs.busOff, ECPolyDefs.slotSize, ECPolyDefs.bankSize,
      ECPolyDefs.pt, ECPolyDefs.triple, ECPolyDefs.run, ECPolyDefs.aux, busWidth, ECAddrGadget.width]
