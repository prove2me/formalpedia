-- Prove2me | solution 1 for DetDLP.w3_separator_newton_readout
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T21:25:51.987798+00:00
-- url     : https://prove2.me/submissions/3e6dc4ad-36ee-4df1-89f4-836107338959

import Definitions.Def_DetDLP_W3_Separator
import Theorems.Thm_DetDLP_lemma_4_2_newton_binomial_filter

set_option autoImplicit false
open DetDLP

private theorem w3_slotLabels (q : w3_Query) (X : q.FB.BlockTuple) : q.FB.tupleLabelSum q.M q.y X =
    ∑ i, ∑ k, ((q.y (q.FB.coordOf i (X i k))).val : ℤ) := by
  classical
  simp only [IndexedFactorBase.tupleLabelSum,IndexedFactorBase.tupleCnt,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; simp [ite_mul]

theorem solution (q : w3_Query) (hm : 2 ≤ q.m) (hM : 2 ≤ q.M)
    (G : BipartiteMultigraph) (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly (w3_precision q) (w3_len q))
    (ok : (Fin G.nE → Bool) → Prop) (e : {a // ok a} ≃ {t // w3_valid q t})
    (live : ∀ a : {a // ok a}, (∏ v, T v (fun j => a.val ((G.ports v).get j))) = w3_pairWeight q (e a).val)
    (dead : ∀ a : Fin G.nE → Bool, ¬ok a → (∏ v, T v (fun j => a ((G.ports v).get j))) = 0)
    (hbound : w3_mass q < (2 : ℤ)^w3_precision q) :
    ∀ c : Fin (w3_len q) → ℕ, BTNContract G T = truncPolyOfCoeffs (w3_precision q) (w3_len q) c →
      ((∑ j : Fin (w3_len q), (newtonCoeff (2*q.m) q.M j.val : ZMod (2^w3_precision q)) * (c j : ZMod (2^w3_precision q))).val : ℤ) = w3_mass q := by
  classical
  let wt := fun a : Fin G.nE → Bool => ∏ v, T v (fun j => a ((G.ports v).get j))
  have hc : BTNContract G T = ∑ t : {t // w3_valid q t}, w3_pairWeight q t.val := by
    change (∑ x, wt x) = _
    rw [← Fintype.sum_subtype_add_sum_subtype ok wt]
    have good (x : {a // ok a}) : wt x.val = w3_pairWeight q (e x).val := live x
    have bad (x : {a // ¬ok a}) : wt x.val = 0 := dead x x.property
    simp only [good,bad,Finset.sum_const_zero,add_zero]
    exact e.sum_comp (fun t => w3_pairWeight q t.val)
  let E : (Fin q.m × (Fin 2 × Fin 2)) ≃ Fin (2*(2*q.m)) :=
    (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans (finProdFinEquiv.trans (finCongr (by omega)))
  let lbl := fun (X : q.FB.BlockTuple) i s => ((q.y (q.FB.coordOf i (X i s))).val : ℤ)
  let val := fun (t : {t // w3_valid q t}) (i : Fin (2*(2*q.m))) =>
    let v := E.symm i
    if v.2.2 = 0 then -lbl t.val.1 v.1 v.2.1 else lbl t.val.2 v.1 v.2.1
  have hv (t : {t // w3_valid q t}) (z : Fin q.m × (Fin 2 × Fin 2)) : val t (E z) =
      (if z.2.2 = 0 then -lbl t.val.1 z.1 z.2.1 else lbl t.val.2 z.1 z.2.1) := by
    dsimp only [val]; rw [E.symm_apply_apply]
  have hne : (1 : Fin 2) ≠ 0 := by decide
  have hdelta (t : {t // w3_valid q t}) : (∑ i, (1 : ℤ)*val t i) = w3_delta q.FB q.M q.y t.val.1 t.val.2 := by
    rw [← E.sum_comp (fun i => (1:ℤ)*val t i)]
    simp only [hv,Fintype.sum_prod_type,Fin.sum_univ_two,one_mul,if_true,hne,if_false,
      w3_delta,w3_slotLabels,Finset.sum_add_distrib,Finset.sum_neg_distrib]
    dsimp [lbl]; abel
  have hprod (t : {t // w3_valid q t}) : (∏ i, w3_binWord q (1*val t i)) = w3_pairWeight q t.val := by
    rw [← E.prod_comp (fun i => w3_binWord q (1*val t i))]
    simp only [hv,Fintype.prod_prod_type,Fin.prod_univ_two,one_mul,if_true,hne,if_false,w3_pairWeight,lbl]
  have hmass : (∑ t : {t // w3_valid q t}, (filterPoly (2*q.m) q.M).eval (∑ i, (1:ℤ)*val t i)) = w3_mass q := by
    simp only [hdelta]
    let summand := fun t : q.FB.BlockTuple × q.FB.BlockTuple => if w3_valid q t then
      (filterPoly (2*q.m) q.M).eval (w3_delta q.FB q.M q.y t.1 t.2) else 0
    have yes (t : {t // w3_valid q t}) : summand t = _ := if_pos t.property
    have no (t : {t // ¬w3_valid q t}) : summand t = 0 := if_neg t.property
    change _ = ∑ t, summand t
    simpa only [yes,no,Finset.sum_const_zero,add_zero] using
      Fintype.sum_subtype_add_sum_subtype (w3_valid q) summand
  obtain ⟨_,_,_,hnewton⟩ := lemma_4_2_newton_binomial_filter (2*q.m) q.M (by omega) hM
  intro c hrepr
  have h1 : 1 ≤ w3_precision q := by unfold w3_precision; omega
  have h := hnewton (w3_precision q) val (fun _ => (1 : ℤ)) h1 (fun _ => Or.inl rfl)
    (hmass.trans_lt hbound) (fun i => (c i : ZMod (2^w3_precision q)))
  apply Eq.trans (h ?_) hmass
  change truncPolyOfCoeffs _ _ c = ∑ t, ∏ i, w3_binWord q (1*val t i)
  rw [←hrepr,hc]; simp only [hprod]
