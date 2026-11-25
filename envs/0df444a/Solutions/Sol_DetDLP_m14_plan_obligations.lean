-- Prove2me | solution 1 for DetDLP.m14_plan_obligations
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T07:46:31.58572+00:00
-- url     : https://prove2.me/submissions/ed3e474b-c95c-4d03-bd65-fb5e8c9889a8

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_m14_sync
import Theorems.Thm_DetDLP_m14_total
import Theorems.Thm_DetDLP_m14_base_fuel
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds
import Theorems.Thm_DetDLP_d4_adaptive_padded_rank_sum

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace DetDLP.M14PlanInternal

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable section

theorem soloPoly_monic {S : ℕ} (hL : 1 ≤ D3Stopped.level S) : (soloPoly S).Monic :=
  (DetDLP.m14_base_fuel.1 hL).1

theorem soloPoly_natDegree {S : ℕ} (hL : 1 ≤ D3Stopped.level S) :
    (soloPoly S).natDegree = 4 * Nat.clog 2 S :=
  (DetDLP.m14_base_fuel.1 hL).2.1

abbrev unrollCertFuel_all_valid {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ) :=
  (DetDLP.m14_sync x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc).2.1

abbrev unrollCertFuel_work {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc guard : ℕ) :=
  (DetDLP.m14_sync x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc).2.2.1 guard

abbrev root_unrollCert_total_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ)
    (rootNode : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
    (hd0 : rootNode.d = 0)
    (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
      (Nat.clog 32 (4 * x.m)) rootNode)
    (η : Fin (4 * x.m * x.k) → Bool) :=
  DetDLP.m14_total x hf hdeg M_node E_pkt o_node o_pkt K_loc H_loc c_loc rootNode hd0 rootUnroll η







theorem reattach_old_eq {C c : ℕ} (x : Input C c) (n : ℕ)
    (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n)
    (old : Fin x.spec.lookupVerts.card ≃ ↥x.spec.lookupVerts)
    (lp : (v : Fin x.spec.lookupVerts.card) →
      Fin (x.G.deg (old v).val) ≃ Fin ((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).deg (v.castAdd n)))
    (hlp : ∀ v i,
      D4CoreCut.origB x.G x.spec.lookupVerts
        (((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).ports (v.castAdd n)).get (lp v i)) =
      (x.G.ports (old v).val).get i)
    (v : Fin x.spec.lookupVerts.card) :
    (old v).val = (D4CoreCut.lookupVerts x.G x.spec.lookupVerts)[v.val]'(by
      rw [D4CoreCut.lookup_length]; exact v.isLt) := by
  let L := x.spec.lookupVerts
  let H := D4CoreCut.reattach x.G L n leafFn
  have hdeg_pos : 0 < x.G.deg (old v).val := by
    rw [x.spec.lookup_deg (old v).val (old v).property]; exact x.hk
  let i₀ : Fin (x.G.deg (old v).val) := ⟨0, hdeg_pos⟩
  let e_b : Fin H.nE := (H.ports (v.castAdd n)).get (lp v i₀)
  have hincH := D4CoreCut.port_inc H (v.castAdd n) (lp v i₀)
  have hleft : D4CoreCut.lookupIdx x.G L e_b = v := by
    rcases hincH with h1 | h2
    · have hv : (D4CoreCut.lookupIdx x.G L e_b).val = v.val := by
        simpa [H, D4CoreCut.reattach, e_b] using congrArg Fin.val h1
      exact Fin.ext hv
    · have hlt : (v.castAdd n).val < L.card := v.isLt
      have hge : L.card ≤ ((H.endpoints e_b).2).val := by simp [H, D4CoreCut.reattach]
      rw [h2] at hge
      exact False.elim (Nat.not_lt_of_ge hge hlt)
  have he_eq : D4CoreCut.origB x.G L e_b = (x.G.ports (old v).val).get i₀ := hlp v i₀
  have hincG := D4CoreCut.port_inc x.G (old v).val i₀
  rw [← he_eq] at hincG
  have hind := D4CoreCut.independent_of_spec x.G x.spec
  have hsel : (if (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 ∈ L then
      (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 else
      (x.G.endpoints (D4CoreCut.origB x.G L e_b)).2) = (old v).val := by
    rcases hincG with h1 | h2
    · rw [h1, if_pos (old v).property]
    · rw [h2]
      by_cases h1in : (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 ∈ L
      · exact False.elim (hind (D4CoreCut.origB x.G L e_b) h1in (h2 ▸ (old v).property))
      · rw [if_neg h1in]
  have hidx_v : (D4CoreCut.lookupVerts x.G L).idxOf (old v).val = v.val := by
    have hv' := congrArg Fin.val hleft
    unfold D4CoreCut.lookupIdx at hv'
    change List.idxOf (if (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 ∈ L then
      (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 else
      (x.G.endpoints (D4CoreCut.origB x.G L e_b)).2) (D4CoreCut.lookupVerts x.G L) = v.val at hv'
    rwa [hsel] at hv'
  have hv_lt : v.val < (D4CoreCut.lookupVerts x.G L).length := by
    rw [D4CoreCut.lookup_length]; exact v.isLt
  have hget := List.getElem_idxOf (h := by rwa [hidx_v])
  conv_lhs => rw [← hget]
  congr 1

private theorem map_filter_comp {α β : Type} (g : α → β) (q : β → Bool) (xs : List α) :
    (xs.filter (q ∘ g)).map g = (xs.map g).filter q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : q (g x)
    · simp [h, ih]
    · simp [h, ih]

theorem lookupVerts_map_val {G : Graph} (L : Finset (Fin G.nV)) :
    (D4CoreCut.lookupVerts G L).map Fin.val =
      (List.range G.nV).filter (fun v =>
        (List.ofFn (fun w : Fin G.nV => decide (w ∈ L))).getD v false) := by
  let q : ℕ → Bool := fun v => (List.ofFn (fun w : Fin G.nV => decide (w ∈ L))).getD v false
  have hfilt : (List.finRange G.nV).filter (fun w => decide (w ∈ L)) =
      (List.finRange G.nV).filter (q ∘ Fin.val) := by
    apply List.filter_congr
    intro w _
    dsimp only [Function.comp_apply, q]
    have hw : w.val < (List.ofFn (fun u : Fin G.nV => decide (u ∈ L))).length := by simp [w.isLt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw, List.getElem_ofFn, Option.getD_some]
  have hmap : (List.finRange G.nV).map Fin.val = List.range G.nV := by
    apply List.ext_getElem <;> simp
  unfold D4CoreCut.lookupVerts
  rw [hfilt, map_filter_comp, hmap]

private theorem readCoeff_loc {R : Type*} [CommRing R] {g : R[X]} (hg : g.Monic)
    {n : ℕ} (hn : Nontrivial R → g.natDegree = n) (b : Fin n → R) (i : Fin n) :
    (AdjoinRoot.modByMonicHom hg (AdjoinRoot.mk _ (∑ j : Fin n, monomial j.val (b j)))).coeff i = b i := by
  nontriviality R
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hg).mpr]
  · simp only [finsetSum_coeff, coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [degree_eq_natDegree hg.ne_zero, hn inferInstance]
    simp_rw [← C_mul_X_pow_eq_monomial]
    exact degree_sum_fin_lt _

private theorem readBase_loc {R : Type*} [CommRing R] {g : R[X]} (hg : g.Monic)
    {n : ℕ} (hn : Nontrivial R → g.natDegree = n) (b : R) (i : Fin n) :
    (AdjoinRoot.modByMonicHom hg (AdjoinRoot.of _ b)).coeff i = if i.val = 0 then b else 0 := by
  nontriviality R
  rw [← AdjoinRoot.mk_C, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hg).mpr, coeff_C]
  apply degree_C_le.trans_lt
  rw [degree_eq_natDegree hg.ne_zero, hn inferInstance]
  exact_mod_cast Nat.zero_lt_of_lt i.isLt


theorem polyToB_eq_trunc (f : ℤ[X]) (l q : ℕ) (Q : ℤ[X]) :
    polyToB f l q Q = AdjoinRoot.mk _ (∑ j : Fin l, monomial j.val
      (AdjoinRoot.of _ ((Q.coeff j.val : ℤ) : ZMod (2 ^ q)))) := by
  have hzero : ∀ k : ℕ, l ≤ k → polyToB f l q (C (Q.coeff k) * X ^ k) = 0 := by
    intro k hk
    have hx : (X : ℤ[X]) ^ k = X ^ l * X ^ (k - l) := by rw [← pow_add]; congr 1; omega
    rw [hx, ← mul_assoc, map_mul, map_mul]
    have hxl : polyToB f l q (X ^ l) = 0 := by
      simp [polyToB, AdjoinRoot.mk_self]
    rw [hxl, mul_zero, zero_mul]
  have hlt_eq : ∀ k : ℕ, k < l → polyToB f l q (C (Q.coeff k) * X ^ k) =
      AdjoinRoot.mk _ (monomial k (AdjoinRoot.of _ ((Q.coeff k : ℤ) : ZMod (2 ^ q)))) := by
    intro k _
    rw [C_mul_X_pow_eq_monomial]
    simp only [polyToB, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_monomial,
      Int.coe_castRingHom]
  conv_lhs => arg 2; rw [Q.as_sum_support_C_mul_X_pow]
  rw [map_sum]
  have hsum1 : (∑ k ∈ Q.support, polyToB f l q (C (Q.coeff k) * X ^ k)) =
      ∑ k ∈ Q.support.filter (· < l),
        AdjoinRoot.mk ((X : (U f q)[X]) ^ l)
          (monomial k (AdjoinRoot.of _ ((Q.coeff k : ℤ) : ZMod (2 ^ q)))) := by
    rw [← Finset.sum_filter_add_sum_filter_not Q.support (· < l)]
    have h2 : ∑ k ∈ Q.support.filter (fun x => ¬x < l), polyToB f l q (C (Q.coeff k) * X ^ k) = 0 :=
      Finset.sum_eq_zero fun k hk => hzero k (Nat.le_of_not_lt (Finset.mem_filter.mp hk).2)
    rw [h2, add_zero]
    exact Finset.sum_congr rfl fun k hk => hlt_eq k (Finset.mem_filter.mp hk).2
  rw [hsum1, ← map_sum, Fin.sum_univ_eq_sum_range (fun k => monomial k
    (AdjoinRoot.of _ ((Q.coeff k : ℤ) : ZMod (2 ^ q))))]
  congr 1
  apply Finset.sum_subset
  · intro k hk; exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
  · intro k hk hnot
    have hk_supp : k ∉ Q.support := fun h => hnot (Finset.mem_filter.mpr ⟨h, Finset.mem_range.mp hk⟩)
    rw [Polynomial.notMem_support_iff.mp hk_supp]
    simp

theorem liftBase_eq_polyToB (f : ℤ[X]) (l q : ℕ) (a : Fin l → ℕ) :
    liftBase f l q a = polyToB f l q (∑ j : Fin l, monomial j.val (a j : ℤ)) := by
  unfold liftBase polyToB
  simp only [map_sum, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, RingHom.comp_apply,
    Polynomial.coe_mapRingHom, Polynomial.map_X, map_natCast]

theorem BTNContract_polyToB (G : Graph) (f : ℤ[X]) (l q : ℕ) (T : Tensor G ℤ[X]) :
    BTNContract G (fun v α => polyToB f l q (T v α)) = polyToB f l q (BTNContract G T) := by
  unfold BTNContract
  simp only [map_sum, map_prod]

theorem word_polyToB_zero {f : ℤ[X]} (hf : f.Monic) (l q : ℕ) (Q : ℤ[X])
    (j : Fin l) (zero : Fin f.natDegree) (hz : zero.val = 0) :
    word f l q hf (polyToB f l q Q) j zero = ((Q.coeff j.val : ℤ) : ZMod (2 ^ q)).val := by
  rw [polyToB_eq_trunc]
  unfold word
  rw [readCoeff_loc (monic_X_pow l) (fun _ => natDegree_X_pow l),
      readBase_loc (hf.map _) (fun _ => hf.natDegree_map _), if_pos hz]

theorem lift_polyToB {f : ℤ[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) (l p q : ℕ) (Q : ℤ[X]) :
    lift hf q (polyToB f l p Q) =
      polyToB f l q (∑ j : Fin l, monomial j.val ((((Q.coeff j.val : ℤ) : ZMod (2 ^ p)).val : ℕ) : ℤ)) := by
  have hw : ∀ j i, word f l p hf (polyToB f l p Q) j i =
      if i.val = 0 then ((Q.coeff j.val : ℤ) : ZMod (2 ^ p)).val else 0 := by
    intro j i
    rw [polyToB_eq_trunc]
    unfold word
    rw [readCoeff_loc (monic_X_pow l) (fun _ => natDegree_X_pow l),
        readBase_loc (hf.map _) (fun _ => hf.natDegree_map _)]
    split_ifs <;> simp
  unfold lift
  simp_rw [hw]
  let i0 : Fin f.natDegree := ⟨0, hdeg⟩
  have hsum_j : ∀ j : Fin l,
      AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2 ^ q))))
        (∑ i : Fin f.natDegree, monomial i.val
          (((if i.val = 0 then ((Q.coeff j.val : ℤ) : ZMod (2 ^ p)).val else 0 : ℕ) : ZMod (2 ^ q)))) =
      AdjoinRoot.of _ ((((Q.coeff j.val : ℤ) : ZMod (2 ^ p)).val : ℕ) : ZMod (2 ^ q)) := by
    intro j
    rw [Finset.sum_eq_single i0]
    · simp [i0]
    · intro i _ hne; have : i.val ≠ 0 := fun h => hne (Fin.ext h); simp [this]
    · intro hm; exact False.elim (hm (Finset.mem_univ i0))
  simp_rw [hsum_j]
  rw [polyToB_eq_trunc]
  congr 1; apply Finset.sum_congr rfl; intro j _
  have hcj : (∑ r : Fin l, monomial r.val
      ((((Q.coeff r.val : ℤ) : ZMod (2 ^ p)).val : ℕ) : ℤ)).coeff j.val =
      ((((Q.coeff j.val : ℤ) : ZMod (2 ^ p)).val : ℕ) : ℤ) := by
    simp [finsetSum_coeff, coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hcj]
  simp

theorem ZMod_mul_pow_div_pow (g p : ℕ) (c : ZMod (2 ^ (g + p))) :
    (((2 ^ g : ℕ) * c : ZMod (2 ^ (g + p))).val) / 2 ^ g = c.val % 2 ^ p := by
  have hg : 0 < 2 ^ g := by positivity
  have h1 : (((2 ^ g : ℕ) * c : ZMod (2 ^ (g + p))).val) = (2 ^ g * c.val) % 2 ^ (g + p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [← Nat.cast_mul, ZMod.val_natCast]
  have hm : (2 ^ g * c.val) % (2 ^ g * 2 ^ p) = 2 ^ g * (c.val % 2 ^ p) :=
    Nat.mul_mod_mul_left (2 ^ g) c.val (2 ^ p)
  rw [← pow_add] at hm
  rw [h1, hm, Nat.mul_div_cancel_left _ hg]



theorem castU_of (f : ℤ[X]) (g p : ℕ) (r : ZMod (2 ^ (g + p))) :
    castU f g p (AdjoinRoot.of _ r) =
      AdjoinRoot.of _ (ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_left p g)) (ZMod (2 ^ p)) r) :=
  AdjoinRoot.lift_of _

theorem castB_of (f : ℤ[X]) (l g p : ℕ) (u : U f (g + p)) :
    castB f l g p (AdjoinRoot.of _ u) = AdjoinRoot.of _ (castU f g p u) :=
  AdjoinRoot.lift_of _

theorem castB_mk (f : ℤ[X]) (l g p : ℕ) (Q : (U f (g + p))[X]) :
    castB f l g p (AdjoinRoot.mk _ Q) = AdjoinRoot.mk _ (Q.map (castU f g p)) := by
  have hcomp : (castB f l g p).comp (AdjoinRoot.mk ((X : (U f (g + p))[X]) ^ l)) =
      (AdjoinRoot.mk ((X : (U f p)[X]) ^ l)).comp (Polynomial.mapRingHom (castU f g p)) := by
    apply Polynomial.ringHom_ext
    · intro u
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        AdjoinRoot.mk_C, castB_of]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      exact AdjoinRoot.lift_root _
  exact congrArg (fun h : (U f (g + p))[X] →+* B f l p => h Q) hcomp

theorem castU_mk (f : ℤ[X]) (g p : ℕ) (Q : (ZMod (2 ^ (g + p)))[X]) :
    castU f g p (AdjoinRoot.mk _ Q) =
      AdjoinRoot.mk _ (Q.map (ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_left p g)) (ZMod (2 ^ p)))) := by
  have hcomp : (castU f g p).comp (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2 ^ (g + p)))))) =
      (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2 ^ p))))).comp
        (Polynomial.mapRingHom (ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_left p g)) (ZMod (2 ^ p)))) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        AdjoinRoot.mk_C, castU_of]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      exact AdjoinRoot.lift_root _
  exact congrArg (fun h : (ZMod (2 ^ (g + p)))[X] →+* U f p => h Q) hcomp

theorem castB_polyToB (f : ℤ[X]) (l g p : ℕ) (Q : ℤ[X]) :
    castB f l g p (polyToB f l (g + p) Q) = polyToB f l p Q := by
  have hcomp : (castB f l g p).comp (polyToB f l (g + p)) = polyToB f l p := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [polyToB, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        AdjoinRoot.mk_C, castB_of, castU_of]
      have hhom : ((ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_left p g)) (ZMod (2 ^ p))).comp
          (Int.castRingHom (ZMod (2 ^ (g + p))))) = Int.castRingHom (ZMod (2 ^ p)) :=
        RingHom.ext_int _ _
      exact congrArg (fun φ : ℤ →+* ZMod (2 ^ p) => AdjoinRoot.of _ (AdjoinRoot.of _ (φ r))) hhom
    · simp only [polyToB, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      exact AdjoinRoot.lift_root _
  exact congrArg (fun h : ℤ[X] →+* B f l p => h Q) hcomp

theorem castB_liftBase (f : ℤ[X]) (l g p : ℕ) (a : Fin l → ℕ) :
    castB f l g p (liftBase f l (g + p) a) = liftBase f l p a := by
  rw [liftBase_eq_polyToB, castB_polyToB, ← liftBase_eq_polyToB]

theorem castB_lift {f : ℤ[X]} (hf : f.Monic) (l g p : ℕ) (z : B f l p) :
    castB f l g p (lift hf (g + p) z) = z := by
  unfold lift
  rw [castB_mk, Polynomial.map_sum]
  have hterm : ∀ j : Fin l, (monomial j.val
      (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2 ^ (g + p)))))
        (∑ i : Fin f.natDegree, monomial i.val ((word f l p hf z j i : ℕ) : ZMod (2 ^ (g + p)))))).map
      (castU f g p) =
      monomial j.val
        (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2 ^ p))))
          (∑ i : Fin f.natDegree, monomial i.val ((word f l p hf z j i : ℕ) : ZMod (2 ^ p)))) := by
    intro j
    rw [Polynomial.map_monomial, castU_mk, Polynomial.map_sum]
    congr 2; apply Finset.sum_congr rfl; intro i _
    rw [Polynomial.map_monomial, map_natCast]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  exact self_lift hf z

theorem word_two_pow_mul_div {f : ℤ[X]} (hf : f.Monic) {l g p : ℕ}
    (y : B f l (g + p)) (j : Fin l) (zero : Fin f.natDegree) :
    word f l (g + p) hf ((2 : B f l (g + p)) ^ g * y) j zero / 2 ^ g =
      word f l p hf (castB f l g p y) j zero := by
  let a : Fin l → Fin f.natDegree → ℕ := fun j' i' => word f l (g + p) hf y j' i'
  have hy : y = AdjoinRoot.mk ((X : (U f (g + p))[X]) ^ l) (∑ j' : Fin l, monomial j'.val
      (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2 ^ (g + p)))))
        (∑ i' : Fin f.natDegree, monomial i'.val ((a j' i' : ℕ) : ZMod (2 ^ (g + p)))))) :=
    (self_lift hf y).symm
  have h2mul : (2 : B f l (g + p)) ^ g * y =
      AdjoinRoot.mk ((X : (U f (g + p))[X]) ^ l) (∑ j' : Fin l, monomial j'.val
        (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2 ^ (g + p)))))
          (∑ i' : Fin f.natDegree, monomial i'.val
            (((2 ^ g : ℕ) : ZMod (2 ^ (g + p))) * ((a j' i' : ℕ) : ZMod (2 ^ (g + p))))))) := by
    conv_lhs => rw [hy]
    have h2nat : ((2 : B f l (g + p)) ^ g) = ((2 ^ g : ℕ) : B f l (g + p)) := by norm_cast
    rw [h2nat, ← map_natCast (AdjoinRoot.mk ((X : (U f (g + p))[X]) ^ l)), ← map_mul, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro j' _
    rw [← map_natCast (C : U f (g + p) →+* (U f (g + p))[X]), C_mul_monomial]
    congr 1
    rw [← map_natCast (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2 ^ (g + p)))))),
        ← map_mul, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro i' _
    rw [← map_natCast (C : ZMod (2 ^ (g + p)) →+* (ZMod (2 ^ (g + p)))[X]), C_mul_monomial]
  have hLHS : word f l (g + p) hf ((2 : B f l (g + p)) ^ g * y) j zero =
      (((2 ^ g : ℕ) * ((a j zero : ℕ) : ZMod (2 ^ (g + p))) : ZMod (2 ^ (g + p))).val) := by
    rw [h2mul]
    unfold word
    rw [readCoeff_loc (monic_X_pow l) (fun _ => natDegree_X_pow l),
        readCoeff_loc (hf.map _) (fun _ => hf.natDegree_map _)]
  have hcast : castB f l g p y =
      AdjoinRoot.mk ((X : (U f p)[X]) ^ l) (∑ j' : Fin l, monomial j'.val
        (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2 ^ p))))
          (∑ i' : Fin f.natDegree, monomial i'.val ((a j' i' : ℕ) : ZMod (2 ^ p))))) := by
    conv_lhs => rw [hy]
    rw [castB_mk, Polynomial.map_sum]
    congr 1; apply Finset.sum_congr rfl; intro j' _
    rw [Polynomial.map_monomial, castU_mk, Polynomial.map_sum]
    congr 2; apply Finset.sum_congr rfl; intro i' _
    rw [Polynomial.map_monomial, map_natCast]
  have hRHS : word f l p hf (castB f l g p y) j zero = (a j zero) % 2 ^ p := by
    rw [hcast]
    unfold word
    rw [readCoeff_loc (monic_X_pow l) (fun _ => natDegree_X_pow l),
        readCoeff_loc (hf.map _) (fun _ => hf.natDegree_map _), ZMod.val_natCast]
  have ha_lt : a j zero < 2 ^ (g + p) := ZMod.val_lt _
  rw [hLHS, hRHS]
  have hz : (((2 ^ g : ℕ) * ((a j zero : ℕ) : ZMod (2 ^ (g + p))) : ZMod (2 ^ (g + p))).val) / 2 ^ g =
      (((a j zero : ℕ) : ZMod (2 ^ (g + p))).val) % 2 ^ p :=
    ZMod_mul_pow_div_pow g p ((a j zero : ℕ) : ZMod (2 ^ (g + p)))
  rw [hz, ZMod.val_natCast_of_lt ha_lt]



theorem deg_le_nE (G : BipartiteMultigraph) (v : Fin G.nV) : G.deg v ≤ G.nE := by
  unfold BipartiteMultigraph.deg BipartiteMultigraph.ports
  exact (List.length_filter_le _ _).trans (by simp)

theorem sum_deg_le_two_nE (G : BipartiteMultigraph) : ∑ v : Fin G.nV, G.deg v ≤ 2 * G.nE := by
  have hdeg_eq : ∀ v : Fin G.nV,
      G.deg v = ∑ e : Fin G.nE, if (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v then 1 else 0 := by
    intro v
    unfold BipartiteMultigraph.deg BipartiteMultigraph.ports
    have hnd : ((List.finRange G.nE).filter fun e => decide ((G.endpoints e).1 = v ∨ (G.endpoints e).2 = v)).Nodup :=
      (List.nodup_finRange _).filter _
    rw [← List.toFinset_card_of_nodup hnd, Finset.card_eq_sum_ones, ← Finset.sum_filter]
    congr 1
    ext e
    simp
  simp_rw [hdeg_eq]
  rw [Finset.sum_comm]
  calc ∑ e : Fin G.nE, ∑ v : Fin G.nV, (if (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v then 1 else 0)
      ≤ ∑ _ : Fin G.nE, 2 := by
        apply Finset.sum_le_sum
        intro e _
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        have hsub : (Finset.univ.filter fun v : Fin G.nV => (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v) ⊆
            {(G.endpoints e).1, (G.endpoints e).2} := by
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton] at hv ⊢
          rcases hv with h1 | h2
          · exact Or.inl h1.symm
          · exact Or.inr h2.symm
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
    _ = 2 * G.nE := by simp [Finset.sum_const, mul_comm]

theorem stopped_pins_bound {C c : ℕ} (L₀_grd : ℕ)
    (hgrd : ∀ {c' : ℕ} (x' : Input C c'),
      let L := D3Stopped.level x'.S; let D := Nat.clog 32 (4 * x'.m); let β := 4 * x'.m * x'.k
      L₀_grd ≤ L →
      ∀ δ : ℕ, δ ≤ β / 32 ^ D + 32 * (L + 2) ∨ (∃ M ≤ D3Stopped.threshold x'.S, δ ≤ 2 * M) →
        δ * x'.m ≤ 1217 * (C + 1) ^ 3 * x'.b)
    (x : Input C c) (hL : L₀_grd ≤ D3Stopped.level x.S)
    {f : ℤ[X]} {PktOK : PktPred f x.l} (nd : SoloNode x f PktOK)
    (hstop : Nat.clog 32 (4 * x.m) ≤ nd.d ∨ nd.G.nE ≤ D3Stopped.threshold x.S) :
    nd.pins.length * x.m ≤ 1217 * (C + 1) ^ 3 * x.b := by
  apply hgrd x hL nd.pins.length
  rcases hstop with hd | hM
  · left
    have hpow : 32 ^ Nat.clog 32 (4 * x.m) ≤ 32 ^ nd.d := Nat.pow_le_pow_right (by decide) hd
    have hdiv : (4 * x.m * x.k) / 32 ^ nd.d ≤ (4 * x.m * x.k) / 32 ^ Nat.clog 32 (4 * x.m) :=
      Nat.div_le_div_left hpow (by positivity)
    exact nd.pins_len_le.trans (by omega)
  · right
    refine ⟨nd.G.nE, hM, ?_⟩
    have hpin1 : nd.pins.length = ∑ _k : Fin nd.pins.length, 1 := by simp
    have hpin_deg : nd.pins.length ≤ ∑ k : Fin nd.pins.length, nd.G.deg (nd.host k) := by
      conv_lhs => rw [hpin1]
      exact Finset.sum_le_sum fun k _ => nd.pinned_deg_pos k
    have hinj : Function.Injective nd.host := fun k₁ k₂ h => nd.host_inj k₁ k₂ h
    have himg : ∑ k : Fin nd.pins.length, nd.G.deg (nd.host k) =
        ∑ w ∈ Finset.univ.image nd.host, nd.G.deg w := by
      rw [Finset.sum_image]
      intro a _ b _ h; exact hinj h
    have hsub : ∑ w ∈ Finset.univ.image nd.host, nd.G.deg w ≤ ∑ w : Fin nd.G.nV, nd.G.deg w :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    exact hpin_deg.trans (himg ▸ hsub.trans (sum_deg_le_two_nE nd.G))


theorem emptyStoppedSpec_tableBits {C c : ℕ} (x : Input C c) (f : ℤ[X]) (deg : ℕ) :
    (emptyStoppedSpec x f deg).tableBits = pack [] := by
  unfold StoppedSpec.tableBits
  have hnil : List.ofFn (emptyStoppedSpec x f deg).vTable = [] := by
    apply List.ext_getElem <;> simp [emptyGraphConst]
  rw [hnil]
  rfl

theorem emptyStoppedSpec_desc {C c : ℕ} (x : Input C c) (f : ℤ[X]) (deg : ℕ) :
    stoppedDesc x.desc x.S x.l x.p 0 f emptyGraphConst (emptyStoppedSpec x f deg).tableBits =
      emptyStoppedDescRaw x.desc (polynomialBits f) x.S x.p x.l := by
  unfold stoppedDesc emptyStoppedDescRaw D3Stopped.descOf
  rw [emptyStoppedSpec_tableBits, encodeList_eq_pack_map, encodeList_eq_pack_map,
      encodeList_eq_pack_map]
  rfl

theorem emptyStoppedSpec_value {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) (deg q : ℕ) (α : Fin deg → Bool) :
    (emptyStoppedSpec x f deg).value hf x.A q α = 1 := by
  unfold StoppedSpec.value BTNContract
  have h1 : (∑ x_e : Fin emptyGraphConst.nE → Bool,
      ∏ v : Fin emptyGraphConst.nV, (emptyStoppedSpec x f deg).entry hf x.A α v
        (fun i => x_e ((emptyGraphConst.ports v).get i))) = 1 := by
    have hfin : (Fin emptyGraphConst.nE → Bool) ≃ Unit :=
      ⟨fun _ => (), fun _ e => Fin.elim0 e, fun g => funext fun e => Fin.elim0 e, fun _ => rfl⟩
    rw [Fintype.sum_equiv hfin _ (fun _ => 1)]
    · simp
    · intro g
      exact Finset.prod_eq_one fun v _ => Fin.elim0 v
  rw [h1]
  have h1_lift : lift hf q (1 : B f x.l x.p) = 1 := by
    unfold lift word
    have h0_l : 0 < x.l := x.hl
    have h1p : 1 < 2 ^ x.p := Nat.one_lt_pow (by have := x.hp; omega) (by decide)
    have h_outer : AdjoinRoot.modByMonicHom (hf.map (Int.castRingHom (ZMod (2 ^ x.p)))) (1 : U f x.p) = 1 := by
      nontriviality ZMod (2 ^ x.p)
      rw [← (AdjoinRoot.mk _).map_one, AdjoinRoot.modByMonicHom_mk,
          (modByMonic_eq_self_iff (hf.map _)).mpr]
      rw [degree_eq_natDegree (hf.map _).ne_zero, hf.natDegree_map]
      exact degree_one_le.trans_lt (Nat.cast_pos.mpr hdeg)
    have hread : ∀ (j : Fin x.l) (i : Fin f.natDegree),
        ((AdjoinRoot.modByMonicHom (hf.map _) ((AdjoinRoot.modByMonicHom (monic_X_pow x.l) (1 : B f x.l x.p)).coeff j.val)).coeff i.val : ZMod (2 ^ x.p)).val =
          if j.val = 0 ∧ i.val = 0 then 1 else 0 := by
      intro j i
      have h_inner : (AdjoinRoot.modByMonicHom (monic_X_pow x.l) (1 : B f x.l x.p)).coeff j.val =
          if j.val = 0 then (1 : U f x.p) else 0 := by
        nontriviality U f x.p
        have hm1 : AdjoinRoot.modByMonicHom (monic_X_pow x.l) (1 : B f x.l x.p) = 1 := by
          rw [← (AdjoinRoot.mk ((X : (U f x.p)[X]) ^ x.l)).map_one, AdjoinRoot.modByMonicHom_mk,
              (modByMonic_eq_self_iff (monic_X_pow x.l)).mpr]
          rw [degree_eq_natDegree (monic_X_pow x.l).ne_zero, natDegree_X_pow]
          exact degree_one_le.trans_lt (Nat.cast_pos.mpr h0_l)
        rw [hm1, coeff_one]
      rw [h_inner]
      by_cases hj : j.val = 0
      · rw [if_pos hj, h_outer, coeff_one]
        by_cases hi : i.val = 0
        · simp [hj, hi, @ZMod.val_one (2 ^ x.p) ⟨h1p⟩]
        · simp [hj, hi]
      · rw [if_neg hj, map_zero, coeff_zero]
        simp [hj]
    simp_rw [hread]
    let j0 : Fin x.l := ⟨0, h0_l⟩
    let i0 : Fin f.natDegree := ⟨0, hdeg⟩
    rw [Finset.sum_eq_single j0]
    · simp only [j0, true_and, monomial_zero_left]
      rw [Finset.sum_eq_single i0]
      · simp [i0]
      · intro i _ hne; have : i.val ≠ 0 := fun h => hne (Fin.ext h); simp [this]
      · intro hm; exact False.elim (hm (Finset.mem_univ i0))
    · intro j _ hne; have : j.val ≠ 0 := fun h => hne (Fin.ext h); simp [this]
    · intro hm; exact False.elim (hm (Finset.mem_univ j0))
  exact h1_lift










private theorem pairwise_filter {α : Type} {R : α → α → Prop} {p : α → Bool} {xs : List α}
    (h : xs.Pairwise R) : (xs.filter p).Pairwise R := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons] at h
    by_cases hx : p x
    · simp only [List.filter_cons, hx, ↓reduceIte, List.pairwise_cons]
      exact ⟨fun y hy => h.1 y (List.mem_filter.mp hy).1, ih h.2⟩
    · simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte]
      exact ih h.2

theorem eq_of_pairwise_lt {xs ys : List ℕ} (hx : xs.Pairwise (· < ·))
    (hy : ys.Pairwise (· < ·)) (hmem : ∀ m, m ∈ xs ↔ m ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys' => exact False.elim (by simpa using (hmem y).mpr List.mem_cons_self)
  | cons x xs ih =>
    cases ys with
    | nil => exact False.elim (by simpa using (hmem x).mp List.mem_cons_self)
    | cons y ys' =>
      rw [List.pairwise_cons] at hx hy
      have hxy : x = y := by
        rcases List.mem_cons.mp ((hmem x).mp List.mem_cons_self) with h1 | h1
        · exact h1
        · have hyx := hy.1 x h1
          rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self) with h2 | h2
          · exact h2.symm
          · have hxy' := hx.1 y h2
            omega
      subst hxy
      congr 1
      apply ih hx.2 hy.2
      intro m
      by_cases hm : m = x
      · subst hm
        have hx1 : m ∉ xs := fun h => Nat.lt_irrefl m (hx.1 m h)
        have hy1 : m ∉ ys' := fun h => Nat.lt_irrefl m (hy.1 m h)
        exact ⟨fun h => absurd h hx1, fun h => absurd h hy1⟩
      · have h1 := hmem m
        simp only [List.mem_cons, hm, false_or] at h1
        exact h1

theorem ports_map_val_pairwise_lt (G : Graph) (v : Fin G.nV) :
    ((G.ports v).map Fin.val).Pairwise (· < ·) := by
  have hfin : (List.finRange G.nE).Pairwise (fun a b : Fin G.nE => a.val < b.val) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa using hij
  have hflt := pairwise_filter (p := fun e => decide ((G.endpoints e).1 = v ∨ (G.endpoints e).2 = v)) hfin
  rw [List.pairwise_map]
  exact hflt

private theorem fin_pairwise_lt_map {α : Type} {xs : List α} {f : α → ℕ}
    (hp : (xs.map f).Pairwise (· < ·)) :
    ∀ {i j : ℕ} (hi : i < xs.length) (hj : j < xs.length),
      f (xs[i]'hi) = f (xs[j]'hj) → i = j := by
  intro i j hi hj heq
  have hp' := List.pairwise_iff_getElem.mp hp
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hlt' := hp' i j (by simpa using hi) (by simpa using hj) hlt
    simp only [List.getElem_map] at hlt'
    omega
  · have hgt' := hp' j i (by simpa using hj) (by simpa using hi) hgt
    simp only [List.getElem_map] at hgt'
    omega

theorem reattach_lp_val_eq {C c : ℕ} (x : Input C c) (n : ℕ)
    (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n)
    (old : Fin x.spec.lookupVerts.card ≃ ↥x.spec.lookupVerts)
    (lp : (v : Fin x.spec.lookupVerts.card) →
      Fin (x.G.deg (old v).val) ≃ Fin ((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).deg (v.castAdd n)))
    (hlp : ∀ v i,
      D4CoreCut.origB x.G x.spec.lookupVerts
        (((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).ports (v.castAdd n)).get (lp v i)) =
      (x.G.ports (old v).val).get i)
    (v : Fin x.spec.lookupVerts.card) (i : Fin (x.G.deg (old v).val)) :
    (lp v i).val = i.val := by
  let L := x.spec.lookupVerts
  let H := D4CoreCut.reattach x.G L n leafFn
  let vH : Fin H.nV := v.castAdd n
  have hmono : ∀ a b : D4CoreCut.B x.G L, a.val < b.val →
      (D4CoreCut.origB x.G L a).val < (D4CoreCut.origB x.G L b).val := by
    intro a b hab
    have hp : ((D4CoreCut.boundaryEdges x.G L).map Fin.val).Pairwise (· < ·) := by
      rw [List.pairwise_map]
      exact pairwise_filter (by
        rw [List.pairwise_iff_getElem]
        intro p q hp hq hpq
        simpa using hpq)
    have hp' := List.pairwise_iff_getElem.mp hp
    simp only [D4CoreCut.origB, List.get_eq_getElem]
    simpa [List.getElem_map] using hp' a.val b.val (by simp [a.isLt]) (by simp [b.isLt]) hab
  have hp_lhs : ((H.ports vH).map (fun e => (D4CoreCut.origB x.G L e).val)).Pairwise (· < ·) := by
    apply List.pairwise_map.mpr
    have hpH := List.pairwise_map.mp (ports_map_val_pairwise_lt H vH)
    exact hpH.imp (fun h => hmono _ _ h)
  have hp_rhs : ((x.G.ports (old v).val).map Fin.val).Pairwise (· < ·) :=
    ports_map_val_pairwise_lt x.G (old v).val
  have heq_list : (H.ports vH).map (fun e => (D4CoreCut.origB x.G L e).val) =
      (x.G.ports (old v).val).map Fin.val := by
    apply eq_of_pairwise_lt hp_lhs hp_rhs
    intro m
    constructor
    · intro hm
      rcases List.mem_map.mp hm with ⟨e, he, rfl⟩
      obtain ⟨r, hr⟩ := List.mem_iff_get.mp he
      let j := (lp v).symm r
      have hlj : lp v j = r := (lp v).apply_symm_apply r
      have h1 : D4CoreCut.origB x.G L e = (x.G.ports (old v).val).get j := by
        calc D4CoreCut.origB x.G L e = D4CoreCut.origB x.G L ((H.ports vH).get r) := congrArg _ hr.symm
          _ = D4CoreCut.origB x.G L ((H.ports vH).get (lp v j)) := by rw [hlj]
          _ = (x.G.ports (old v).val).get j := hlp v j
      rw [h1]
      exact List.mem_map_of_mem (List.get_mem _ j)
    · intro hm
      rcases List.mem_map.mp hm with ⟨e, he, rfl⟩
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
      have h1 : e = D4CoreCut.origB x.G L ((H.ports vH).get (lp v j)) :=
        hj.symm.trans (hlp v j).symm
      rw [h1]
      exact List.mem_map_of_mem (List.get_mem _ (lp v j))
  have hi_len : i.val < (x.G.ports (old v).val).length := i.isLt
  have hlpi_len : (lp v i).val < (H.ports vH).length := (lp v i).isLt
  have hget_rhs : (x.G.ports (old v).val)[i.val]'hi_len = (x.G.ports (old v).val).get i := rfl
  have hget_lhs : (D4CoreCut.origB x.G L ((H.ports vH)[(lp v i).val]'hlpi_len)).val =
      ((x.G.ports (old v).val).get i).val :=
    congrArg Fin.val (hlp v i)
  have getD_map_nat : ∀ {α : Type} (xs : List α) (fn : α → ℕ) (k : ℕ) (hk : k < xs.length),
      (xs.map fn).getD k 0 = fn (xs[k]'hk) := by
    intro α xs fn k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk),
      List.getElem_map, Option.getD_some]
  have hlpi_rhs : (lp v i).val < (x.G.ports (old v).val).length := by
    have hlen1 : ((H.ports vH).map (fun e => (D4CoreCut.origB x.G L e).val)).length = (H.ports vH).length :=
      List.length_map (as := H.ports vH) _
    have hlen2 : ((x.G.ports (old v).val).map Fin.val).length = (x.G.ports (old v).val).length :=
      List.length_map (as := x.G.ports (old v).val) _
    exact ((hlpi_len.trans_eq hlen1.symm).trans_eq (congrArg List.length heq_list)).trans_eq hlen2
  have heq_at : ((x.G.ports (old v).val)[(lp v i).val]'hlpi_rhs).val =
      ((x.G.ports (old v).val)[i.val]'hi_len).val := by
    calc ((x.G.ports (old v).val)[(lp v i).val]'hlpi_rhs).val
        = ((x.G.ports (old v).val).map Fin.val).getD (lp v i).val 0 :=
          (getD_map_nat (x.G.ports (old v).val) Fin.val (lp v i).val hlpi_rhs).symm
      _ = ((H.ports vH).map (fun e => (D4CoreCut.origB x.G L e).val)).getD (lp v i).val 0 :=
          congrArg (fun xs => xs.getD (lp v i).val 0) heq_list.symm
      _ = (D4CoreCut.origB x.G L ((H.ports vH)[(lp v i).val]'hlpi_len)).val :=
          getD_map_nat (H.ports vH) _ (lp v i).val hlpi_len
      _ = ((x.G.ports (old v).val)[i.val]'hi_len).val := hget_lhs.trans (congrArg Fin.val hget_rhs.symm)
  exact fin_pairwise_lt_map hp_rhs hlpi_rhs hi_len heq_at

theorem reattach_lookup_idx {C c : ℕ} (x : Input C c) (n : ℕ)
    (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n)
    (old : Fin x.spec.lookupVerts.card ≃ ↥x.spec.lookupVerts)
    (rank : D4CoreCut.B x.G x.spec.lookupVerts ≃ Fin (4 * x.m * x.k))
    (hrank : ∀ i, (rank i).val = i.val)
    (lp : (v : Fin x.spec.lookupVerts.card) →
      Fin (x.G.deg (old v).val) ≃ Fin ((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).deg (v.castAdd n)))
    (hlp : ∀ v i,
      D4CoreCut.origB x.G x.spec.lookupVerts
        (((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).ports (v.castAdd n)).get (lp v i)) =
      (x.G.ports (old v).val).get i)
    (v : Fin x.spec.lookupVerts.card) (i : Fin (x.G.deg (old v).val)) :
    let L := x.spec.lookupVerts
    let H := D4CoreCut.reattach x.G L n leafFn
    (D4CoreCut.boundaryEdges x.G L).idxOf ((x.G.ports (old v).val).get i) =
      (rank ((H.ports (v.castAdd n)).get (lp v i))).val := by
  intro L H
  let e_b : D4CoreCut.B x.G L := (H.ports (v.castAdd n)).get (lp v i)
  have hnd : (D4CoreCut.boundaryEdges x.G L).Nodup := (List.nodup_finRange _).filter _
  rw [← hlp v i, hrank e_b]
  dsimp only [D4CoreCut.origB]
  have hidx_lt : (D4CoreCut.boundaryEdges x.G L).idxOf ((D4CoreCut.boundaryEdges x.G L).get e_b) <
      (D4CoreCut.boundaryEdges x.G L).length :=
    List.idxOf_lt_length_iff.mpr (List.get_mem _ e_b)
  have hget : (D4CoreCut.boundaryEdges x.G L).get
      ⟨(D4CoreCut.boundaryEdges x.G L).idxOf ((D4CoreCut.boundaryEdges x.G L).get e_b), hidx_lt⟩ =
      (D4CoreCut.boundaryEdges x.G L).get e_b := by
    simp only [List.get_eq_getElem]
    exact List.getElem_idxOf hidx_lt
  exact congrArg Fin.val (hnd.injective_get hget)






theorem hit_node_ports_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (doneNodes : List (SoloNode x f PktOK))
    (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))) :
    let L := x.spec.lookupVerts
    let n := doneNodes.length
    let H := D4CoreCut.reattach x.G L n (hitLeafFn x hbLen doneNodes hperm)
    ∀ j : Fin n,
      (H.ports (Fin.natAdd L.card j)).map Fin.val = (doneNodes.get j).pins.map (·.1.val) := by
  intro L n H j
  let leafHit := hitLeafFn x hbLen doneNodes hperm
  let jH : Fin H.nV := Fin.natAdd L.card j
  have huniq := unique_leaf_of_pinFirsts_perm doneNodes hperm
  have hp_lhs : ((H.ports jH).map Fin.val).Pairwise (· < ·) := ports_map_val_pairwise_lt H jH
  have hp_rhs : ((doneNodes.get j).pins.map (·.1.val)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact (doneNodes.get j).pins_sorted.imp fun h => h
  apply eq_of_pairwise_lt hp_lhs hp_rhs
  intro m
  constructor
  · intro hm
    rcases List.mem_map.mp hm with ⟨e, he, rfl⟩
    have hinc : (H.endpoints e).1 = jH ∨ (H.endpoints e).2 = jH :=
      of_decide_eq_true (List.mem_filter.mp he).2
    have hright : leafHit e = j := by
      rcases hinc with h1 | h2
      · have hlt : ((D4CoreCut.lookupIdx x.G L e).castAdd n).val < L.card :=
          (D4CoreCut.lookupIdx x.G L e).isLt
        have hge : L.card ≤ jH.val := by simp [jH]
        have h1' : ((D4CoreCut.lookupIdx x.G L e).castAdd n).val = jH.val :=
          congrArg Fin.val h1
        omega
      · exact Fin.ext (by
          have h2' : L.card + (leafHit e).val = L.card + j.val := congrArg Fin.val h2
          omega)
    have hspec := (Classical.choose_spec (huniq (e.cast hbLen))).1
    change ∃ kp : Fin (doneNodes.get (leafHit e)).pins.length,
      ((doneNodes.get (leafHit e)).pins.get kp).1 = e.cast hbLen at hspec
    rw [hright] at hspec
    obtain ⟨kp, hkp⟩ := hspec
    refine List.mem_map.mpr ⟨(doneNodes.get j).pins.get kp, List.get_mem _ kp, ?_⟩
    exact congrArg Fin.val hkp
  · intro hm
    rcases List.mem_map.mp hm with ⟨pv, hpv, rfl⟩
    obtain ⟨kp, hkp⟩ := List.mem_iff_get.mp hpv
    let e : D4CoreCut.B x.G L := ⟨pv.1.val, hbLen.symm ▸ pv.1.isLt⟩
    have hj_eq : j = leafHit e := by
      apply (Classical.choose_spec (huniq (e.cast hbLen))).2 j
      refine ⟨kp, ?_⟩
      apply Fin.ext
      dsimp only [e]
      exact congrArg Fin.val (congrArg Prod.fst hkp)
    have hmem_e : e ∈ H.ports jH := by
      apply List.mem_filter.mpr
      refine ⟨List.mem_finRange e, decide_eq_true (Or.inr ?_)⟩
      change Fin.natAdd L.card (leafHit e) = Fin.natAdd L.card j
      rw [← hj_eq]
    exact List.mem_map_of_mem hmem_e

theorem hit_node_deg_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (doneNodes : List (SoloNode x f PktOK))
    (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k)))
    (j : Fin doneNodes.length) :
    (D4CoreCut.reattach x.G x.spec.lookupVerts doneNodes.length (hitLeafFn x hbLen doneNodes hperm)).deg
        (Fin.natAdd x.spec.lookupVerts.card j) = (doneNodes.get j).pins.length := by
  have hlen := congrArg List.length (hit_node_ports_eq x hbLen doneNodes hperm j)
  simpa only [BipartiteMultigraph.deg, List.length_map] using hlen

theorem hit_branch_port_align {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (doneNodes : List (SoloNode x f PktOK))
    (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k)))
    (w : ReattachWit x doneNodes.length (hitLeafFn x hbLen doneNodes hperm))
    (j : Fin doneNodes.length) (kp : Fin (doneNodes.get j).pins.length) :
    w.rank (w.rp j (kp.cast (hit_node_deg_eq x hbLen doneNodes hperm j).symm)).val =
      ((doneNodes.get j).pins.get kp).1 := by
  let L := x.spec.lookupVerts
  let leafHit := hitLeafFn x hbLen doneNodes hperm
  let H := D4CoreCut.reattach x.G L doneNodes.length leafHit
  have hports := hit_node_ports_eq x hbLen doneNodes hperm j
  have hdeg := hit_node_deg_eq x hbLen doneNodes hperm j
  apply Fin.ext
  rw [w.hrank, w.hrp j (kp.cast hdeg.symm)]
  have h1 := congrArg (fun xs : List ℕ => xs.getD kp.val 0) hports
  have hkp_lhs : kp.val < (H.ports (Fin.natAdd L.card j)).length := by
    change kp.val < H.deg (Fin.natAdd L.card j)
    rw [hdeg]; exact kp.isLt
  have hlhs : ((H.ports (Fin.natAdd L.card j)).map Fin.val).getD kp.val 0 =
      ((H.ports (Fin.natAdd L.card j)).get (kp.cast hdeg.symm)).val := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hkp_lhs),
      List.getElem_map, Option.getD_some]
    rfl
  have hrhs : ((doneNodes.get j).pins.map (·.1.val)).getD kp.val 0 =
      ((doneNodes.get j).pins.get kp).1.val := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp),
      List.getElem_map, Option.getD_some]
    rfl
  rw [hlhs, hrhs] at h1
  exact h1





def mkPlanBranch {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (guard B_bud : ℕ) (certTree : D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard))
    (hvalid : treeAll SoloLeafData.Valid certTree)
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (u : Fin (2 ^ B_bud)) : PlanBranchData x f (pktOKOf E_pkt o_pkt K_loc x f hf) (guard + x.p) :=
  mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen
    (fun dn hp => hit_node_deg_eq x hbLen dn hp) u







private theorem castB_lift_of_eq {f : ℤ[X]} (hf : f.Monic) {l g p₁ p : ℕ}
    (hp : p₁ = p) (z : B f l p₁) :
    castB f l g p (lift hf (g + p) z) = lift hf p z := by
  subst hp
  rw [castB_lift, self_lift hf z]

theorem rootSoloNode_pinFirsts {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) :
    pinFirsts ([rootSoloNode x f PktOK] : List (SoloNode x f PktOK)) =
      List.finRange (4 * x.m * x.k) := by
  let rootNode := rootSoloNode x f PktOK
  let L := x.spec.lookupVerts
  let t := rootCut x
  have hSpec := DetDLP.d4_core_cut_poly_and_spec.2 x
  have hcut : D4CoreCut.cutCoreRaw (D4Plan.input x) = t.encode x.G L := hSpec.1
  have hbLen : t.boundary.length = 4 * x.m * x.k := hSpec.2.2.2.2.1
  have hbits := rootSoloNode_bits_eq x f PktOK
  have hlhs : (unpack (fld rootNode.toWorkItem.bits 3)).map (fun w => (ints w).getD 0 0) =
      rootNode.pins.map (fun pv => pv.1.val) := by
    unfold SoloNode.toWorkItem WorkItem.bits
    simp [fld_pack, unpack_pack, List.map_map, ints_encodeNatListBin]
  have hrhs : (unpack (fld (rootRaw (D4CoreCut.cutCoreRaw (D4Plan.input x)) x.p) 3)).map
      (fun w => (ints w).getD 0 0) = List.range (4 * x.m * x.k) := by
    rw [hcut]
    unfold rootRaw D4CoreCut.Cut.encode
    simp only [fld_pack, fld_encodeList_id, List.getD_cons_succ, List.getD_cons_zero, unpack_pack,
      List.map_map, Function.comp_def, ints_encodeNatListBin, List.length_ofFn, hbLen, List.map_id']
  have hvals : rootNode.pins.map (fun pv => pv.1.val) = List.range (4 * x.m * x.k) := by
    rw [← hlhs, hbits, hrhs]
  have hlen : rootNode.pins.length = 4 * x.m * x.k := by
    have h1 := congrArg List.length hvals
    simpa using h1
  unfold pinFirsts
  rw [List.flatMap_singleton]
  apply List.ext_getElem
  · simp [rootNode, hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_finRange]
    apply Fin.ext
    have hi : i < rootNode.pins.length := by simpa using h1
    have hget := congrArg (fun xs : List ℕ => xs.getD i 0) hvals
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]),
        List.getElem_map, Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [hlen] using hi),
        List.getElem_range, Option.getD_some] at hget
    exact hget

theorem mkPlanBranch_none {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc guard B_bud : ℕ)
    (certTree : D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard))
    (hvalid : treeAll SoloLeafData.Valid certTree)
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (u : Fin (2 ^ B_bud)) (hnone : certTree.read B_bud u.val = none) :
    mkPlanBranch x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u =
      let L := x.spec.lookupVerts
      let lfFn := missLeafFn x hbLen
      let H := D4CoreCut.reattach x.G L (4 * x.m) lfFn
      ⟨4 * x.m, lfFn, 0,
        fun _ => emptyStoppedDescRaw x.desc (polynomialBits f) x.S x.p x.l,
        fun j β => (emptyStoppedSpec x f (H.deg (Fin.natAdd L.card j))).value hf x.A (guard + x.p) β⟩ := by
  unfold mkPlanBranch mkPlanBranchAux
  dsimp only
  split
  · rfl
  · rename_i lf hsome
    rw [hnone] at hsome
    cases hsome

theorem mkPlanBranch_some {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc guard B_bud : ℕ)
    (certTree : D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard))
    (hvalid : treeAll SoloLeafData.Valid certTree)
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (u : Fin (2 ^ B_bud)) (lf : SoloLeafData x hf E_pkt o_pkt K_loc guard)
    (hsome : certTree.read B_bud u.val = some lf) :
    mkPlanBranch x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u =
      let hlf : lf.Valid := treeAll_read hvalid B_bud u.val hsome
      let lfFn := hitLeafFn x hbLen lf.doneNodes hlf.2.2.2
      ⟨lf.doneNodes.length, lfFn, lf.weight,
        fun j =>
          let nd := lf.doneNodes.get j
          stoppedDesc x.desc x.S x.l nd.pCurr nd.d f nd.G nd.toStoppedSpec.tableBits,
        fun j β =>
          let nd := lf.doneNodes.get j
          let hdeg := hit_node_deg_eq x hbLen lf.doneNodes hlf.2.2.2 j
          nd.toStoppedSpec.value hf x.A (guard + x.p) (fun kp => β (kp.cast hdeg.symm))⟩ := by
  unfold mkPlanBranch mkPlanBranchAux
  dsimp only
  split
  · rename_i hnone
    rw [hsome] at hnone
    cases hnone
  · rename_i lf' hsome'
    have heq : lf' = lf := Option.some.inj (hsome'.symm.trans hsome)
    subst heq
    rfl

private theorem reattach_contr_eval {C c : ℕ} (x : Input C c) (n : ℕ)
    (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n)
    (w : ReattachWit x n leafFn)
    {R : Type} [CommRing R]
    (T : (v : ↥x.spec.lookupVerts) → (Fin (x.G.deg v.val) → Bool) → R)
    (F : (j : Fin n) → ({e : D4CoreCut.B x.G x.spec.lookupVerts // leafFn e = j} → Bool) → R)
    (G_right : (j : Fin n) →
      (Fin ((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).deg
        (Fin.natAdd x.spec.lookupVerts.card j)) → Bool) → R)
    (hG : ∀ j β, G_right j β = F j (fun e => β ((w.rp j).symm e))) :
    BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn)
      (Fin.addCases (fun v β => T (w.old v) (fun i => β (w.lp v i))) G_right) =
    ∑ η : Fin (4 * x.m * x.k) → Bool,
      (∏ v : Fin x.spec.lookupVerts.card,
        T (w.old v) (fun i => η (w.rank
          (((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).ports (v.castAdd n)).get (w.lp v i))))) *
      ∏ j : Fin n, F j (fun e => η (w.rank e.val)) := by
  have hfg : G_right = fun j β => F j (fun e => β ((w.rp j).symm e)) := by
    funext j β; exact hG j β
  rw [hfg]
  exact w.hcontr R T F

private theorem branch_contr_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc guard B_bud : ℕ)
    (certTree : D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard))
    (hvalid : treeAll SoloLeafData.Valid certTree)
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (u : Fin (2 ^ B_bud)) :
    let L := x.spec.lookupVerts
    let q := guard + x.p
    let t := rootCut x
    let b := mkPlanBranch x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u
    b.wVal * BTNContract (D4CoreCut.reattach x.G L b.n b.leafFn)
      (let w := getReattachWit x b.n b.leafFn
       Fin.addCases (fun v β => liftBase f x.l q (x.A (w.old v).val (fun i => β (w.lp v i)))) b.rightV) =
    ∑ η : Fin (4 * x.m * x.k) → Bool,
      (∏ v : ↥L, liftBase f x.l q (x.A v.val fun i =>
        (List.ofFn η).getD (t.boundary.idxOf ((x.G.ports v.val).get i)) false)) *
      ((certTree.read B_bud u.val).map (fun lf => lf.weight * lf.doneProd η)).getD 0 := by
  let L := x.spec.lookupVerts
  let q := guard + x.p
  let t := rootCut x
  let PktOK := pktOKOf E_pkt o_pkt K_loc x f hf
  let P_look : (Fin (4 * x.m * x.k) → Bool) → B f x.l q := fun η =>
    ∏ v : ↥L, liftBase f x.l q (x.A v.val fun i =>
      (List.ofFn η).getD (t.boundary.idxOf ((x.G.ports v.val).get i)) false)
  let branchContr : PlanBranchData x f PktOK q → B f x.l q := fun b =>
    b.wVal * BTNContract (D4CoreCut.reattach x.G L b.n b.leafFn)
      (let w := getReattachWit x b.n b.leafFn
       Fin.addCases (fun v β => liftBase f x.l q (x.A (w.old v).val (fun i => β (w.lp v i)))) b.rightV)
  change branchContr (mkPlanBranch x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u) =
    ∑ η : Fin (4 * x.m * x.k) → Bool,
      P_look η * ((certTree.read B_bud u.val).map (fun lf => lf.weight * lf.doneProd η)).getD 0
  cases hread : certTree.read B_bud u.val with
  | none =>
    rw [congrArg branchContr (mkPlanBranch_none x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u hread)]
    simp only [branchContr, zero_mul, Option.map_none, Option.getD_none, mul_zero, Finset.sum_const_zero]
  | some lf =>
    rw [congrArg branchContr (mkPlanBranch_some x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u lf hread)]
    simp only [Option.map_some, Option.getD_some]
    have hlf : lf.Valid := treeAll_read hvalid B_bud u.val hread
    let n := lf.doneNodes.length
    let leafHit := hitLeafFn x hbLen lf.doneNodes hlf.2.2.2
    let H := D4CoreCut.reattach x.G L n leafHit
    change lf.weight * BTNContract H
      (let w := getReattachWit x n leafHit
       Fin.addCases (fun v β => liftBase f x.l q (x.A (w.old v).val (fun i => β (w.lp v i))))
         (fun j β =>
           let nd := lf.doneNodes.get j
           let hdeg := hit_node_deg_eq x hbLen lf.doneNodes hlf.2.2.2 j
           nd.toStoppedSpec.value hf x.A q (fun kp => β (kp.cast hdeg.symm)))) =
      ∑ η : Fin (4 * x.m * x.k) → Bool, P_look η * (lf.weight * lf.doneProd η)
    generalize getReattachWit x n leafHit = w
    dsimp only
    let F_node : (j : Fin n) → ({e : D4CoreCut.B x.G L // leafHit e = j} → Bool) → B f x.l q :=
      fun j α =>
        let nd := lf.doneNodes.get j
        have hdeg := hit_node_deg_eq x hbLen lf.doneNodes hlf.2.2.2 j
        nd.toStoppedSpec.value hf x.A q (fun kp => α (w.rp j (kp.cast hdeg.symm)))
    have hbtn := reattach_contr_eval x n leafHit w
      (fun v α => liftBase f x.l q (x.A v.val α)) F_node
      (fun j β =>
        let nd := lf.doneNodes.get j
        have hdeg := hit_node_deg_eq x hbLen lf.doneNodes hlf.2.2.2 j
        nd.toStoppedSpec.value hf x.A q (fun kp => β (kp.cast hdeg.symm)))
      (fun j β => by simp only [F_node, Equiv.symm_apply_apply])
    rw [hbtn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    have hP_eq : (∏ v : Fin L.card, liftBase f x.l q (x.A (w.old v).val
        (fun i => η (w.rank (((D4CoreCut.reattach x.G x.spec.lookupVerts n leafHit).ports (v.castAdd n)).get (w.lp v i)))))) = P_look η := by
      apply Fintype.prod_equiv w.old
      intro v
      congr 2; funext i
      have getD_ofFn_bool : ∀ {m : ℕ} (fn : Fin m → Bool) (r : Fin m) (k : ℕ),
          k = r.val → (List.ofFn fn).getD k false = fn r := by
        intro m fn r k hk
        subst hk
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [r.isLt]),
          List.getElem_ofFn, Option.getD_some]
      have hidx := reattach_lookup_idx x n leafHit w.old w.rank w.hrank w.lp w.hlp v i
      exact (getD_ofFn_bool η _ _ hidx).symm
    have hR_eq : (∏ j : Fin n, F_node j (fun e => η (w.rank e.val))) = lf.doneProd η := by
      have hprod_get : ∀ {α β : Type} [CommMonoid β] (xs : List α) (g : α → β),
          (xs.map g).prod = ∏ j : Fin xs.length, g (xs.get j) := by
        intro α β _ xs g
        rw [Fin.prod_univ_def]
        congr 1
        exact List.ext_getElem (by simp) (fun idx h1 _ => by simp)
      unfold SoloLeafData.doneProd
      rw [hprod_get]
      apply Finset.prod_congr rfl
      intro j _
      dsimp only [F_node, SoloNode.pinnedVal, StoppedSpec.value]
      have halign := hit_branch_port_align x hbLen lf.doneNodes hlf.2.2.2 w j
      rw [SoloNode.toStoppedSpec_entry_eq hf (lf.doneNodes.get j)]
      congr 3
      funext k_pin
      exact congrArg η (halign k_pin)
    rw [hP_eq, hR_eq, mul_left_comm]




def soloPlan {C c : ℕ} (hC : 0 < C) (x : Input C c) (hL_level : 1 ≤ D3Stopped.level x.S)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ)
    (hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
    (hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
    (rootUnroll : SoloUnroll x (soloPoly_monic hL_level) M_node E_pkt o_node o_pkt K_loc H_loc c_loc
      (Nat.clog 32 (4 * x.m)) (rootSoloNode x (soloPoly x.S) (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) (soloPoly_monic hL_level)))) :
    Plan x :=
  let f := soloPoly x.S
  let hf := soloPoly_monic hL_level
  let hdeg_f := soloPoly_natDegree hL_level
  let hdeg_pos : 0 < f.natDegree := by rw [hdeg_f]; exact Nat.mul_pos (by decide) hL_level
  let D := Nat.clog 32 (4 * x.m)
  let guard := totalGuard x.S D
  let q := guard + x.p
  let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
  let PktOK := pktOKOf E_pkt o_pkt K_loc x f hf
  let rootNode := rootSoloNode x f PktOK
  let certTree := unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
    [⟨D, rootNode, rootUnroll⟩] [] 1 0
  have hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k :=
    (DetDLP.d4_core_cut_poly_and_spec.2 x).2.2.2.2.1
  have hbudSpec := (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose_spec.choose_spec x hL_bud
  have hslots : D4GuardTree.slots D ≤ 64 ^ D := slots_bound_64 D
  have hwork : D4UnrollBudget.Work x.S D (8 * K_loc) [(0, rootNode.G.nE)] certTree := by
    have hw := unrollCertFuel_work x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard
      (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] 1 0 (by simpa [remSlots] using hslots)
    exact hw
  have hM_root : rootNode.G.nE ≤ x.S := by
    have h1 := rootNode.edges_le
    rw [rootSoloNode_d, pow_zero, Nat.div_one] at h1
    exact h1
  have hfits : certTree.Fits B_bud := hbudSpec.2.2 hM_root hwork
  have hvalid : treeAll SoloLeafData.Valid certTree := by
    apply unrollCertFuel_all_valid x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
      (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] 1 0
    · simpa [remSlots] using hslots
    · simp only [remSlots, List.map_singleton, List.sum_singleton, zero_add]
      exact Nat.mul_le_mul_left _ hslots
    · simp [remLeaves, D]
    · intro _ hm; cases hm
    · simp only [List.nil_append, todoNodes, List.map_singleton]
      rw [rootSoloNode_pinFirsts x f PktOK]
  let br := mkPlanBranch x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen
  let L := x.spec.lookupVerts
  { f := f
    hf := hf
    deg := hdeg_f
    zero := ⟨0, hdeg_pos⟩
    zero_val := rfl
    guard := guard
    N := 2 ^ B_bud
    R := fun u => D4CoreCut.reattach x.G L (br u).n (br u).leafFn
    V := fun u =>
      let w := getReattachWit x (br u).n (br u).leafFn
      Fin.addCases
        (fun v β => liftBase f x.l q (x.A (w.old v).val (fun i => β (w.lp v i))))
        (br u).rightV
    w := fun u => (br u).wVal
    source := fun u =>
      let w := getReattachWit x (br u).n (br u).leafFn
      Fin.addCases
        (fun v => lookupDesc x.desc (w.old v).val.val f.natDegree x.l q)
        (br u).rightSrc
    edges := fun u => (DetDLP.d4_reattach_poly_and_spec.2 x (br u).n (br u).leafFn).2.1
    vertices := fun u => by
      have hnV := (DetDLP.d4_reattach_poly_and_spec.2 x (br u).n (br u).leafFn).2.2.1
      change (D4CoreCut.reattach x.G L (br u).n (br u).leafFn).nV ≤ 4 * x.m + 64 ^ D
      rw [hnV]
      have hn_le : (br u).n ≤ 64 ^ D := by
        dsimp only [br]
        cases hread : certTree.read B_bud u.val with
        | none =>
          rw [mkPlanBranch_none x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u hread]
          have h32 : 4 * x.m ≤ 32 ^ D := Nat.le_pow_clog (by decide : 1 < 32) (4 * x.m)
          exact h32.trans (Nat.pow_le_pow_left (by decide) D)
        | some lf =>
          rw [mkPlanBranch_some x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u lf hread]
          exact (treeAll_read hvalid B_bud u.val hread).2.1
      exact Nat.add_le_add_left hn_le _
    degree := fun u => by
      have hxk_le : x.k * x.m ≤ 1217 * (C + 1) ^ 3 * x.b := by
        have h1 : x.k * x.m ≤ 4 * x.m * x.k := by
          calc x.k * x.m = 1 * x.m * x.k := by ring
            _ ≤ 4 * x.m * x.k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
        have h2 : C * x.b ≤ 1217 * (C + 1) ^ 3 * x.b := by
          apply Nat.mul_le_mul_right
          calc C ≤ C + 1 := Nat.le_succ C
            _ ≤ (C + 1) * (C + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
            _ = 1 * (C + 1) ^ 3 := by ring
            _ ≤ 1217 * (C + 1) ^ 3 := Nat.mul_le_mul_right _ (by decide)
        exact h1.trans (x.upper.trans h2)
      dsimp only [br]
      cases hread : certTree.read B_bud u.val with
      | none =>
        rw [mkPlanBranch_none x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u hread]
        dsimp only
        have hre := DetDLP.d4_reattach_poly_and_spec.2 x (4 * x.m) (missLeafFn x hbLen)
        have hcard : ∀ j : Fin (4 * x.m),
            Fintype.card {i : D4CoreCut.B x.G L // missLeafFn x hbLen i = j} ≤ x.k := by
          intro j
          let emb : {i : D4CoreCut.B x.G L // missLeafFn x hbLen i = j} → Fin x.k :=
            fun e => ⟨e.1.val % x.k, Nat.mod_lt _ x.hk⟩
          have hinj : Function.Injective emb := by
            intro a b hab
            apply Subtype.ext; apply Fin.ext
            have ha_div : a.1.val / x.k = j.val := congrArg Fin.val a.2
            have hb_div : b.1.val / x.k = j.val := congrArg Fin.val b.2
            have ha_mod : a.1.val % x.k = b.1.val % x.k := congrArg Fin.val hab
            calc a.1.val = x.k * (a.1.val / x.k) + a.1.val % x.k := (Nat.div_add_mod a.1.val x.k).symm
              _ = x.k * (b.1.val / x.k) + b.1.val % x.k := by rw [ha_div, hb_div, ha_mod]
              _ = b.1.val := Nat.div_add_mod b.1.val x.k
          exact (Fintype.card_le_of_injective emb hinj).trans (by simp)
        have hmd := hre.2.2.2.1 x.k hcard
        simp only [max_self] at hmd
        exact (Nat.mul_le_mul_right x.m hmd).trans hxk_le
      | some lf =>
        rw [mkPlanBranch_some x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u lf hread]
        dsimp only
        have hlf : lf.Valid := treeAll_read hvalid B_bud u.val hread
        let leafHit := hitLeafFn x hbLen lf.doneNodes hlf.2.2.2
        have hre := DetDLP.d4_reattach_poly_and_spec.2 x lf.doneNodes.length leafHit
        let U := (1217 * (C + 1) ^ 3 * x.b) / x.m
        have hcard : ∀ j : Fin lf.doneNodes.length,
            Fintype.card {i : D4CoreCut.B x.G L // leafHit i = j} ≤ U := by
          intro j
          let nd := lf.doneNodes.get j
          have hdeg := hit_node_deg_eq x hbLen lf.doneNodes hlf.2.2.2 j
          let w := getReattachWit x lf.doneNodes.length leafHit
          have hcard_eq : Fintype.card {i : D4CoreCut.B x.G L // leafHit i = j} = nd.pins.length := by
            rw [← Fintype.card_fin nd.pins.length, ← hdeg, Fintype.card_congr (w.rp j).symm]
          rw [hcard_eq]
          have hpins_mul := stopped_pins_bound (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose
            (fun x' hl' => (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose_spec.choose_spec x' hl' |>.2.2.2.1)
            x hL_grd nd (hlf.2.2.1 nd (List.get_mem _ j))
          exact (Nat.le_div_iff_mul_le x.hm).mpr hpins_mul
        have hmd := hre.2.2.2.1 U hcard
        have hU_mul : U * x.m ≤ 1217 * (C + 1) ^ 3 * x.b := Nat.div_mul_le_self _ _
        have hmax_mul : max x.k U * x.m ≤ 1217 * (C + 1) ^ 3 * x.b := by
          rcases le_total x.k U with hle | hle
          · simpa [max_eq_right hle] using hU_mul
          · simpa [max_eq_left hle] using hxk_le
        exact (Nat.mul_le_mul_right x.m hmd).trans hmax_mul
    correct := by
      let t := rootCut x
      let P_look : (q' : ℕ) → (Fin (4 * x.m * x.k) → Bool) → B f x.l q' := fun q' η =>
        ∏ v : ↥L, liftBase f x.l q' (x.A v.val fun i =>
          (List.ofFn η).getD (t.boundary.idxOf ((x.G.ports v.val).get i)) false)
      have hsum_all : (∑ u : Fin (2 ^ B_bud),
          (br u).wVal * BTNContract (D4CoreCut.reattach x.G L (br u).n (br u).leafFn)
            (let w := getReattachWit x (br u).n (br u).leafFn
             Fin.addCases (fun v β => liftBase f x.l q (x.A (w.old v).val (fun i => β (w.lp v i)))) (br u).rightV)) =
          (2 : B f x.l q) ^ guard * ∑ η : Fin (4 * x.m * x.k) → Bool,
            P_look q η * SoloNode.pinnedVal hf q η rootNode := by
        have hterm_congr : ∀ u : Fin (2 ^ B_bud),
            (br u).wVal * BTNContract (D4CoreCut.reattach x.G L (br u).n (br u).leafFn)
              (let w := getReattachWit x (br u).n (br u).leafFn
               Fin.addCases (fun v β => liftBase f x.l q (x.A (w.old v).val (fun i => β (w.lp v i)))) (br u).rightV) =
            ∑ η : Fin (4 * x.m * x.k) → Bool,
              P_look q η * ((certTree.read B_bud u.val).map (fun lf => lf.weight * lf.doneProd η)).getD 0 :=
          fun u => branch_contr_eq x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u
        rw [Finset.sum_congr rfl fun u _ => hterm_congr u, Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro η _
        rw [← Finset.mul_sum]
        rw [DetDLP.d4_adaptive_padded_rank_sum certTree (fun lf => lf.weight * lf.doneProd η) B_bud hfits]
        rw [root_unrollCert_total_eq x hf hdeg_pos M_node E_pkt o_node o_pkt K_loc H_loc c_loc rootNode
          (rootSoloNode_d x f PktOK) rootUnroll η]
        exact mul_left_comm _ _ _
      let y : B f x.l q := ∑ η : Fin (4 * x.m * x.k) → Bool, P_look q η * SoloNode.pinnedVal hf q η rootNode
      have hcast_y : castB f x.l guard x.p y =
          BTNContract x.G (fun v α => liftBase f x.l x.p (x.A v α)) := by
        dsimp only [y]
        rw [map_sum]
        have hctr := rootSoloNode_contract_eq x f hf PktOK
        dsimp only [rootNode, rootCut] at hctr ⊢
        rw [hctr]
        apply Finset.sum_congr rfl
        intro η _
        rw [map_mul]
        congr 1
        · dsimp only [P_look]
          rw [map_prod]
          apply Finset.prod_congr rfl
          intro v _
          exact castB_liftBase f x.l guard x.p _
        · dsimp only [SoloNode.pinnedVal]
          exact castB_lift_of_eq hf (rootSoloNode_pCurr x f PktOK)
            (BTNContract rootNode.G (pin (rootNode.openTensor hf) (fun kp => η (rootNode.pins.get kp).1)))
      have hZ_eq : BTNContract x.G (fun v α => liftBase f x.l x.p (x.A v α)) = polyToB f x.l x.p (Z x) := by
        unfold Z
        rw [← BTNContract_polyToB]
        congr 1; funext v α
        exact liftBase_eq_polyToB f x.l x.p (x.A v α)
      unfold answer
      dsimp only
      rw [hsum_all]
      congr 1; congr 1
      funext j
      change ((Z x).coeff j.val : ZMod (2 ^ x.p)).val =
        word f x.l (guard + x.p) hf ((2 : B f x.l q) ^ guard * y) j ⟨0, hdeg_pos⟩ / 2 ^ guard
      rw [word_two_pow_mul_div hf y j ⟨0, hdeg_pos⟩, hcast_y, hZ_eq,
        word_polyToB_zero hf x.l x.p (Z x) j ⟨0, hdeg_pos⟩ rfl] }





end
end DetDLP.M14PlanInternal

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    (∀ {C c : ℕ} (x : Input C c) (n : ℕ) (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n),
      let w := getReattachWit x n leafFn
      (∀ v, (w.old v).val = (D4CoreCut.lookupVerts x.G x.spec.lookupVerts)[v.val]'(by
        rw [D4CoreCut.lookup_length]; exact v.isLt)) ∧
      (∀ v i, (w.lp v i).val = i.val)) ∧
    (∀ {C c : ℕ} (x : Input C c) (f : ℤ[X]) (deg : ℕ),
      (emptyStoppedSpec x f deg).tableBits = pack [] ∧
      stoppedDesc x.desc x.S x.l x.p 0 f emptyGraphConst (emptyStoppedSpec x f deg).tableBits =
        emptyStoppedDescRaw x.desc (polynomialBits f) x.S x.p x.l) ∧
    (∀ {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l),
      pinFirsts ([rootSoloNode x f PktOK] : List (SoloNode x f PktOK)) =
        List.finRange (4 * x.m * x.k)) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
      (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
      (doneNodes : List (SoloNode x f PktOK))
      (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
      HitDegProp x hbLen doneNodes hperm) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
      (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc guard B_bud : ℕ)
      (certTree : D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard))
      (hvalid : treeAll SoloLeafData.Valid certTree)
      (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
      (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
        (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
        HitDegProp x hbLen doneNodes hperm)
      (u : Fin (2 ^ B_bud)),
      (certTree.read B_bud u.val = none →
        mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all u =
          let L := x.spec.lookupVerts
          let lfFn := missLeafFn x hbLen
          let H := D4CoreCut.reattach x.G L (4 * x.m) lfFn
          ⟨4 * x.m, lfFn, 0,
            fun _ => emptyStoppedDescRaw x.desc (polynomialBits f) x.S x.p x.l,
            fun j β => (emptyStoppedSpec x f (H.deg (Fin.natAdd L.card j))).value hf x.A (guard + x.p) β⟩) ∧
      (∀ lf (hsome : certTree.read B_bud u.val = some lf),
        mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all u =
          let hlf : lf.Valid := treeAll_read hvalid B_bud u.val hsome
          let lfFn := hitLeafFn x hbLen lf.doneNodes hlf.2.2.2
          ⟨lf.doneNodes.length, lfFn, lf.weight,
            fun j =>
              let nd := lf.doneNodes.get j
              stoppedDesc x.desc x.S x.l nd.pCurr nd.d f nd.G nd.toStoppedSpec.tableBits,
            fun j β =>
              let nd := lf.doneNodes.get j
              let hdeg := hdeg_all lf.doneNodes hlf.2.2.2 j
              nd.toStoppedSpec.value hf x.A (guard + x.p) (fun kp => β (kp.cast hdeg.symm))⟩)) ∧
    (∀ {C c : ℕ} (hC : 0 < C) (x : Input C c)
      (hL_level : 1 ≤ D3Stopped.level x.S)
      (hf : (soloPoly x.S).Monic)
      (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
      (K_loc H_loc c_loc : ℕ)
      (hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
      (hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
      (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
        (Nat.clog 32 (4 * x.m))
        (rootSoloNode x (soloPoly x.S)
          (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) hf)))
      (hvalid : treeAll SoloLeafData.Valid
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
          (totalGuard x.S (Nat.clog 32 (4 * x.m))) (64 ^ Nat.clog 32 (4 * x.m))
          [⟨Nat.clog 32 (4 * x.m),
            rootSoloNode x (soloPoly x.S)
              (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) hf),
            rootUnroll⟩] [] 1 0))
      (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
      (hdeg_all : ∀ (doneNodes : List (SoloNode x (soloPoly x.S)
          (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) hf)))
        (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
        HitDegProp x hbLen doneNodes hperm)
      (hpos : 0 < (soloPoly x.S).natDegree),
      let f := soloPoly x.S
      let D := Nat.clog 32 (4 * x.m)
      let guard := totalGuard x.S D
      let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
      let certTree := unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
        [⟨D, rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf), rootUnroll⟩] [] 1 0
      let br := mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all
      (∀ u : Fin (2 ^ B_bud),
        (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).nV ≤
          4 * x.m + 64 ^ Nat.clog 32 (4 * x.m)) ∧
      (∀ u : Fin (2 ^ B_bud),
        (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).maxDeg * x.m ≤
          1217 * (C + 1) ^ 3 * x.b) ∧
      (answer x = encodeNatListBin (List.ofFn fun j : Fin x.l =>
        word f x.l (guard + x.p) hf
          (∑ u : Fin (2 ^ B_bud), (br u).wVal *
            BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn)
              (planVOfBr x f guard B_bud br u))
          j ⟨0, hpos⟩ / 2 ^ guard))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C c x n leafFn
    let w := getReattachWit x n leafFn
    exact ⟨fun v => DetDLP.M14PlanInternal.reattach_old_eq x n leafFn w.old w.lp w.hlp v,
      fun v i => DetDLP.M14PlanInternal.reattach_lp_val_eq x n leafFn w.old w.lp w.hlp v i⟩
  · intro C c x f deg
    exact ⟨DetDLP.M14PlanInternal.emptyStoppedSpec_tableBits x f deg,
      DetDLP.M14PlanInternal.emptyStoppedSpec_desc x f deg⟩
  · intro C c x f PktOK
    exact DetDLP.M14PlanInternal.rootSoloNode_pinFirsts x f PktOK
  · intro C c x f PktOK hbLen doneNodes hperm
    exact DetDLP.M14PlanInternal.hit_node_deg_eq x hbLen doneNodes hperm
  · intro C c x f hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all u
    exact ⟨fun hnone => DetDLP.M14PlanInternal.mkPlanBranch_none x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u hnone,
      fun lf hsome => DetDLP.M14PlanInternal.mkPlanBranch_some x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen u lf hsome⟩
  · intro C c hC x hL_level hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc hL_bud hL_grd rootUnroll hvalid hbLen hdeg_all hpos
    let P₀ := DetDLP.M14PlanInternal.soloPlan hC x hL_level M_node E_pkt o_node o_pkt K_loc H_loc c_loc hL_bud hL_grd rootUnroll
    exact ⟨P₀.vertices, P₀.degree, P₀.correct⟩
