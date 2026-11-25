-- Prove2me | solution 1 for DetDLP.f9a2_b_mul_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:23:18.71016+00:00
-- url     : https://prove2.me/submissions/e5cf3d4e-7e5b-4d6c-8bb0-ecfa9661e0ae

import Definitions.Def_DetDLP_F9A3_BUnpackTerm
import Definitions.Def_DetDLP_F9A2_BMul
import Theorems.Thm_DetDLP_d3_mul_cost


set_option maxHeartbeats 2500000
namespace DetDLP.ResidualScalarOracle
open Polynomial Finset
noncomputable section

private def lp (m : ℕ) : List ℕ → (ZMod m)[X]
  | [] => 0
  | a :: l => C (a : ZMod m) + X * lp m l

private theorem lp_coeff (m : ℕ) (l : List ℕ) (i : ℕ) :
    (lp m l).coeff i = (l.getD i 0 : ℕ) := by
  induction l generalizing i with
  | nil => simp [lp,List.getD]
  | cons a l ih => cases i <;> simp [lp,coeff_X_mul,ih,List.getD_eq_getElem?_getD]

private theorem lp_degree (m : ℕ) (l : List ℕ) : (lp m l).degree < l.length := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  rw [lp_coeff,List.getD_eq_default _ _ (by exact_mod_cast hi),Nat.cast_zero]

private theorem range_get {α : Type*} (g : ℕ → α) (n i : ℕ) (d : α) (hi : i < n) :
    ((List.range n).map g).getD i d = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp

private theorem cast_step (m a b : ℕ) (hm : 0 < m) :
    ((((a+m)-b%m)%m : ℕ) : ZMod m) = (a : ZMod m) - b := by
  rw [ZMod.natCast_mod,Nat.cast_sub (by have := Nat.mod_lt b hm; omega),Nat.cast_add,
    ZMod.natCast_self,add_zero,ZMod.natCast_mod]

private theorem step_identity (m : ℕ) (hm : 0 < m) (F : (ZMod m)[X]) (n : ℕ) (hn : 0 < n)
    (fc s : List ℕ) (hc : fc.length = n) (hs : s.length = n)
    (hfc : ∀ i < n, (fc.getD i 0 : ZMod m) = F.coeff i)
    (hlt : ∀ i, n < i → F.coeff i = 0) (hmon : F.coeff n = 1) (v : ℕ) :
    lp m (hornerStep m fc s v) = lp m (v :: s) - C (s.getD (n-1) 0 : ZMod m) * F := by
  ext i
  rw [lp_coeff,coeff_sub,coeff_C_mul,lp_coeff]
  by_cases hi : i < n
  · simp only [hornerStep,hc,range_get _ _ _ _ hi,cast_step _ _ _ hm,Nat.cast_mul,hfc i hi]
  · rw [List.getD_eq_default _ _ (by simp [hornerStep,hc]; omega),Nat.cast_zero]
    rcases lt_or_eq_of_le (Nat.le_of_not_gt hi) with h | rfl
    · rw [hlt _ h,List.getD_eq_default _ _ (by simp [hs]; omega)]; simp
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      simp [hmon,List.getD_eq_getElem?_getD]

private theorem power_coeff (f : ℤ[X]) (q : ℕ) (hf : f.Monic) (hd : 0 < f.natDegree)
    (fuel : List ℕ) (k : Fin f.natDegree) :
    let D := List.range f.natDegree; let m := 2^q; let F := f.map (Int.castRingHom (ZMod m))
    (((F9A2.power m D (fCoeffs f q) fuel).getD k 0 : ℕ) : ZMod m) =
      (AdjoinRoot.modByMonicHom (hf.map _) ((AdjoinRoot.root F)^fuel.length)).coeff k.val := by
  let m := 2^q; let F := f.map (Int.castRingHom (ZMod m)); let fc := fCoeffs f q
  let D := List.range f.natDegree
  have hm : 0 < m := pow_pos (by decide) _
  have hc : fc.length = f.natDegree := by simp [fc,fCoeffs]
  have hfc (i : ℕ) (hi : i < f.natDegree) : (fc.getD i 0 : ZMod m) = F.coeff i := by
    rw [List.getD_eq_getElem _ _ (hc ▸ hi)]; simp [fc,fCoeffs,F,m,coeff_map]
  have inv (l : List ℕ) : let v := F9A2.power m D fc l
                          v.length = f.natDegree ∧ AdjoinRoot.mk F (lp m v) = (AdjoinRoot.root F)^l.length := by
    induction l using List.reverseRecOn with
    | nil =>
      have base : lp m (D.map fun k => if k = 0 then 1 else 0) = 1 := by
        ext i; rw [lp_coeff]; by_cases hi : i < f.natDegree
        · rw [range_get _ _ _ _ hi]; by_cases h : i = 0 <;> simp [h,coeff_one]
        · rw [List.getD_eq_default _ _ (by simp [D]; omega)]; simp [coeff_one,show i ≠ 0 by omega]
      simp only [F9A2.power,if_neg hm.ne',List.foldl_nil,List.length_map,List.length_range,D,base,List.length_nil,pow_zero,map_one, true_and]
    | append_singleton l a ih =>
      let v := F9A2.power m D fc l
      have e : F9A2.power m D fc (l++[a]) = hornerStep m fc v 0 := by
        simp [F9A2.power,v,hm.ne',F9A2.step,hornerStep,D,hc,Nat.add_comm]
      rw [e]; refine ⟨by simp [hornerStep,hc],?_⟩
      rw [step_identity m hm F _ hd fc v hc ih.1 hfc (fun i hi => by simp [F,coeff_map,coeff_eq_zero_of_natDegree_lt hi]) (by simp [F,coeff_map,hf.coeff_natDegree])]
      simp only [map_sub,map_mul,AdjoinRoot.mk_self,mul_zero,sub_zero,lp,Nat.cast_zero,map_zero,zero_add,AdjoinRoot.mk_X]
      rw [show AdjoinRoot.mk F (lp m v) = _ from ih.2]; simp [pow_succ,mul_comm]
  obtain ⟨hl,he⟩ := inv fuel
  dsimp only; change _ = (AdjoinRoot.modByMonicHom _ ((AdjoinRoot.root F)^fuel.length)).coeff _
  rw [← he,AdjoinRoot.modByMonicHom_mk]
  have hr : lp m (F9A2.power m D fc fuel) %ₘ F = lp m (F9A2.power m D fc fuel) := by
    rcases subsingleton_or_nontrivial (ZMod m) with ht | ht
    · exact Subsingleton.elim _ _
    · apply (modByMonic_eq_self_iff (hf.map _)).2
      rw [degree_eq_natDegree (hf.map _).ne_zero,hf.natDegree_map]; simpa only [hl] using lp_degree m (F9A2.power m D fc fuel)
  rw [hr,lp_coeff]

private theorem repr_sum {R : Type} [CommRing R] (g : R[X]) (hg : g.Monic) (n : ℕ)
    (hn : g.degree ≤ n) (x : AdjoinRoot g) :
    (∑ i : Fin n, (AdjoinRoot.modByMonicHom hg x).coeff i.val • (AdjoinRoot.root g)^i.val) = x := by
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
  have eqn := congrArg (AdjoinRoot.mk g) (sum_modByMonic_coeff (p:=p) hg hn)
  simp only [← C_mul_X_pow_eq_monomial,map_sum,map_mul,map_pow,AdjoinRoot.mk_X,AdjoinRoot.mk_C] at eqn
  simpa only [AdjoinRoot.modByMonicHom_mk,Algebra.smul_def,AdjoinRoot.algebraMap_eq] using
    eqn.trans (AdjoinRoot.mk_leftInverse hg (AdjoinRoot.mk g p))

private theorem outer_prod {R : Type} [CommRing R] (n : ℕ) (x y : AdjoinRoot ((X:R[X])^n)) (t : Fin n) :
    let canon := AdjoinRoot.modByMonicHom (monic_X_pow (R:=R) n)
    (canon (x*y)).coeff t.val = ∑ r : Fin n, ∑ s : Fin n, if r.val+s.val=t.val then (canon x).coeff r.val*(canon y).coeff s.val else 0 := by
  let g := (X:R[X])^n; let canon := AdjoinRoot.modByMonicHom (monic_X_pow (R:=R) n)
  have rep (v : AdjoinRoot g) : AdjoinRoot.mk g (∑ i : Fin n, monomial i.val ((canon v).coeff i.val)) = v := by
    simpa [← C_mul_X_pow_eq_monomial,Algebra.smul_def,AdjoinRoot.algebraMap_eq] using repr_sum g (monic_X_pow n) n (degree_X_pow_le n) v
  change (canon (x*y)).coeff t.val = _
  conv_lhs => rw [← rep x,← rep y,← map_mul]
  simp only [canon,g,AdjoinRoot.modByMonicHom_mk]
  rw [modByMonic_eq_sub_mul_div,coeff_sub,X_pow_mul,coeff_mul_X_pow',if_neg (by omega : ¬n ≤ t.val),sub_zero]
  simp only [Finset.sum_mul,Finset.mul_sum,finsetSum_coeff,monomial_mul_monomial,coeff_monomial]
  rw [Finset.sum_comm]

private theorem inner_prod (f : ℤ[X]) (q : ℕ) (hf : f.Monic) (x y : U f q) (k : Fin f.natDegree) :
    let F := f.map (Int.castRingHom (ZMod (2^q))); let canon := AdjoinRoot.modByMonicHom (hf.map (Int.castRingHom (ZMod (2^q))))
    (canon (x*y)).coeff k.val = ∑ i : Fin f.natDegree, ∑ j : Fin f.natDegree,
      ((canon x).coeff i.val*(canon y).coeff j.val)*(canon ((AdjoinRoot.root F)^(i.val+j.val))).coeff k.val := by
  dsimp only; let F := f.map (Int.castRingHom (ZMod (2^q)))
  have hF : F.degree ≤ f.natDegree := (degree_map_le).trans degree_le_natDegree
  conv_lhs => rw [← repr_sum F (hf.map _) _ hF x, ← repr_sum F (hf.map _) _ hF y]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,← pow_add,map_sum,map_smul,finsetSum_coeff,coeff_smul,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; dsimp [F]; ring

private theorem range_fn {α : Type} (n : ℕ) (g : ℕ → α) : (List.range n).map g = List.ofFn (fun i : Fin n => g i.val) := by
  apply List.ext_getElem (by simp); intros; simp

private theorem rowsum_fin (n : ℕ) (g : ℕ → ℕ) : F9A2.rowsum (List.range n) g = ∑ i : Fin n, g i.val := by rw [F9A2.rowsum,range_fn,Fin.sum_ofFn]

private theorem flat_get {l d : ℕ} (b : Fin l → Fin d → ℕ) (r : Fin l) (i : Fin d) :
    (F9A2.flatten b).getD (r.val*d+i.val) 0 = b r i := by
  let g := fun j : Fin (l*d) => b (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  have he (s : Fin l) (k : Fin d) (h : s.val*d+k.val < l*d) : g ⟨s.val*d+k.val,h⟩ = b s k := by
    have hidx : (⟨s.val*d+k.val,h⟩ : Fin (l*d)) = finProdFinEquiv (s,k) := by ext; simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
    simp only [g,hidx,Equiv.symm_apply_apply]
  have hflat : F9A2.flatten b = List.ofFn g := by rw [List.ofFn_mul]; unfold F9A2.flatten; simp only [he]
  have hi : r.val*d+i.val < l*d := by have h := Nat.mul_le_mul_right d r.isLt; rw [Nat.succ_mul] at h; have := i.isLt; omega
  rw [hflat,List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn,he]

open OAI.Algorithms.SubexponentialSAT in
private theorem mul_spec (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (hd : 0 < f.natDegree)
    (x y : B f ell q) :
      F9A2.bMulRaw (Encoding.encodeList id [(2^q : ℕ).bits, List.replicate ell true,
        List.replicate f.natDegree true, encodeNatListBin (fCoeffs f q),
        encodeNatListBin (F9A2.flatten (word f ell q hf x)),encodeNatListBin (F9A2.flatten (word f ell q hf y))]) =
      encodeNatListBin (F9A2.flatten (word f ell q hf (x*y))) := by
  classical
  simp only [F9A2.bMulRaw,DetDLP_W1_Queries.first_cons,DetDLP_W1_Queries.more_cons,id_eq,Groundwork.PolyT.bval_bits,w5_M6Sort.decode_encode,List.length_replicate]
  congr 1
  unfold F9A2.table; conv_rhs => unfold F9A2.flatten
  rw [List.flatMap_def,range_fn]; apply congrArg List.flatten; apply congrArg List.ofFn; funext t
  rw [range_fn]; apply congrArg List.ofFn; funext k
  unfold F9A2.coeff
  simp only [List.length_range,rowsum_fin]
  rw [← ZMod.val_natCast]
  apply congrArg ZMod.val
  unfold word
  rw [outer_prod]
  simp only [Nat.cast_sum,map_sum,finsetSum_coeff]
  apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _
  by_cases hrs : r.val+s.val=t.val
  · simp only [hrs,if_true,inner_prod f q hf,Nat.cast_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    simp only [flat_get,Nat.cast_mul,ZMod.natCast_zmod_val,power_coeff f q hf hd,List.length_take,List.length_append,List.length_range]
    rw [min_eq_left (by have := i.isLt; have := j.isLt; omega)]
  · simp [hrs]

end
end DetDLP.ResidualScalarOracle


open Polynomial DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem solution :
    (∀ (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic), 0 < f.natDegree → 0 < ell → 0 < q →
      ∀ x y : ResidualScalarOracle.B f ell q,
        F9A2.bMulRaw (Encoding.encodeList id [(2^q : ℕ).bits, List.replicate ell true,
          List.replicate f.natDegree true,
          encodeNatListBin (List.ofFn fun i : Fin f.natDegree => ((f.coeff i.val : ZMod (2^q)).val)),
          encodeNatListBin (F9A2.flatten (ResidualScalarOracle.word f ell q hf x)),
          encodeNatListBin (F9A2.flatten (ResidualScalarOracle.word f ell q hf y))]) =
        encodeNatListBin (F9A2.flatten (ResidualScalarOracle.word f ell q hf (x*y)))) ∧
    Groundwork.PolyT F9A2.bMulRaw := ⟨fun f l q hf hd _ _ x y => ResidualScalarOracle.mul_spec f l q hf hd x y, DetDLP.d3_mul_cost⟩

