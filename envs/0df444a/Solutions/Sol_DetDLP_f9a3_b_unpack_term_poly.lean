-- Prove2me | solution 1 for DetDLP.f9a3_b_unpack_term_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:23:53.439206+00:00
-- url     : https://prove2.me/submissions/2b52532a-da95-44a2-a22c-59c227d2db1e

import Definitions.Def_DetDLP_F9A3_BUnpackTerm
import Theorems.Thm_DetDLP_d3_unpack_cost

import Theorems.Thm_Groundwork_Unary_of_length

set_option maxHeartbeats 2500000
namespace DetDLP.ResidualScalarOracle
open Polynomial Finset
noncomputable section

theorem sum_unpackTerm (f : ℤ[X]) (ell q : ℕ) (G : BipartiteMultigraph) (h J : ℕ)
    (d : (Fin G.nV → Fin J) → Fin (spacing f G * ell) → ℕ) :
    ∑ a, unpackTerm f ell q G h a (d a) = unpack f ell q G h J d := by
  classical
  unfold unpackTerm unpack
  dsimp only
  rw [← map_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← map_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]


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

private theorem row_spec (f : ℤ[X]) (q : ℕ) (hf : f.Monic) (hk : 0 < f.natDegree) (row : List ℕ) :
    let s := reduceRow (2^q) (fCoeffs f q) row
    let F := f.map (Int.castRingHom (ZMod (2^q)))
    s.length = f.natDegree ∧ (∀ t ∈ s, t < 2^q) ∧
      AdjoinRoot.mk F (lp (2^q) s) = AdjoinRoot.mk F (lp (2^q) row) := by
  dsimp only
  let m := 2^q
  have hm : 0 < m := pow_pos (by decide) _
  let fc := fCoeffs f q
  have hc : fc.length = f.natDegree := by simp [fc,fCoeffs]
  let F := f.map (Int.castRingHom (ZMod m))
  have hfc (i : ℕ) (hi : i < f.natDegree) : (fc.getD i 0 : ZMod m) = F.coeff i := by
    rw [List.getD_eq_getElem _ _ (hc ▸ hi)]
    simp [fc, fCoeffs,F,m,coeff_map]
  change (reduceRow m fc row).length = _ ∧ (∀ t ∈ reduceRow m fc row, t < m) ∧
    AdjoinRoot.mk F (lp m (reduceRow m fc row)) = AdjoinRoot.mk F (lp m row)
  induction row with
  | nil =>
    have hzero : lp m (fc.map (fun _ => 0)) = 0 := by
      generalize fc = c; induction c <;> simp_all [lp]
    refine ⟨by simp [reduceRow,hc], by simp [reduceRow]; grind, ?_⟩
    change AdjoinRoot.mk F (lp m (fc.map fun _ => 0)) = AdjoinRoot.mk F 0
    rw [hzero]
  | cons v row ih =>
    let s := reduceRow m fc row
    have heq : reduceRow m fc (v::row) = hornerStep m fc s v := by
      simp [reduceRow,s,List.foldl_append,max_eq_right (show 1 ≤ m by omega)]
    rw [heq]
    refine ⟨by simp [hornerStep,hc], ?_, ?_⟩
    · intro t ht; obtain ⟨_,_,rfl⟩ := List.mem_map.mp ht; exact Nat.mod_lt _ hm
    · rw [step_identity m hm F _ hk fc s hc ih.1 hfc (fun i hi => by simp [F,coeff_map,coeff_eq_zero_of_natDegree_lt hi])
        (by simp [F,coeff_map,hf.coeff_natDegree]) v]
      simp only [map_sub,map_mul,AdjoinRoot.mk_self,mul_zero,sub_zero,lp,map_add,ih.2.2,s]

private theorem row_words (f : ℤ[X]) (q : ℕ) (hf : f.Monic) (hk : 0 < f.natDegree) (row : List ℕ) :
    reduceRow (2^q) (fCoeffs f q) row = List.ofFn fun i : Fin f.natDegree =>
      ((AdjoinRoot.modByMonicHom (hf.map _) (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2^q)))) (lp (2^q) row))).coeff i.val).val := by
  let m := 2^q
  let F := f.map (Int.castRingHom (ZMod m))
  let s := reduceRow m (fCoeffs f q) row
  obtain ⟨hs,hb,he⟩ := row_spec f q hf hk row
  change s.length = _ at hs
  change ∀ t ∈ s, t < m at hb
  change AdjoinRoot.mk F (lp m s) = _ at he
  change s = List.ofFn fun i : Fin f.natDegree => ((AdjoinRoot.modByMonicHom (hf.map _) (AdjoinRoot.mk F (lp m row))).coeff i.val).val
  rw [← he,AdjoinRoot.modByMonicHom_mk]
  have hr : lp m s %ₘ F = lp m s := by
    cases subsingleton_or_nontrivial (ZMod m) with
    | inl h => exact Subsingleton.elim _ _
    | inr h =>
      apply (modByMonic_eq_self_iff (hf.map _)).2
      rw [degree_eq_natDegree (hf.map _).ne_zero,hf.natDegree_map]; simpa only [hs] using lp_degree m s
  rw [hr]
  apply List.ext_getElem (by simp [hs]); intro i hi hi'
  simp only [List.getElem_ofFn,lp_coeff,List.getD_eq_getElem _ _ hi,ZMod.val_natCast]
  exact (Nat.mod_eq_of_lt (hb _ (List.getElem_mem ..))).symm

private theorem lp_range (m k : ℕ) (v : ℕ → ℕ) : lp m ((List.range k).map v) =
    ∑ i : Fin k, monomial i.val (v i.val : ZMod m) := by
  classical
  rw [← ofFn_eq_sum_monomial]
  ext i
  rw [lp_coeff]
  by_cases hi : i < k
  · simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega),ofFn_coeff_eq_zero_of_ge _ (by omega)]; simp

private theorem outer_coeff {R : Type} [CommRing R] (k : ℕ) (v : Fin k → R) (j : Fin k) :
    (AdjoinRoot.modByMonicHom (monic_X_pow k) (AdjoinRoot.mk (X^k) (∑ t : Fin k, monomial t.val (v t)))).coeff j.val = v j := by
  classical
  nontriviality R
  rw [← ofFn_eq_sum_monomial,AdjoinRoot.modByMonicHom_mk,(modByMonic_eq_self_iff (monic_X_pow k)).2 (by simpa using ofFn_degree_lt v)]
  exact ofFn_coeff_eq_val_of_lt _ j.isLt

private theorem range_as_ofFn {α : Type} (n : ℕ) (g : ℕ → α) : (List.range n).map g = List.ofFn (fun i : Fin n => g i.val) := by
  apply List.ext_getElem (by simp); intros; simp

open OAI.Algorithms.SubexponentialSAT in
theorem bUnpackTermRaw_correct (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (hk : 0 < f.natDegree)
    (G : BipartiteMultigraph) (h J : ℕ) (a : Fin G.nV → Fin J) (d : Fin (spacing f G * ell) → ℕ) :
    bUnpackTermRaw (Encoding.encodeList id [(2^q : ℕ).bits,
         (2^(h * ∑ v, (a v).val) % 2^q : ℕ).bits, List.replicate ell true,
         List.replicate (spacing f G) true, encodeNatListBin (fCoeffs f q),
         encodeNatListBin (List.ofFn d)]) =
       encodeNatListBin (List.ofFn fun idx : Fin (ell * f.natDegree) =>
         word f ell q hf (unpackTerm f ell q G h a d)
           (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2) := by
  classical
  simp only [bUnpackTermRaw,DetDLP_W1_Queries.first_cons,DetDLP_W1_Queries.more_cons,id_eq,
    Groundwork.PolyT.bval_bits,w5_M6Sort.decode_encode,unpackRows,List.length_replicate]
  congr 1
  rw [List.flatMap_def,range_as_ofFn]; conv_rhs => rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  rw [row_words f q hf hk]
  apply congrArg List.ofFn
  funext i
  have hidx : (⟨j.val * f.natDegree + i.val, by have := (finProdFinEquiv (j,i)).isLt; simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm] using this⟩ : Fin (ell*f.natDegree)) = finProdFinEquiv (j,i) := by ext; simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [hidx,Equiv.symm_apply_apply]
  unfold word unpackTerm
  simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,Polynomial.map_sum,Polynomial.map_monomial,Int.coe_castRingHom,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast]
  rw [outer_coeff,lp_range]
  congr 5
  funext u
  congr 1
  have hi' : u.val + spacing f G * j.val < spacing f G * ell := by
    have H := Nat.mul_le_mul_left (spacing f G) j.isLt
    rw [Nat.mul_succ] at H; have := u.isLt; omega
  simp [hi',ZMod.natCast_mod]

end
end DetDLP.ResidualScalarOracle

open Polynomial Finset DetDLP DetDLP.ResidualScalarOracle OAI.Algorithms.SubexponentialSAT
theorem solution :
    (∀ (f : ℤ[X]) (ell q : ℕ) (G : BipartiteMultigraph) (h J : ℕ)
       (d : (Fin G.nV → Fin J) → Fin (spacing f G * ell) → ℕ),
       ∑ a, unpackTerm f ell q G h a (d a) = unpack f ell q G h J d) ∧
    (∀ (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (_ : 0 < f.natDegree)
       (G : BipartiteMultigraph) (h J : ℕ) (a : Fin G.nV → Fin J)
       (d_a : Fin (spacing f G * ell) → ℕ),
       bUnpackTermRaw (Encoding.encodeList id [(2^q : ℕ).bits,
         (2^(h * ∑ v, (a v).val) % 2^q : ℕ).bits, List.replicate ell true,
         List.replicate (spacing f G) true, encodeNatListBin (fCoeffs f q),
         encodeNatListBin (List.ofFn d_a)]) =
       encodeNatListBin (List.ofFn fun idx : Fin (ell * f.natDegree) =>
         word f ell q hf (unpackTerm f ell q G h a d_a)
           (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2)) ∧
    Groundwork.PolyT bUnpackTermRaw := ⟨sum_unpackTerm, bUnpackTermRaw_correct, DetDLP.d3_unpack_cost⟩
