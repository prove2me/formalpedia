-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:17:28.890281+00:00
-- url     : https://prove2.me/submissions/a06e5e6c-fce6-4799-8760-02cc83be3b5f

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData

set_option autoImplicit false
noncomputable section

section


open Classical Finset Polynomial
open FasterDistributedMatching.ApproximateMatching

namespace BlockColorProof

variable {F : Type} [Field F] [Fintype F]

def poly {d : ℕ} (a : Fin d → F) : F[X] :=
  ∑ i : Fin d, monomial i.val (a i)

lemma poly_coeff {d : ℕ} (a : Fin d → F) (i : Fin d) : (poly a).coeff i.val = a i := by
  simp [poly,Polynomial.coeff_monomial,Fin.val_inj]

lemma poly_injective (d : ℕ) : Function.Injective (@poly F _ d) := by
  intro a b h
  funext i
  have hh := congrArg (fun p : F[X] => p.coeff i.val) h
  simpa only [poly_coeff] using hh

lemma degree_poly {d : ℕ} (a : Fin d → F) : (poly a).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le (a i)).trans (Nat.le_of_lt i.isLt)

lemma collisions {d : ℕ} (a b : Fin d → F) (hab : a ≠ b) :
    (univ.filter (fun x : F => (poly a).eval x = (poly b).eval x)).card ≤ d := by
  have hp : poly a - poly b ≠ 0 := sub_ne_zero.mpr (fun h => hab (poly_injective d h))
  have hsub : (univ.filter (fun x : F => (poly a).eval x = (poly b).eval x)) ⊆
      (poly a-poly b).roots.toFinset := by
    intro x hx
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hp).mpr
    change (poly a-poly b).eval x = 0
    rw [Polynomial.eval_sub,sub_eq_zero]
    exact (mem_filter.mp hx).2
  exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans ((Polynomial.natDegree_sub_le _ _).trans
      (max_le (degree_poly a) (degree_poly b)))))

lemma separating_point {d k D : ℕ} (enc : Fin k ↪ (Fin d → F))
    (hsize : D*d < Fintype.card F) (c : Fin k) (ns : Finset (Fin k))
    (hns : ns.card ≤ D) (hself : c ∉ ns) :
    ∃ x : F, ∀ b ∈ ns, (poly (enc c)).eval x ≠ (poly (enc b)).eval x := by
  let bad := ns.biUnion fun b => univ.filter fun x : F => (poly (enc c)).eval x = (poly (enc b)).eval x
  have hbad : bad.card ≤ D*d := by
    calc
      _ ≤ ∑ b ∈ ns, (univ.filter fun x : F => (poly (enc c)).eval x = (poly (enc b)).eval x).card :=
        card_biUnion_le
      _ ≤ ∑ _ ∈ ns, d := by
        apply sum_le_sum
        intro b hb
        exact collisions (enc c) (enc b) (fun h => hself (enc.injective h ▸ hb))
      _ ≤ D*d := by simpa using Nat.mul_le_mul_right d hns
  have hproper : bad ≠ univ := by
    intro h
    rw [h,card_univ] at hbad
    omega
  have hex : ∃ x : F, x ∉ bad := by
    by_contra h
    apply hproper
    ext x
    simp only [mem_univ,iff_true]
    by_contra hx
    exact h ⟨x,hx⟩
  obtain ⟨x,hx⟩ := hex
  refine ⟨x,?_⟩
  intro b hb heq
  exact hx (mem_biUnion.mpr ⟨b,hb,mem_filter.mpr ⟨mem_univ x,heq⟩⟩)

def nextPalette (D k : ℕ) : ℕ := 4*(D*Nat.clog 2 k+1)^2

lemma separating_family (D k : ℕ) :
    ∃ S : Fin k → Finset (Fin (nextPalette D k)),
      ∀ (c : Fin k) (ns : Finset (Fin k)), ns.card ≤ D → c ∉ ns →
        ∃ i ∈ S c, ∀ b ∈ ns, i ∉ S b := by
  let d := Nat.clog 2 k
  obtain ⟨q,hprime,hq,hqu⟩ := Nat.exists_prime_lt_and_le_two_mul (D*d+1) (by omega)
  letI : Fact q.Prime := ⟨hprime⟩
  have hq2 : 2 ≤ q := hprime.two_le
  have hcard : Fintype.card (Fin k) ≤ Fintype.card (Fin d → ZMod q) := by
    simp only [Fintype.card_fin,Fintype.card_fun,ZMod.card]
    exact (Nat.le_pow_clog (by decide) k).trans (Nat.pow_le_pow_left hq2 d)
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hcard2 : Fintype.card (ZMod q × ZMod q) ≤ nextPalette D k := by
    simp only [Fintype.card_prod,ZMod.card]
    unfold nextPalette
    change q*q ≤ 4*(D*d+1)^2
    nlinarith
  let E : (ZMod q × ZMod q) ↪ Fin (nextPalette D k) :=
    (Fintype.equivFin (ZMod q × ZMod q)).toEmbedding.trans (Fin.castLEEmb hcard2)
  let S : Fin k → Finset (Fin (nextPalette D k)) := fun c =>
    univ.image fun x : ZMod q => E (x,(poly (enc c)).eval x)
  refine ⟨S,?_⟩
  intro c ns hns hc
  have hsize : D*d < Fintype.card (ZMod q) := by simpa using (by omega : D*d < q)
  obtain ⟨x,hx⟩ := separating_point enc hsize c ns hns hc
  refine ⟨E (x,(poly (enc c)).eval x),mem_image.mpr ⟨x,mem_univ x,rfl⟩,?_⟩
  intro b hb hmem
  obtain ⟨y,_,hy⟩ := mem_image.mp hmem
  have heq := E.injective hy
  have hyx : y = x := congrArg Prod.fst heq
  have hev := congrArg Prod.snd heq
  apply hx b hb
  simpa only [hyx] using hev.symm

def family (D k : ℕ) : Fin k → Finset (Fin (nextPalette D k)) :=
  (separating_family D k).choose

lemma family_spec (D k : ℕ) (c : Fin k) (ns : Finset (Fin k))
    (hns : ns.card ≤ D) (hc : c ∉ ns) :
    ∃ i ∈ family D k c, ∀ b ∈ ns, i ∉ family D k b :=
  (separating_family D k).choose_spec c ns hns hc

def finiteNeighbors (k : ℕ) (ns : Finset ℕ) (hns : ∀ b ∈ ns, b < k) : Finset (Fin k) :=
  ns.attach.image fun b => ⟨b.val,hns b.val b.property⟩

lemma finiteNeighbors_card (k : ℕ) (ns : Finset ℕ) (hns : ∀ b ∈ ns, b < k) :
    (finiteNeighbors k ns hns).card ≤ ns.card := by
  exact (card_image_le).trans_eq (card_attach)

lemma finiteNeighbors_mem (k : ℕ) (ns : Finset ℕ) (hns : ∀ b ∈ ns, b < k) (b : Fin k) :
    b ∈ finiteNeighbors k ns hns ↔ b.val ∈ ns := by
  constructor
  · intro hb
    obtain ⟨c,hc,heq⟩ := mem_image.mp hb
    exact (congrArg Fin.val heq) ▸ c.property
  · intro hb
    exact mem_image.mpr ⟨⟨b.val,hb⟩,mem_attach _ _,Fin.ext rfl⟩

def localReduce (D k c : ℕ) (ns : Finset ℕ) : ℕ :=
  if h : c < k ∧ ns.card ≤ D ∧ c ∉ ns ∧ ∀ b ∈ ns, b < k then
    let nsFin := finiteNeighbors k ns h.2.2.2
    let hc : (⟨c,h.1⟩ : Fin k) ∉ nsFin := by
      intro hm
      exact h.2.2.1 ((finiteNeighbors_mem k ns h.2.2.2 _).mp hm)
    ((family_spec D k ⟨c,h.1⟩ nsFin
      ((finiteNeighbors_card k ns h.2.2.2).trans h.2.1) hc).choose).val
  else 0

lemma localReduce_spec (D k c : ℕ) (ns : Finset ℕ)
    (h : c < k ∧ ns.card ≤ D ∧ c ∉ ns ∧ ∀ b ∈ ns, b < k) :
    ∃ i : Fin (nextPalette D k), localReduce D k c ns = i.val ∧
      i ∈ family D k ⟨c,h.1⟩ ∧ ∀ b (hb : b ∈ ns), i ∉ family D k ⟨b,h.2.2.2 b hb⟩ := by
  let nsFin := finiteNeighbors k ns h.2.2.2
  have hcard : nsFin.card ≤ D := (finiteNeighbors_card k ns h.2.2.2).trans h.2.1
  have hc : (⟨c,h.1⟩ : Fin k) ∉ nsFin := by
    intro hm
    exact h.2.2.1 ((finiteNeighbors_mem k ns h.2.2.2 _).mp hm)
  have hex := family_spec D k ⟨c,h.1⟩ nsFin hcard hc
  refine ⟨hex.choose,?_,hex.choose_spec.1,?_⟩
  · unfold localReduce
    rw [dif_pos h]
  · intro b hb
    exact hex.choose_spec.2 _ ((finiteNeighbors_mem k ns h.2.2.2 _).mpr hb)

lemma localReduce_lt (D k c : ℕ) (ns : Finset ℕ) : localReduce D k c ns < nextPalette D k := by
  unfold localReduce
  split_ifs
  · exact Fin.isLt _
  · unfold nextPalette
    positivity

lemma localReduce_distinct (D k c b : ℕ) (ns ms : Finset ℕ)
    (hc : c < k ∧ ns.card ≤ D ∧ c ∉ ns ∧ ∀ j ∈ ns, j < k)
    (hb : b < k ∧ ms.card ≤ D ∧ b ∉ ms ∧ ∀ j ∈ ms, j < k)
    (hbn : b ∈ ns) : localReduce D k c ns ≠ localReduce D k b ms := by
  obtain ⟨i,hi,hif,hin⟩ := localReduce_spec D k c ns hc
  obtain ⟨j,hj,hjf,hjn⟩ := localReduce_spec D k b ms hb
  intro heq
  have hij : i = j := Fin.ext (hi.symm.trans (heq.trans hj))
  exact hin b hbn (hij ▸ hjf)

lemma local_reduce_proper {V : Type} [Fintype V] (H : SimpleGraph V)
    (D k : ℕ) (col : V → ℕ) (hcol : Proper H k col)
    (hD : ∀ v, H.degree v ≤ D) :
    Proper H (nextPalette D k)
      (fun v => localReduce D k (col v) ((H.neighborFinset v).image col)) := by
  have hgood (v : V) : col v < k ∧ ((H.neighborFinset v).image col).card ≤ D ∧
      col v ∉ (H.neighborFinset v).image col ∧
      ∀ j ∈ (H.neighborFinset v).image col, j < k := by
    refine ⟨hcol.1 v,(card_image_le).trans ?_,?_,?_⟩
    · simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hD v
    · intro h
      obtain ⟨w,hw,heq⟩ := mem_image.mp h
      exact hcol.2 v w (by simpa using hw) heq.symm
    · intro j hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hj
      exact hcol.1 w
  refine ⟨fun v => localReduce_lt D k _ _,?_⟩
  intro v w hvw
  exact localReduce_distinct D k (col v) (col w) _ _ (hgood v) (hgood w)
    (mem_image.mpr ⟨w,by simpa using hvw,rfl⟩)

lemma nextPalette_bound (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    nextPalette D k ≤ 16 * D^2 * (Nat.clog 2 k)^2 := by
  have hd : 1 ≤ Nat.clog 2 k := Nat.clog_pos (by decide) (by omega)
  unfold nextPalette
  have hm : 1 ≤ D * Nat.clog 2 k := by nlinarith
  nlinarith

lemma clog_nextPalette (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    Nat.clog 2 (nextPalette D k) ≤ 4+2*Nat.clog 2 D+2*Nat.clog 2 (Nat.clog 2 k) := by
  apply Nat.clog_le_of_le_pow
  calc
    _ ≤ 16 * D^2 * (Nat.clog 2 k)^2 := nextPalette_bound D k hD hk
    _ ≤ 16 * (2^Nat.clog 2 D)^2 * (2^Nat.clog 2 (Nat.clog 2 k))^2 := by
      gcongr
      · exact Nat.le_pow_clog (by decide) _
      · exact Nat.le_pow_clog (by decide) _
    _ = _ := by
      simp only [pow_add,← pow_mul,Nat.mul_comm]
      norm_num

lemma polynomial_le_exponential (l : ℕ) (hl : 64 ≤ l) :
    (32*l)^4 ≤ 2^(l-1) := by
  induction l,hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    have hratio : (32*(l+1))^4 ≤ 2*(32*l)^4 := by
      have hsmall : 8*(l+1) ≤ 9*l := by omega
      have hp := Nat.pow_le_pow_left hsmall 4
      simp only [mul_pow] at hp
      norm_num at hp
      have hp' : 4096*(l+1)^4 ≤ 8192*l^4 := hp.trans
        (Nat.mul_le_mul_right _ (by decide : 6561 ≤ 8192))
      have hh : (l+1)^4 ≤ 2*l^4 := by omega
      calc
        _ = 32^4 * (l+1)^4 := by ring
        _ ≤ 32^4 * (2*l^4) := Nat.mul_le_mul_left _ hh
        _ = _ := by ring
    calc
      _ ≤ 2*(32*l)^4 := hratio
      _ ≤ 2*2^(l-1) := Nat.mul_le_mul_left 2 ih
      _ = _ := by rw [show l+1-1 = (l-1)+1 by omega,pow_succ]; omega

lemma clog_fourth_bound (d : ℕ) (hd : 2^64 ≤ d) :
    (32*Nat.clog 2 d)^4 ≤ d := by
  have hlog : 64 ≤ Nat.clog 2 d := by
    have ht : 2^63 < d := by omega
    have hh := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr ht
    omega
  have hp := polynomial_le_exponential (Nat.clog 2 d) hlog
  have hd1 : 1 < d := by omega
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hd1
  exact hp.trans (by simpa only [Nat.pred_eq_sub_one] using hpred.le)

lemma two_step_palette (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    nextPalette D (nextPalette D k) ≤ max (D^64) (Nat.clog 2 k) := by
  let d := Nat.clog 2 k
  let a := Nat.clog 2 D
  let b := Nat.clog 2 d
  have ha : a ≤ D := Nat.clog_le_of_le_pow (show D ≤ 2^D from (Nat.lt_pow_self (by decide : 1 < 2)).le)
  have hd : 1 ≤ d := Nat.clog_pos (by decide) (by omega)
  have hlog : Nat.clog 2 (nextPalette D k) ≤ 4+2*a+2*b := clog_nextPalette D k hD hk
  have hnext : nextPalette D (nextPalette D k) ≤ 4*(D*(4+2*a+2*b)+1)^2 := by
    unfold nextPalette
    exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.mul_le_mul_left D hlog) 1) 2)
  by_cases hsmall : d ≤ D^64
  · have hb : b ≤ 64*a := by
      apply Nat.clog_le_of_le_pow
      calc
        d ≤ D^64 := hsmall
        _ ≤ (2^a)^64 := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) D) 64
        _ = _ := by rw [← pow_mul,Nat.mul_comm]
    have hinner : D*(4+2*a+2*b)+1 ≤ 135*D^2 := by nlinarith
    have hbound : nextPalette D (nextPalette D k) ≤ 72900*D^4 := by
      calc
        _ ≤ 4*(D*(4+2*a+2*b)+1)^2 := hnext
        _ ≤ 4*(135*D^2)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hinner 2)
        _ = _ := by ring
    have hconst : 72900 ≤ D^60 :=
      (by norm_num : 72900 ≤ 2^60).trans (Nat.pow_le_pow_left hD 60)
    apply le_trans _ (le_max_left _ _)
    calc
      _ ≤ 72900*D^4 := hbound
      _ ≤ D^60*D^4 := Nat.mul_le_mul_right _ hconst
      _ = _ := by rw [← pow_add]
  · have hlarge : 2^64 ≤ d := (Nat.pow_le_pow_left hD 64).trans (by omega)
    have hfour : (32*b)^4 ≤ d := clog_fourth_bound d hlarge
    have hD4 : D^4 ≤ d :=
      (Nat.pow_le_pow_right (by omega : 0 < D) (by decide : 4 ≤ 64)).trans (by omega)
    have hDpow : D ≤ D^4 := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < D) (by decide : 1 ≤ 4)
    have hDle : D ≤ d := hDpow.trans hD4
    have hab : a ≤ b := Nat.clog_mono_right 2 hDle
    have hb : 1 ≤ b := Nat.clog_pos (by decide) (by omega)
    have hinner : D*(4+2*a+2*b)+1 ≤ 16*D*b := by nlinarith
    have hbound : nextPalette D (nextPalette D k) ≤ 1024*D^2*b^2 := by
      calc
        _ ≤ 4*(D*(4+2*a+2*b)+1)^2 := hnext
        _ ≤ 4*(16*D*b)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hinner 2)
        _ = _ := by ring
    have hsquare : (1024*D^2*b^2)^2 ≤ d^2 := by
      calc
        _ = D^4*(32*b)^4 := by ring
        _ ≤ D^4*d := Nat.mul_le_mul_left _ hfour
        _ ≤ d*d := Nat.mul_le_mul_right d hD4
        _ = _ := by ring
    have hlast : 1024*D^2*b^2 ≤ d := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsquare
    exact (hbound.trans hlast).trans (le_max_right _ _)

lemma nextPalette_mono (D : ℕ) : Monotone (nextPalette D) := by
  intro a b hab
  unfold nextPalette
  gcongr

lemma nextPalette_threshold (D : ℕ) (hD : 2 ≤ D) : nextPalette D (D^64) ≤ D^64 := by
  have hclog : Nat.clog 2 (D^64) ≤ 64*D := by
    apply Nat.clog_le_of_le_pow
    calc
      D^64 ≤ (2^D)^64 := Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1 < 2)).le 64
      _ = _ := by rw [← pow_mul,Nat.mul_comm]
  have hinner : D*Nat.clog 2 (D^64)+1 ≤ 65*D^2 := by nlinarith
  have hconst : 16900 ≤ D^60 :=
    (by norm_num : 16900 ≤ 2^60).trans (Nat.pow_le_pow_left hD 60)
  calc
    _ = 4*(D*Nat.clog 2 (D^64)+1)^2 := rfl
    _ ≤ 4*(65*D^2)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hinner 2)
    _ = 16900*D^4 := by ring
    _ ≤ D^60*D^4 := Nat.mul_le_mul_right _ hconst
    _ = _ := by rw [← pow_add]

def paddedNext (D k : ℕ) : ℕ := max (D^64) (nextPalette D k)

lemma paddedNext_mono (D : ℕ) : Monotone (paddedNext D) :=
  fun _ _ h => max_le_max_left _ (nextPalette_mono D h)

lemma paddedNext_twice (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    paddedNext D (paddedNext D k) ≤ max (D^64) (Nat.clog 2 k) := by
  unfold paddedNext
  apply max_le (le_max_left _ _)
  by_cases h : nextPalette D k ≤ D^64
  · rw [max_eq_left h]
    exact (nextPalette_threshold D hD).trans (le_max_left _ _)
  · rw [max_eq_right (by omega : D^64 ≤ nextPalette D k)]
    exact two_step_palette D k hD hk

lemma clog_lt_self (n : ℕ) (hn : 2 ≤ n) : Nat.clog 2 n < n := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr ?_ |>.trans_lt (Nat.pred_lt (by omega))
  have hpow : n ≤ 2^(n-1) := by
    induction n,hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [show n+1-1 = (n-1)+1 by omega,pow_succ]
      omega
  simpa only [Nat.pred_eq_sub_one] using hpow

def height (n : ℕ) : ℕ := if h : n ≤ 1 then 0 else 1+height (Nat.clog 2 n)
termination_by n
 decreasing_by exact clog_lt_self n (by omega)

lemma height_le_self (n : ℕ) : height n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [height]
    split_ifs with hn
    · omega
    · have hlt := clog_lt_self n (by omega)
      have hh := ih _ hlt
      omega

lemma height_mono : Monotone height := by
  intro a b hab
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases ha : a ≤ 1
    · rw [height,dif_pos ha]; exact Nat.zero_le _
    · have hb : ¬ b ≤ 1 := by omega
      have hea : height a = 1+height (Nat.clog 2 a) := by rw [height,dif_neg ha]
      have heb : height b = 1+height (Nat.clog 2 b) := by rw [height,dif_neg hb]
      rw [hea,heb]
      have hlt := clog_lt_self b (by omega)
      exact Nat.add_le_add_left (ih _ hlt (Nat.clog_mono_right 2 hab)) 1

lemma height_pow_two (n : ℕ) (hn : 1 ≤ n) : height (2^n) = 1+height n := by
  rw [height,dif_neg (by
    have h : 2 ≤ 2^n := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega),Nat.clog_pow 2 n (by decide)]

lemma square_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n^2 ≤ 2^n := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    have hh : (n+1)^2 ≤ 2*n^2 := by nlinarith
    exact hh.trans (Nat.mul_le_mul_left 2 ih |>.trans_eq (by ring))

def tower (n : ℕ) : ℕ → ℕ
  | 0 => n
  | t+1 => 2^(tower n t)

lemma tower_ge (n t : ℕ) : n ≤ tower n t := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih.trans (Nat.lt_pow_self (by decide : 1 < 2)).le

lemma height_tower (n t : ℕ) (hn : 1 ≤ n) : height (tower n t) = t+height n := by
  induction t with
  | zero => simp [tower]
  | succ t ih =>
    rw [tower,height_pow_two _ (hn.trans (tower_ge n t)),ih]
    omega

lemma power_le_tower (n B : ℕ) (hn : 2 ≤ n) : n^B ≤ tower n B := by
  induction B with
  | zero => simpa [tower] using (show 1 ≤ n by omega)
  | succ B ih =>
    cases B with
    | zero => simpa [tower] using (Nat.lt_pow_self (by decide : 1 < 2) : n < 2^n).le
    | succ B =>
      have ht : 4 ≤ tower n (B+1) := by
        change 4 ≤ 2^(tower n B)
        exact (by norm_num : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (hn.trans (tower_ge n B)))
      calc
        n^(B+1+1) = n^(B+1)*n := by rw [pow_succ]
        _ ≤ (tower n (B+1))^2 := by
          simpa only [pow_two] using Nat.mul_le_mul ih (tower_ge n (B+1))
        _ ≤ 2^(tower n (B+1)) := square_le_two_pow _ ht
        _ = _ := rfl

lemma height_power (n B : ℕ) (hn : 2 ≤ n) : height (n^B) ≤ height n+B := by
  have h := height_mono (power_le_tower n B hn)
  rw [height_tower n B (by omega)] at h
  omega

lemma clog_ceil_log (x : ℝ) (hx : 0 < x) :
    Nat.clog 2 ⌈x⌉₊ = ⌈logTwo x⌉₊ := by
  apply eq_of_forall_ge_iff
  intro j
  rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2),Nat.ceil_le,Nat.ceil_le]
  rw [Nat.cast_pow,Nat.cast_ofNat]
  have h : logTwo x ≤ (j : ℝ) ↔ x ≤ (2 : ℝ)^(j : ℝ) :=
    Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx
  simpa only [Real.rpow_natCast] using h.symm

lemma iterLog_height (fuel : ℕ) (x : ℝ) (hx : 0 < x) (hf : ⌈x⌉₊ ≤ fuel) :
    iterLog fuel x = height ⌈x⌉₊ := by
  induction fuel generalizing x with
  | zero =>
    have hh : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
    omega
  | succ fuel ih =>
    by_cases hx1 : x ≤ 1
    · have hn : ⌈x⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using hx1)
      rw [iterLog,if_pos hx1,height,dif_pos hn]
    · have hn : ¬ ⌈x⌉₊ ≤ 1 := by
        intro h
        have hh := Nat.ceil_le.mp h
        norm_num at hh
        exact hx1 hh
      have hlog : 0 < logTwo x := Real.logb_pos (by norm_num) (by linarith)
      have hceil := clog_ceil_log x hx
      have hlt := clog_lt_self ⌈x⌉₊ (by omega)
      have hnext : ⌈logTwo x⌉₊ ≤ fuel := by omega
      rw [iterLog,if_neg hx1,ih _ hlog hnext]
      conv_rhs => rw [height,dif_neg hn]
      rw [← hceil]

lemma height_nat_iterLog (n : ℕ) : height n = iterLog n n := by
  by_cases hn : n = 0
  · subst n
    rw [height,dif_pos (by decide)]
    rfl
  · have h := iterLog_height n (n : ℝ) (by exact_mod_cast Nat.pos_of_ne_zero hn) (by simp)
    simpa using h.symm

lemma height_max (a b : ℕ) : height (max a b) = max (height a) (height b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,max_eq_right (height_mono h)]
  · rw [max_eq_left h,max_eq_left (height_mono h)]

lemma height_two : height 2 = 1 := by
  rw [height,dif_neg (by decide)]
  change 1+height 1 = 1
  rw [height,dif_pos (by decide)]

lemma height_max_two (n : ℕ) : height (max 2 n) = logStar n := by
  rw [height_max,height_two,height_nat_iterLog]
  rfl

lemma height_ID_bound (n B : ℕ) : height ((max 2 n)^B) ≤ (B+1)*logStar n := by
  have hh := height_power (max 2 n) B (le_max_left _ _)
  rw [height_max_two] at hh
  have hpos : 1 ≤ logStar n := le_max_left _ _
  nlinarith

lemma palette_iterations (D k : ℕ) (hD : 2 ≤ D) :
    (paddedNext D)^[2*height k] (max (D^64) k) ≤ D^64 := by
  have hfix : paddedNext D (D^64) = D^64 := by
    exact max_eq_left (nextPalette_threshold D hD)
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k ≤ D^64
    · rw [max_eq_left hk,Function.iterate_fixed hfix]
    · have hk2 : 2 ≤ k := by
        have hsmall : 2 ≤ D^64 := by
          exact (by norm_num : 2 ≤ 2^64).trans (Nat.pow_le_pow_left hD 64)
        omega
      have hh : height k = 1+height (Nat.clog 2 k) := by
        rw [height,dif_neg (by omega)]
      rw [hh,show 2*(1+height (Nat.clog 2 k)) = 2*height (Nat.clog 2 k)+2 by omega,
        Function.iterate_add_apply,max_eq_right (by omega : D^64 ≤ k)]
      have htwo : (paddedNext D)^[2] k ≤ max (D^64) (Nat.clog 2 k) := paddedNext_twice D k hD hk2
      apply le_trans ((paddedNext_mono D).iterate (2*height (Nat.clog 2 k)) htwo)
      exact ih _ (clog_lt_self k hk2)

structure ColorParameters where
  degree : ℕ
  palette : ℕ

structure ColorState where
  degree : ℕ
  palette : ℕ
  color : ℕ

def colorProgram : Deterministic ColorParameters ℕ ℕ where
  program := {
    State := ColorState
    Msg := ℕ
    rounds := fun k => 2*height k.palette
    init := fun k _ col _ => ⟨k.degree,max (k.degree^64) k.palette,col⟩
    send := ColorState.color
    step := fun s msgs => ⟨s.degree,paddedNext s.degree s.palette,
      localReduce s.degree s.palette s.color msgs.toFinset⟩
    out := ColorState.color }
  tape_independent := by intros; rfl

lemma colorProgram_invariant {V : Type} [Fintype V] (H : SimpleGraph V)
    (k : ColorParameters) (ids initial : V → ℕ) (hinit : Proper H k.palette initial) (hD : ∀ v, H.degree v ≤ k.degree) (t : ℕ) :
    let run := colorProgram.program.run H k ids initial (fun _ _ => false)
    (∀ v, (run t v).degree = k.degree ∧
      (run t v).palette = (paddedNext k.degree)^[t] (max (k.degree^64) k.palette)) ∧
    Proper H ((paddedNext k.degree)^[t] (max (k.degree^64) k.palette))
      (fun v => (run t v).color) := by
  dsimp only
  induction t with
  | zero =>
    refine ⟨fun v => ⟨rfl,rfl⟩,fun v => (hinit.1 v).trans_le (le_max_right _ _),?_⟩
    intro v w hvw heq
    exact hinit.2 v w hvw heq
  | succ t ih =>
    obtain ⟨hstate,hproper⟩ := ih
    let run := colorProgram.program.run H k ids initial (fun _ _ => false)
    let Q := (paddedNext k.degree)^[t] (max (k.degree^64) k.palette)
    have hnew := local_reduce_proper H k.degree _ _ hproper hD
    have hstep (v : V) : (run (t+1) v).color =
        localReduce k.degree Q (run t v).color
          ((H.neighborFinset v).image (fun w => (run t w).color)) := by
      change localReduce (run t v).degree (run t v).palette (run t v).color
        (((univ.filter (H.Adj v)).val.map fun w => (run t w).color).toFinset) = _
      rw [(hstate v).1,(hstate v).2]
      rw [← Finset.image_toFinset,Finset.val_toFinset,← H.neighborFinset_eq_filter]
    constructor
    · intro v
      constructor
      · change (run t v).degree = k.degree
        exact (hstate v).1
      · change paddedNext (run t v).degree (run t v).palette = _
        rw [(hstate v).1,(hstate v).2,Function.iterate_succ_apply']
    · simp only [Function.iterate_succ_apply']
      constructor
      · intro v
        change (run (t+1) v).color < paddedNext k.degree Q
        rw [hstep]
        exact (hnew.1 v).trans_le (le_max_right _ _)
      · intro v w hvw
        change (run (t+1) v).color ≠ (run (t+1) w).color
        rw [hstep,hstep]
        exact hnew.2 v w hvw

lemma colorProgram_correct {V : Type} [Fintype V] (H : SimpleGraph V)
    (k : ColorParameters) (ids initial : V → ℕ) (hinit : Proper H k.palette initial) (hD2 : 2 ≤ k.degree) (hD : ∀ v, H.degree v ≤ k.degree) :
    Proper H (k.degree^64)
      (colorProgram.program.output H k ids initial (fun _ _ => false)) := by
  have h := colorProgram_invariant H k ids initial hinit hD (2*height k.palette)
  have hp := palette_iterations k.degree k.palette hD2
  exact ⟨fun v => (h.2.1 v).trans_le hp,h.2.2⟩

lemma colorProgram_rounds (D n B : ℕ) :
    colorProgram.program.rounds ⟨D,(max 2 n)^B⟩ ≤ 2*(B+1)*logStar n := by
  change 2*height ((max 2 n)^B) ≤ _
  have h := Nat.mul_le_mul_left 2 (height_ID_bound n B)
  simpa only [mul_assoc] using h


def greedy {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) : ℕ → Finset V
  | 0 => ∅
  | t+1 => greedy H col t ∪ univ.filter (fun v => col v = t ∧
      ∀ w, H.Adj v w → w ∉ greedy H col t)

lemma greedy_step {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) (t : ℕ) (v : V) :
    v ∈ greedy H col (t+1) ↔ v ∈ greedy H col t ∨
      (col v = t ∧ ∀ w, H.Adj v w → w ∉ greedy H col t) := by
  simp only [greedy,mem_union,mem_filter,mem_univ,true_and]

lemma greedy_mono {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) :
    Monotone (greedy H col) := by
  apply monotone_nat_of_le_succ
  intro t v hv
  exact (greedy_step H col t v).mpr (Or.inl hv)

lemma greedy_independent {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ)
    (hc : ∀ v w, H.Adj v w → col v ≠ col w) (t : ℕ) :
    ∀ v ∈ greedy H col t, ∀ w ∈ greedy H col t, ¬ H.Adj v w := by
  induction t with
  | zero => simp [greedy]
  | succ t ih =>
    intro v hv w hw hvw
    rcases (greedy_step H col t v).mp hv with hold | hnew
    · rcases (greedy_step H col t w).mp hw with holdw | hneww
      · exact ih v hold w holdw hvw
      · exact hneww.2 v hvw.symm hold
    · rcases (greedy_step H col t w).mp hw with holdw | hneww
      · exact hnew.2 w hvw holdw
      · exact hc v w hvw (hnew.1.trans hneww.1.symm)

lemma greedy_dominates {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) (t : ℕ) :
    ∀ v, col v < t → v ∈ greedy H col t ∨ ∃ w, H.Adj v w ∧ w ∈ greedy H col t := by
  induction t with
  | zero => intro v hv; omega
  | succ t ih =>
    intro v hv
    by_cases hlt : col v < t
    · rcases ih v hlt with h | ⟨w,hw,hmem⟩
      · exact Or.inl (greedy_mono H col (Nat.le_succ t) h)
      · exact Or.inr ⟨w,hw,greedy_mono H col (Nat.le_succ t) hmem⟩
    · have heq : col v = t := by omega
      by_cases hn : ∀ w, H.Adj v w → w ∉ greedy H col t
      · exact Or.inl ((greedy_step H col t v).mpr (Or.inr ⟨heq,hn⟩))
      · push Not at hn
        obtain ⟨w,hw,hmem⟩ := hn
        exact Or.inr ⟨w,hw,greedy_mono H col (Nat.le_succ t) hmem⟩

structure MISState where
  colors : ColorState
  remaining : ℕ
  index : ℕ
  selected : Bool

def misProgram : Deterministic ColorParameters ℕ Bool where
  program := {
    State := MISState
    Msg := ℕ ⊕ Bool
    rounds := fun k => 2*height k.palette+k.degree^64
    init := fun k id initial _ =>
      ⟨colorProgram.program.init k id initial (fun _ => false),2*height k.palette,0,false⟩
    send := fun s => if 0 < s.remaining then Sum.inl s.colors.color else Sum.inr s.selected
    step := fun s msgs => if 0 < s.remaining then
      {s with remaining := s.remaining-1, colors := (colorProgram.program.step s.colors
        (msgs.filterMap fun m => match m with | .inl n => some n | .inr _ => none))}
      else {s with index := s.index+1, selected := (s.selected ||
        (decide (s.colors.color = s.index) && !decide (Sum.inr true ∈ msgs)))}
    out := MISState.selected }
  tape_independent := by intros; rfl

set_option backward.isDefEq.respectTransparency false in
lemma mis_prefix {V : Type} [Fintype V] (H : SimpleGraph V) (k : ColorParameters)
    (ids initial : V → ℕ) (t : ℕ) (ht : t ≤ 2*height k.palette) : ∀ v,
    misProgram.program.run H k ids initial (fun _ _ => false) t v =
      ⟨colorProgram.program.run H k ids initial (fun _ _ => false) t v,
        2*height k.palette-t,0,false⟩ := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    have hpos : 0 < 2*height k.palette-t := by omega
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih (by omega)]
    simp only [misProgram]
    simp only [hpos,if_true,Multiset.filterMap_map,Function.comp_def]
    change (⟨colorProgram.program.step
      (colorProgram.program.run H k ids initial (fun _ _ => false) t v)
        (Multiset.filterMap (some ∘ (fun w => (colorProgram.program.run H k ids initial (fun _ _ => false) t w).color))
          (univ.filter (H.Adj v)).val),2*height k.palette-t-1,0,false⟩ : MISState) = _
    rw [Multiset.filterMap_eq_map]
    congr 1

lemma greedy_bool_update {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ)
    (i : ℕ) (v : V) :
    (decide (v ∈ greedy H col i) || (decide (col v = i) &&
      !decide (Sum.inr true ∈ ((univ.filter (H.Adj v)).val.map fun w =>
        (Sum.inr (decide (w ∈ greedy H col i)) : ℕ ⊕ Bool))))) =
      decide (v ∈ greedy H col (i+1)) := by
  have hm : (Sum.inr true ∈ ((univ.filter (H.Adj v)).val.map fun w =>
      (Sum.inr (decide (w ∈ greedy H col i)) : ℕ ⊕ Bool))) ↔
        ∃ w, H.Adj v w ∧ w ∈ greedy H col i := by simp
  have hn : (∀ w, H.Adj v w → w ∉ greedy H col i) ↔
      ¬∃ w, H.Adj v w ∧ w ∈ greedy H col i := by aesop
  simp only [greedy_step,hn,hm]
  by_cases h₁ : v ∈ greedy H col i <;> by_cases h₂ : col v = i <;>
    by_cases h₃ : ∃ w, H.Adj v w ∧ w ∈ greedy H col i <;> simp [h₁,h₂,h₃]

lemma mis_greedy {V : Type} [Fintype V] (H : SimpleGraph V) (k : ColorParameters)
    (ids initial : V → ℕ) (i : ℕ) : ∀ v,
    misProgram.program.run H k ids initial (fun _ _ => false) (2*height k.palette+i) v =
      ⟨colorProgram.program.run H k ids initial (fun _ _ => false) (2*height k.palette) v,
        0,i,decide (v ∈ greedy H
          (colorProgram.program.output H k ids initial (fun _ _ => false)) i)⟩ := by
  induction i with
  | zero =>
    intro v
    simpa only [Nat.add_zero,Nat.sub_self,greedy,notMem_empty,decide_false] using
      mis_prefix H k ids initial (2*height k.palette) le_rfl v
  | succ i ih =>
    intro v
    rw [show 2*height k.palette+(i+1) = (2*height k.palette+i)+1 by omega,SmoothedMIS.LocalAlg.run]
    simp only [ih]
    simp only [misProgram,Nat.lt_irrefl,if_false]
    change (⟨_,0,i+1,_⟩ : MISState) = _
    congr 1
    exact greedy_bool_update H _ i v

lemma mis_correct {V : Type} [Fintype V] (H : SimpleGraph V) (k : ColorParameters)
    (ids initial : V → ℕ) (hinit : Proper H k.palette initial)
    (hD2 : 2 ≤ k.degree) (hD : ∀ v, H.degree v ≤ k.degree) :
    (∀ v w, misProgram.program.output H k ids initial (fun _ _ => false) v = true →
      misProgram.program.output H k ids initial (fun _ _ => false) w = true → ¬ H.Adj v w) ∧
    ∀ v, misProgram.program.output H k ids initial (fun _ _ => false) v = true ∨
      ∃ w, H.Adj v w ∧ misProgram.program.output H k ids initial (fun _ _ => false) w = true := by
  let col := colorProgram.program.output H k ids initial (fun _ _ => false)
  have hcol := colorProgram_correct H k ids initial hinit hD2 hD
  have hout (v : V) : misProgram.program.output H k ids initial (fun _ _ => false) v =
      decide (v ∈ greedy H col (k.degree^64)) := by
    change (misProgram.program.run H k ids initial (fun _ _ => false)
      (2*height k.palette+k.degree^64) v).selected = _
    rw [mis_greedy]
  constructor
  · intro v w hv hw
    rw [hout,decide_eq_true_eq] at hv hw
    exact greedy_independent H col hcol.2 _ v hv w hw
  · intro v
    rcases greedy_dominates H col _ v (hcol.1 v) with h | ⟨w,hw,hs⟩
    · exact Or.inl (by rw [hout,decide_eq_true_eq]; exact h)
    · exact Or.inr ⟨w,hw,by rw [hout,decide_eq_true_eq]; exact hs⟩

end BlockColorProof

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching

namespace BlockProof

lemma virtual_degree {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (q : ℝ) (p : Pairing N) (hp : ValidPairing G x q p) (a : Copy p) :
    (virtualGraph p).degree a ≤ 2 := by
  let S := (virtualGraph p).neighborFinset a
  have hinj : Set.InjOn (fun b : Copy p => b.1) (S : Set (Copy p)) := by
    intro b hb c hc hid
    have hab : (virtualGraph p).Adj a b := by simpa [S] using hb
    have hac : (virtualGraph p).Adj a c := by simpa [S] using hc
    cases b with
    | mk vb ib =>
      cases c with
      | mk vc ic =>
        change vb = vc at hid
        subst vc
        have hact := hp.2.2.1 ⟨vb,ib⟩ a.1 hab.2.2
        have huniq := (hp.2.1 vb a.1).mp hact
        have hi : ib = ic := huniq.unique hab.2.2 hac.2.2
        subst ic
        rfl
  have hsub : S.image (fun b : Copy p => b.1) ⊆ group p a := by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    have h : (virtualGraph p).Adj a b := by simpa [S] using hb
    exact h.2.1
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  change S.card ≤ 2
  calc
    S.card = (S.image (fun b : Copy p => b.1)).card := (card_image_iff.mpr hinj).symm
    _ ≤ (group p a).card := card_le_card hsub
    _ ≤ 2 := by rcases hp.1 a with h | h <;> omega

section Geometry
variable {V : Type} [Fintype V] (H : SimpleGraph V)

def outside (S : Finset V) (v : V) : Finset V := H.neighborFinset v \ S

def boundary (S : Finset V) : Finset V := S.biUnion (outside H S)

lemma degree_partition (S : Finset V) (v : S) :
    (H.induce (S : Set V)).degree v + (outside H S v.val).card = H.degree v.val := by
  letI : Fintype ↥(S : Set V) := inferInstanceAs (Fintype ↥S)
  have hmap := H.map_neighborFinset_induce (s := (S : Set V)) v
  have hcard := congrArg Finset.card hmap
  have hin : (H.induce (S : Set V)).degree v = (H.neighborFinset v.val ∩ S).card := by
    simp only [card_map,SimpleGraph.card_neighborFinset_eq_degree,Finset.toFinset_coe] at hcard
    refine Eq.trans ?_ hcard
    unfold SimpleGraph.degree SimpleGraph.neighborFinset
    simp only [Set.toFinset_card,← Nat.card_eq_fintype_card]
  rw [hin]
  have h := card_sdiff_add_card_inter (H.neighborFinset v.val) S
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h
  unfold outside
  omega

lemma boundary_card (S : Finset V) (hc : (H.induce (S : Set V)).Connected)
    (hD : ∀ v, H.degree v ≤ 2) : (boundary H S).card ≤ 2 := by
  letI : Fintype ↥(S : Set V) := inferInstanceAs (Fintype ↥S)
  have hsum : (∑ v : S, (H.induce (S : Set V)).degree v) +
      (∑ v : S, (outside H S v.val).card) ≤ 2*S.card := by
    rw [← sum_add_distrib]
    calc
      _ ≤ ∑ _ : S, 2 := sum_le_sum fun v _ => by rw [degree_partition]; exact hD v.val
      _ = _ := by simp [mul_comm]
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hsum
  have hedge := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card] at hedge
  have hs : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
  have hout : (∑ v : S, (outside H S v.val).card) ≤ 2 := by omega
  calc
    _ ≤ ∑ v ∈ S, (outside H S v).card := card_biUnion_le
    _ ≤ 2 := by rw [← sum_coe_sort]; exact hout

def ball (r : ℕ) (a : V) : Finset V := univ.filter (Close H r a)

lemma center_mem_ball (r : ℕ) (a : V) : a ∈ ball H r a :=
  mem_filter.mpr ⟨mem_univ a,.intro .nil (by simp)⟩

lemma ball_mono (a : V) {r s : ℕ} (hrs : r ≤ s) : ball H r a ⊆ ball H s a := by
  intro v hv
  obtain ⟨w,hw⟩ := (mem_filter.mp hv).2
  exact mem_filter.mpr ⟨mem_univ v,w,hw.trans hrs⟩

lemma ball_connected (r : ℕ) (a : V) : (H.induce (ball H r a : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨a,center_mem_ball H r a⟩,?_⟩
  rintro ⟨v,hv⟩
  obtain ⟨w,hw⟩ := (mem_filter.mp hv).2
  have hall : ∀ c ∈ w.support, c ∈ (ball H r a : Set V) := by
    intro c hc
    exact mem_filter.mpr ⟨mem_univ c,w.takeUntil c hc,(w.length_takeUntil_le_length hc).trans hw⟩
  exact ⟨w.induce (ball H r a : Set V) hall⟩

lemma ball_new_boundary (r : ℕ) (a : V) :
    ball H (r+1) a \ ball H r a ⊆ boundary H (ball H r a) := by
  intro c hc
  obtain ⟨hc,hnot⟩ := mem_sdiff.mp hc
  obtain ⟨w,hw⟩ := (mem_filter.mp hc).2
  have hlen : w.reverse.length ≤ r+1 := by simpa using hw
  cases hrev : w.reverse with
  | nil => exact False.elim (hnot (center_mem_ball H r _))
  | @cons c b a h tail =>
    have ht : tail.length ≤ r := by
      rw [hrev,SimpleGraph.Walk.length_cons] at hlen
      omega
    apply mem_biUnion.mpr
    refine ⟨b,mem_filter.mpr ⟨mem_univ b,tail.reverse,by simpa using ht⟩,?_⟩
    exact mem_sdiff.mpr ⟨by simpa using h.symm,hnot⟩

lemma ball_card_linear (hD : ∀ v, H.degree v ≤ 2) (r : ℕ) (a : V) :
    (ball H r a).card ≤ 2*r+1 := by
  have hzero : ball H 0 a = {a} := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw⟩ := (mem_filter.mp hv).2
      exact mem_singleton.mpr (w.eq_of_length_eq_zero (by omega)).symm
    · intro hv
      have hv' := mem_singleton.mp hv
      subst v
      exact center_mem_ball H 0 a
  induction r with
  | zero => simp [hzero]
  | succ r ih =>
    have hnew : (ball H (r+1) a \ ball H r a).card ≤ 2 :=
      (card_le_card (ball_new_boundary H r a)).trans (boundary_card H _ (ball_connected H r a) hD)
    have hcard := card_sdiff_add_card_eq_card (ball_mono H a (show r ≤ r+1 by omega))
    omega

def comp (a : V) : Finset V := univ.filter (H.Reachable a)

lemma ball_subset_comp (r : ℕ) (a : V) : ball H r a ⊆ comp H a := by
  intro v hv
  obtain ⟨w,_⟩ := (mem_filter.mp hv).2
  exact mem_filter.mpr ⟨mem_univ v,⟨w⟩⟩

lemma boundary_ball (r : ℕ) (a : V) : boundary H (ball H r a) = ball H (r+1) a \ ball H r a := by
  apply subset_antisymm
  · intro v hv
    obtain ⟨u,hu,huv⟩ := mem_biUnion.mp hv
    obtain ⟨hadj,hnot⟩ := mem_sdiff.mp huv
    have hadj' : H.Adj u v := by simpa using hadj
    obtain ⟨w,hw⟩ := (mem_filter.mp hu).2
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ v,w.append (.cons hadj' .nil),?_⟩,hnot⟩
    simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil]
    omega
  · exact ball_new_boundary H r a

lemma comp_subset_of_boundary_empty (a : V) (S : Finset V) (ha : a ∈ S)
    (hb : boundary H S = ∅) : comp H a ⊆ S := by
  have hclosed (u v : V) (hu : u ∈ S) (huv : H.Adj u v) : v ∈ S := by
    by_contra hv
    have hmem : v ∈ boundary H S :=
      mem_biUnion.mpr ⟨u,hu,mem_sdiff.mpr ⟨by simpa using huv,hv⟩⟩
    rw [hb] at hmem
    exact notMem_empty _ hmem
  have hwalk {u v : V} (w : H.Walk u v) : u ∈ S → v ∈ S := by
    induction w with
    | nil => exact id
    | cons h w ih => intro hu; exact ih (hclosed _ _ hu h)
  intro v hv
  obtain ⟨w⟩ := (mem_filter.mp hv).2
  exact hwalk w ha

lemma ball_grows (r : ℕ) (a : V) (h : ball H r a ≠ comp H a) :
    (ball H r a).card < (ball H (r+1) a).card := by
  have hb : (boundary H (ball H r a)).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    apply h
    exact subset_antisymm (ball_subset_comp H r a)
      (comp_subset_of_boundary_empty H a _ (center_mem_ball H r a) he)
  rw [boundary_ball] at hb
  have hpos : 0 < (ball H (r+1) a \ ball H r a).card := card_pos.mpr hb
  have heq := card_sdiff_add_card_eq_card (ball_mono H a (show r ≤ r+1 by omega))
  omega

lemma ball_card_lower (r : ℕ) (a : V) : min (r+1) (comp H a).card ≤ (ball H r a).card := by
  induction r with
  | zero =>
    have hpos := card_pos.mpr (show (ball H 0 a).Nonempty from ⟨a,center_mem_ball H 0 a⟩)
    exact (min_le_left _ _).trans (by omega)
  | succ r ih =>
    by_cases heq : ball H r a = comp H a
    · apply le_trans (min_le_right _ _)
      rw [← heq]
      exact card_le_card (ball_mono H a (show r ≤ r+1 by omega))
    · have hgrow := ball_grows H r a heq
      have hcard : (ball H r a).card < (comp H a).card := by
        apply card_lt_card
        exact Finset.ssubset_iff_subset_ne.mpr ⟨ball_subset_comp H r a,heq⟩
      omega

lemma comp_card_dist {a b : V} (h : H.Reachable a b) : H.dist a b+1 ≤ (comp H a).card := by
  obtain ⟨w,hpath,hw⟩ := h.exists_path_of_dist
  have hsub : w.support.toFinset ⊆ comp H a := by
    intro v hv
    have hv' : v ∈ w.support := List.mem_toFinset.mp hv
    exact mem_filter.mpr ⟨mem_univ v,⟨w.takeUntil v hv'⟩⟩
  have hc := card_le_card hsub
  rw [List.toFinset_card_of_nodup hpath.support_nodup,SimpleGraph.Walk.length_support,hw] at hc
  exact hc

lemma packing_card (hD : ∀ v, H.degree v ≤ 2) (r : ℕ) (hr : 1 ≤ r)
    (a : V) (S : Finset V)
    (hsep : ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ¬ Close H r b c)
    (hnear : ∀ b ∈ S, Close H (2*r) a b)
    (hlarge : ∀ b ∈ S, r/2+1 ≤ (comp H b).card) : S.card ≤ 10 := by
  have hdisj : (S : Set V).PairwiseDisjoint (fun b => ball H (r/2) b) := by
    intro b hb c hc hbc
    apply disjoint_left.mpr
    intro z hzb hzc
    obtain ⟨p,hp⟩ := (mem_filter.mp hzb).2
    obtain ⟨q,hq⟩ := (mem_filter.mp hzc).2
    apply hsep b hb c hc hbc
    exact ⟨p.append q.reverse,by simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse]; omega⟩
  have hsub : S.biUnion (fun b => ball H (r/2) b) ⊆ ball H (2*r+r/2) a := by
    intro z hz
    obtain ⟨b,hb,hz⟩ := mem_biUnion.mp hz
    obtain ⟨p,hp⟩ := hnear b hb
    obtain ⟨q,hq⟩ := (mem_filter.mp hz).2
    exact mem_filter.mpr ⟨mem_univ z,p.append q,by rw [SimpleGraph.Walk.length_append]; omega⟩
  have hcount : S.card*(r/2+1) ≤ 2*(2*r+r/2)+1 := by
    calc
      _ = ∑ _ ∈ S, (r/2+1) := by simp
      _ ≤ ∑ b ∈ S, (ball H (r/2) b).card := by
        apply sum_le_sum
        intro b hb
        have h := ball_card_lower H (r/2) b
        rw [min_eq_left (hlarge b hb)] at h
        exact h
      _ = (S.biUnion (fun b => ball H (r/2) b)).card := (card_biUnion hdisj).symm
      _ ≤ (ball H (2*r+r/2) a).card := card_le_card hsub
      _ ≤ _ := ball_card_linear H hD _ _
  by_contra h
  have hh : 11*(r/2+1) ≤ S.card*(r/2+1) := Nat.mul_le_mul_right _ (by omega)
  omega

def filteredPower (r : ℕ) (S : Finset V) : SimpleGraph V where
  Adj a b := a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ Close H r a b
  symm := ⟨by
    intro a b h
    obtain ⟨w,hw⟩ := h.2.2.2
    exact ⟨h.2.1,h.1,h.2.2.1.symm,w.reverse,by simpa using hw⟩⟩
  loopless := ⟨by intro a h; exact h.2.2.1 rfl⟩

lemma filteredPower_degree (hD : ∀ v, H.degree v ≤ 2) (r : ℕ) (hr : 1 ≤ r)
    (S : Finset V) (hsep : ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ¬ Close H r b c) (a : V) :
    (filteredPower H (2*r) S).degree a ≤ 10 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  let T := (filteredPower H (2*r) S).neighborFinset a
  have hT (b : V) (hb : b ∈ T) : a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ Close H (2*r) a b := by
    exact (SimpleGraph.mem_neighborFinset (filteredPower H (2*r) S) a b).mp hb
  have hsepT : ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ¬ Close H r b c := by
    intro b hb c hc hbc
    exact hsep b (hT b hb).2.1 c (hT c hc).2.1 hbc
  have hnear : ∀ b ∈ T, Close H (2*r) a b := fun b hb => (hT b hb).2.2.2
  have hlarge : ∀ b ∈ T, r/2+1 ≤ (comp H b).card := by
    intro b hb
    obtain ⟨w,hw⟩ := (hT b hb).2.2.2
    have hreach : H.Reachable b a := ⟨w.reverse⟩
    have hnclose : ¬ Close H r b a := hsep b (hT b hb).2.1 a (hT b hb).1 (hT b hb).2.2.1.symm
    have hd : r < H.dist b a := by
      by_contra hh
      obtain ⟨q,hq⟩ := hreach.exists_walk_length_eq_dist
      exact hnclose ⟨q,by omega⟩
    have hcomp := comp_card_dist H hreach
    omega
  exact packing_card H hD r hr a T hsepT hnear hlarge

end Geometry

end BlockProof

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace BlockProof
section Net
variable {V : Type} [Fintype V] (H : SimpleGraph V)

def leaderStep (r zeta : ℕ) (col : V → ℕ) (S : Finset V) : Finset V :=
  S.filter fun v => BlockColorProof.misProgram.program.output
    (filteredPower H r S) ⟨10,zeta⟩ (fun _ => 0) col (fun _ _ => false) v = true

lemma leaderStep_subset (r zeta : ℕ) (col : V → ℕ) (S : Finset V) :
    leaderStep H r zeta col S ⊆ S := filter_subset _ _

lemma leaderStep_spec (r zeta : ℕ) (col : V → ℕ) (S : Finset V)
    (hcol : Separates H r zeta col)
    (hD : ∀ v, (filteredPower H r S).degree v ≤ 10) :
    (∀ a ∈ leaderStep H r zeta col S, ∀ b ∈ leaderStep H r zeta col S,
      a ≠ b → ¬ Close H r a b) ∧
    ∀ a ∈ S, ∃ b ∈ leaderStep H r zeta col S, Close H r a b := by
  have hp : Proper (filteredPower H r S) zeta col :=
    ⟨hcol.1,fun a b hab => hcol.2 a b hab.2.2.1 hab.2.2.2⟩
  have hm := BlockColorProof.mis_correct (filteredPower H r S) ⟨10,zeta⟩
    (fun _ => 0) col hp (by norm_num) hD
  constructor
  · intro a ha b hb hab hclose
    exact hm.1 a b (mem_filter.mp ha).2 (mem_filter.mp hb).2
      ⟨(mem_filter.mp ha).1,(mem_filter.mp hb).1,hab,hclose⟩
  · intro a ha
    rcases hm.2 a with hs | ⟨b,hab,hs⟩
    · exact ⟨a,mem_filter.mpr ⟨ha,hs⟩,SimpleGraph.Walk.nil,by simp⟩
    · exact ⟨b,mem_filter.mpr ⟨hab.2.1,hs⟩,hab.2.2.2⟩

def leaders (zeta : ℕ) (col : V → ℕ) : ℕ → Finset V
  | 0 => univ
  | j+1 => leaderStep H (2^(j+1)) zeta col (leaders zeta col j)

lemma leaders_mono (zeta : ℕ) (col : V → ℕ) : Antitone (leaders H zeta col) := by
  apply antitone_nat_of_succ_le
  intro j
  exact leaderStep_subset H _ _ _ _

lemma filteredPower_two_degree (hD : ∀ v, H.degree v ≤ 2) (S : Finset V) (a : V) :
    (filteredPower H 2 S).degree a ≤ 10 := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (filteredPower H 2 S).neighborFinset a ⊆ ball H 2 a := by
    intro b hb
    have hab := (SimpleGraph.mem_neighborFinset _ _ _).mp hb
    exact mem_filter.mpr ⟨mem_univ _,hab.2.2.2⟩
  exact (card_le_card hsub).trans ((ball_card_linear H hD 2 a).trans (by decide))

lemma leaders_spec (hD : ∀ v, H.degree v ≤ 2) (zeta t : ℕ) (col : V → ℕ)
    (hcol : Separates H (2^t) zeta col) (j : ℕ) (hj : j ≤ t) :
    (0 < j → ∀ a ∈ leaders H zeta col j, ∀ b ∈ leaders H zeta col j,
      a ≠ b → ¬ Close H (2^j) a b) ∧
    ∀ a, ∃ b ∈ leaders H zeta col j, Close H (2^(j+1)-2) a b := by
  induction j with
  | zero =>
    refine ⟨by omega,fun a => ⟨a,mem_univ _,SimpleGraph.Walk.nil,by simp⟩⟩
  | succ j ih =>
    have hjt : j ≤ t := by omega
    have ih := ih hjt
    have hc : Separates H (2^(j+1)) zeta col := by
      refine ⟨hcol.1,fun a b hab ⟨w,hw⟩ => hcol.2 a b hab ⟨w,?_⟩⟩
      exact hw.trans (Nat.pow_le_pow_right (by decide) hj)
    have hd : ∀ v, (filteredPower H (2^(j+1)) (leaders H zeta col j)).degree v ≤ 10 := by
      cases j with
      | zero => simpa using filteredPower_two_degree H hD (leaders H zeta col 0)
      | succ j =>
        rw [pow_succ]
        rw [Nat.mul_comm (2^(j+1)) 2]
        exact filteredPower_degree H hD (2^(j+1))
          (Nat.one_le_pow _ _ (by decide)) (leaders H zeta col (j+1)) (ih.1 (by omega))
    have hs := leaderStep_spec H (2^(j+1)) zeta col (leaders H zeta col j) hc hd
    refine ⟨fun _ => hs.1,fun a => ?_⟩
    obtain ⟨b,hb,w,hw⟩ := ih.2 a
    obtain ⟨c,hc,q,hq⟩ := hs.2 b hb
    refine ⟨c,hc,w.append q,?_⟩
    rw [SimpleGraph.Walk.length_append]
    have hp : 2 ≤ 2^(j+1) := by
      exact (show 2^1 ≤ 2^(j+1) from Nat.pow_le_pow_right (by decide) (by omega))
    have he : 2^(j+1+1) = 2^(j+1)*2 := pow_succ _ _
    omega

def netDepth (ell : ℕ) : ℕ := Nat.clog 2 (8*ell)

lemma netDepth_bounds (ell : ℕ) (hell : 1 ≤ ell) :
    0 < netDepth ell ∧ 8*ell ≤ 2^netDepth ell ∧ 2^netDepth ell < 16*ell := by
  have hx : 1 < 8*ell := by omega
  have hp := Nat.clog_pos (by decide : 1 < 2) hx
  have hu := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hx
  simp only [Nat.pred_eq_sub_one] at hu
  have he : 2^Nat.clog 2 (8*ell) = 2^(Nat.clog 2 (8*ell)-1)*2 := by
    rw [←pow_succ]
    congr 1
    omega
  exact ⟨hp,Nat.le_pow_clog (by decide) _,by change 2^Nat.clog 2 (8*ell) < _; rw [he]; omega⟩

def finalLeaders (ell zeta : ℕ) (col : V → ℕ) : Finset V := leaders H zeta col (netDepth ell)

lemma finalLeaders_spec (hD : ∀ v, H.degree v ≤ 2) (ell zeta : ℕ) (hell : 1 ≤ ell)
    (col : V → ℕ) (hcol : Separates H (64*ell) zeta col) :
    (∀ a ∈ finalLeaders H ell zeta col, ∀ b ∈ finalLeaders H ell zeta col,
      a ≠ b → ¬Close H (8*ell) a b) ∧
    ∀ a, ∃ b ∈ finalLeaders H ell zeta col, Close H (32*ell) a b := by
  obtain ⟨ht,hlo,hup⟩ := netDepth_bounds ell hell
  have hc : Separates H (2^netDepth ell) zeta col := by
    refine ⟨hcol.1,fun a b hab ⟨w,hw⟩ => hcol.2 a b hab ⟨w,?_⟩⟩
    omega
  have hs := leaders_spec H hD zeta (netDepth ell) col hc (netDepth ell) le_rfl
  constructor
  · intro a ha b hb hab ⟨w,hw⟩
    exact hs.1 ht a ha b hb hab ⟨w,hw.trans hlo⟩
  · intro a
    obtain ⟨b,hb,w,hw⟩ := hs.2 a
    refine ⟨b,hb,w,?_⟩
    rw [pow_succ] at hw
    omega

end Net
end BlockProof

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace BlockProof
section Voronoi
variable {V : Type} [Fintype V] (H : SimpleGraph V)

def score (key : V → ℕ) (v l : V) : Lex (ℕ × ℕ) := toLex (H.dist v l,key l)

def Nearest (S : Finset V) (key : V → ℕ) (v l : V) : Prop :=
  l ∈ S ∧ H.Reachable v l ∧ ∀ m ∈ S, H.Reachable v m → score H key v l ≤ score H key v m

lemma nearest_exists (S : Finset V) (key : V → ℕ) (v : V)
    (hex : ∃ l ∈ S, H.Reachable v l) : ∃ l, Nearest H S key v l := by
  let T := S.filter (H.Reachable v)
  have ht : T.Nonempty := by simpa only [T,Finset.Nonempty,mem_filter] using hex
  obtain ⟨l,hl,hmin⟩ := exists_min_image T (score H key v) ht
  refine ⟨l,(mem_filter.mp hl).1,(mem_filter.mp hl).2,?_⟩
  intro m hm hr
  exact hmin m (mem_filter.mpr ⟨hm,hr⟩)

lemma nearest_unique (S : Finset V) (key : V → ℕ) (hi : Function.Injective key)
    {v l m : V} (hl : Nearest H S key v l) (hm : Nearest H S key v m) : l = m := by
  have h := le_antisymm (hl.2.2 m hm.1 hm.2.1) (hm.2.2 l hl.1 hl.2.1)
  exact hi (congrArg (fun x : Lex (ℕ × ℕ) => (ofLex x).2) h)

lemma nearest_self (S : Finset V) (key : V → ℕ) {l : V} (hl : l ∈ S) :
    Nearest H S key l l := by
  refine ⟨hl,(⟨SimpleGraph.Walk.nil⟩ : H.Reachable l l),fun m hm hr => ?_⟩
  by_cases he : l = m
  · subst m; exact le_rfl
  · apply Prod.Lex.toLex_le_toLex.mpr
    exact Or.inl (by simpa only [SimpleGraph.dist_self] using
      Nat.pos_of_ne_zero (fun h => he (hr.dist_eq_zero_iff.mp h)))

lemma nearest_dist_le (S : Finset V) (key : V → ℕ) {v l m : V}
    (hl : Nearest H S key v l) (hm : m ∈ S) (hr : H.Reachable v m) :
    H.dist v l ≤ H.dist v m := by
  have h := Prod.Lex.toLex_le_toLex.mp (hl.2.2 m hm hr)
  rcases h with h | ⟨h,_⟩ <;> omega

lemma geodesic_dist {a l c : V} (w : H.Walk a l) (hw : w.length = H.dist a l)
    (hc : c ∈ w.support) : H.dist a c + H.dist c l = H.dist a l := by
  have hp := H.dist_le (w.takeUntil c hc)
  have hq := H.dist_le (w.dropUntil c hc)
  have he := congrArg SimpleGraph.Walk.length (w.take_spec hc)
  simp only [SimpleGraph.Walk.length_append] at he
  have ht := (w.takeUntil c hc).reachable.dist_triangle_left l
  omega

lemma nearest_geodesic (S : Finset V) (key : V → ℕ) {a l c : V}
    (hl : Nearest H S key a l) (w : H.Walk a l) (hw : w.length = H.dist a l)
    (hc : c ∈ w.support) : Nearest H S key c l := by
  refine ⟨hl.1,(w.dropUntil c hc).reachable,fun m hm hr => ?_⟩
  have hac := (w.takeUntil c hc).reachable
  have hmin := Prod.Lex.toLex_le_toLex.mp (hl.2.2 m hm (hac.trans hr))
  have he := geodesic_dist H w hw hc
  have ht := hac.dist_triangle_left m
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases hmin with h | ⟨h,hkey⟩
  · left; omega
  · by_cases heq : H.dist c l = H.dist c m
    · exact Or.inr ⟨heq,hkey⟩
    · left; omega

lemma comp_eq_of_reachable {a b : V} (h : H.Reachable a b) : comp H a = comp H b := by
  ext v
  simp only [comp,mem_filter,mem_univ,true_and]
  exact ⟨fun hr => h.symm.trans hr,fun hr => h.trans hr⟩

def voronoi (ell : ℕ) (S : Finset V) (key : V → ℕ) (v : V) : Option V :=
  if h : ell ≤ (comp H v).card ∧ ∃ l, Nearest H S key v l then some h.2.choose else none

lemma voronoi_eq (ell : ℕ) (S : Finset V) (key : V → ℕ) (hi : Function.Injective key)
    {v l : V} (hv : ell ≤ (comp H v).card) (hl : Nearest H S key v l) :
    voronoi H ell S key v = some l := by
  unfold voronoi
  have hex : ell ≤ (comp H v).card ∧ ∃ l, Nearest H S key v l := ⟨hv,l,hl⟩
  rw [dif_pos hex]
  exact congrArg some (nearest_unique H S key hi hex.2.choose_spec hl)

lemma voronoi_spec (ell : ℕ) (S : Finset V) (key : V → ℕ) {v l : V}
    (hv : voronoi H ell S key v = some l) :
    ell ≤ (comp H v).card ∧ Nearest H S key v l := by
  unfold voronoi at hv
  split_ifs at hv with h
  · have he : h.2.choose = l := Option.some.inj hv
    exact ⟨h.1,he ▸ h.2.choose_spec⟩

def cell (B : V → Option V) (l : V) : Finset V := univ.filter (fun v => B v = some l)

lemma voronoi_none (ell : ℕ) (S : Finset V) (key : V → ℕ) (R : ℕ)
    (hcover : ∀ a, ∃ l ∈ S, Close H R a l) (v : V) :
    voronoi H ell S key v = none ↔ (comp H v).card < ell := by
  have hex : ∃ l, Nearest H S key v l := by
    obtain ⟨l,hl,w,hw⟩ := hcover v
    exact nearest_exists H S key v ⟨l,hl,w.reachable⟩
  simp only [voronoi]
  split_ifs with h
  · simp only [Option.some_ne_none,false_iff,not_lt]
    exact h.1
  · simp only [true_iff]
    have hn : ¬ell ≤ (comp H v).card := fun hv => h ⟨hv,hex⟩
    omega

lemma voronoi_cell_upper (hD : ∀ v, H.degree v ≤ 2) (ell R : ℕ) (S : Finset V)
    (key : V → ℕ) (hcover : ∀ a, ∃ m ∈ S, Close H R a m) (l : V) :
    (cell (voronoi H ell S key) l).card ≤ 2*R+1 := by
  apply le_trans (card_le_card (show cell (voronoi H ell S key) l ⊆ ball H R l from ?_))
    (ball_card_linear H hD R l)
  intro v hv
  have hs := (voronoi_spec H ell S key ((mem_filter.mp hv).2)).2
  obtain ⟨m,hm,w,hw⟩ := hcover v
  have hd := (nearest_dist_le H S key hs hm w.reachable).trans ((H.dist_le w).trans hw)
  obtain ⟨q,hq⟩ := hs.2.1.symm.exists_walk_length_eq_dist
  exact mem_filter.mpr ⟨mem_univ v,q,by simpa only [hq,SimpleGraph.dist_comm] using hd⟩

lemma nearest_near_leader (ell : ℕ) (hell : 1 ≤ ell) (S : Finset V) (key : V → ℕ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬Close H (8*ell) a b)
    {l v : V} (hl : l ∈ S) (hv : Close H (ell-1) l v) : Nearest H S key v l := by
  obtain ⟨w,hw⟩ := hv
  refine ⟨hl,w.reverse.reachable,fun m hm hr => ?_⟩
  by_cases he : l = m
  · subst m; exact le_rfl
  · apply Prod.Lex.toLex_le_toLex.mpr
    left
    by_contra hn
    have hd : H.dist v m ≤ H.dist v l := by omega
    have hdvl : H.dist v l ≤ ell-1 := by
      simpa only [SimpleGraph.dist_comm] using (H.dist_le w).trans hw
    obtain ⟨q,hq⟩ := hr.exists_walk_length_eq_dist
    exact hsep l hl m hm he ⟨w.append q,by rw [SimpleGraph.Walk.length_append,hq]; omega⟩

lemma voronoi_cell_lower (ell : ℕ) (hell : 1 ≤ ell) (S : Finset V) (key : V → ℕ)
    (hi : Function.Injective key)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬Close H (8*ell) a b)
    {a l : V} (ha : voronoi H ell S key a = some l) :
    ell ≤ (cell (voronoi H ell S key) l).card := by
  obtain ⟨hlarge,hs⟩ := voronoi_spec H ell S key ha
  have hlcomp : ell ≤ (comp H l).card := by rwa [←comp_eq_of_reachable H hs.2.1]
  have hsub : ball H (ell-1) l ⊆ cell (voronoi H ell S key) l := by
    intro v hv
    have hclose := (mem_filter.mp hv).2
    have hcomp : comp H l = comp H v := comp_eq_of_reachable H hclose.choose.reachable
    have hvlarge : ell ≤ (comp H v).card := by rwa [←hcomp]
    exact mem_filter.mpr ⟨mem_univ v,voronoi_eq H ell S key hi hvlarge
      (nearest_near_leader H ell hell S key hsep hs.1 hclose)⟩
  have hlow := ball_card_lower H (ell-1) l
  have hmin : min (ell-1+1) (comp H l).card = ell := by omega
  rw [hmin] at hlow
  exact hlow.trans (card_le_card hsub)

lemma voronoi_self (ell : ℕ) (S : Finset V) (key : V → ℕ) (hi : Function.Injective key)
    {a l : V} (ha : voronoi H ell S key a = some l) :
    voronoi H ell S key l = some l := by
  obtain ⟨hlarge,hs⟩ := voronoi_spec H ell S key ha
  apply voronoi_eq H ell S key hi
  · rwa [←comp_eq_of_reachable H hs.2.1]
  · exact nearest_self H S key hs.1

lemma voronoi_connected (ell : ℕ) (S : Finset V) (key : V → ℕ) (hi : Function.Injective key)
    {a b l : V} (ha : voronoi H ell S key a = some l)
    (hb : voronoi H ell S key b = some l) : ∃ w : H.Walk a b,
      ∀ c ∈ w.support, c ∈ cell (voronoi H ell S key) l := by
  obtain ⟨haL,haN⟩ := voronoi_spec H ell S key ha
  obtain ⟨hbL,hbN⟩ := voronoi_spec H ell S key hb
  obtain ⟨p,hp⟩ := haN.2.1.exists_walk_length_eq_dist
  obtain ⟨q,hq⟩ := hbN.2.1.exists_walk_length_eq_dist
  have hpall : ∀ c ∈ p.support, c ∈ cell (voronoi H ell S key) l := by
    intro c hc
    have hcomp := comp_eq_of_reachable H (p.takeUntil c hc).reachable
    exact mem_filter.mpr ⟨mem_univ _,voronoi_eq H ell S key hi (by rwa [←hcomp])
      (nearest_geodesic H S key haN p hp hc)⟩
  have hqall : ∀ c ∈ q.support, c ∈ cell (voronoi H ell S key) l := by
    intro c hc
    have hcomp := comp_eq_of_reachable H (q.takeUntil c hc).reachable
    exact mem_filter.mpr ⟨mem_univ _,voronoi_eq H ell S key hi (by rwa [←hcomp])
      (nearest_geodesic H S key hbN q hq hc)⟩
  refine ⟨p.append q.reverse,fun c hc => ?_⟩
  have hmem : c ∈ p.support ∨ c ∈ q.support := by
    simpa only [SimpleGraph.Walk.mem_support_append_iff,SimpleGraph.Walk.support_reverse,List.mem_reverse] using hc
  exact hmem.elim (hpall c) (hqall c)

end Voronoi
end BlockProof

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace BlockProof

lemma voronoi_valid {N : ℕ} (p : Pairing N) (ell : ℕ) (hell : 1 ≤ ell)
    (hD : ∀ a : Copy p, (virtualGraph p).degree a ≤ 2)
    (S : Finset (Copy p)) (key : Copy p → ℕ) (hi : Function.Injective key)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬Close (virtualGraph p) (8*ell) a b)
    (hcover : ∀ a, ∃ l ∈ S, Close (virtualGraph p) (32*ell) a l) :
    ValidBlocks ell (voronoi (virtualGraph p) ell S key) := by
  let H := virtualGraph p
  let B := voronoi H ell S key
  constructor
  · intro a
    simpa only [H,component,comp] using voronoi_none H ell S key (32*ell) hcover a
  · intro a l ha
    refine ⟨voronoi_self H ell S key hi ha,
      ?_,?_,?_⟩
    · simpa only [H,block,cell] using voronoi_cell_lower H ell hell S key hi hsep ha
    · have hu := voronoi_cell_upper H hD ell (32*ell) S key hcover l
      have hu' : (cell (voronoi H ell S key) l).card ≤ 65*ell+1 :=
        hu.trans (by omega)
      simpa only [H,block,cell] using hu'
    · intro b hb
      simpa only [H,block,cell] using voronoi_connected H ell S key hi ha ((mem_filter.mp hb).2)

lemma blocks_exist {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (q : ℝ) (p : Pairing N) (hp : ValidPairing G x q p)
    (ell zeta : ℕ) (hell : 1 ≤ ell) (col : Copy p → ℕ)
    (hcol : Separates (virtualGraph p) (64*ell) zeta col)
    (key : Copy p → ℕ) (hi : Function.Injective key) :
    ValidBlocks ell (voronoi (virtualGraph p) ell
      (finalLeaders (virtualGraph p) ell zeta col) key) := by
  have hd := virtual_degree G x q p hp
  have hs := finalLeaders_spec (virtualGraph p) hd ell zeta hell col hcol
  exact voronoi_valid p ell hell hd _ key hi hs.1 hs.2

end BlockProof

end

section


set_option maxHeartbeats 200000

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
attribute [local irreducible] BlockColorProof.misProgram

namespace BlockProof
section Locality
variable {V W : Type} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (J : SimpleGraph W) (f : W → V) (hf : Function.Injective f)

lemma walk_forward (hforward : ∀ a b, J.Adj a b → H.Adj (f a) (f b))
    {a b : W} (w : J.Walk a b) : ∃ q : H.Walk (f a) (f b), q.length = w.length := by
  induction w with
  | nil => exact ⟨.nil,rfl⟩
  | cons h w ih =>
    obtain ⟨q,hq⟩ := ih
    exact ⟨.cons (hforward _ _ h) q,by simp [hq]⟩

lemma walk_backward (hgraph : ∀ a b, J.Adj a b ↔ H.Adj (f a) (f b))
    {a : W} {v : V} (w : H.Walk (f a) v)
    (hall : ∀ b ∈ w.support, ∃ u, f u = b) :
    ∃ b : W, f b = v ∧ ∃ q : J.Walk a b, q.length = w.length := by
  generalize he : f a = start at w
  induction w generalizing a with
  | nil => exact ⟨a,he,.nil,rfl⟩
  | @cons x y z h w ih =>
    obtain ⟨b,hb⟩ := hall y (by simp)
    obtain ⟨c,hc,q,hq⟩ := ih hb (fun d hd => hall d (by simp [hd]))
    refine ⟨c,hc,.cons ((hgraph a b).mpr ?_) q,by simp [hq]⟩
    simpa only [he,hb] using h

include hf in
lemma run_embedding {K I O : Type} (A : Deterministic K I O) (k : K)
    (ids : V → ℕ) (inp : V → I) (ids' : W → ℕ) (inp' : W → I)
    (t : ℕ) (a : W)
    (hall : ∀ u, Close H t (f a) (f u) →
      ids' u = ids (f u) ∧ inp' u = inp (f u) ∧
        (∀ w, J.Adj u w → H.Adj (f u) (f w)) ∧
        ∀ v, H.Adj (f u) v → ∃ w, J.Adj u w ∧ f w = v) :
    A.program.run J k ids' inp' (fun _ _ => false) t a =
      A.program.run H k ids inp (fun _ _ => false) t (f a) := by
  induction t generalizing a with
  | zero =>
    obtain ⟨hi,hp,_⟩ := hall a ⟨.nil,by simp⟩
    simp only [SmoothedMIS.LocalAlg.run,hi,hp]
  | succ t ih =>
    have hself := hall a ⟨.nil,by simp⟩
    have hprev : ∀ u, Close H t (f a) (f u) →
        ids' u = ids (f u) ∧ inp' u = inp (f u) ∧
        (∀ w, J.Adj u w → H.Adj (f u) (f w)) ∧
          ∀ v, H.Adj (f u) v → ∃ w, J.Adj u w ∧ f w = v := by
      intro u ⟨p,hp⟩
      exact hall u ⟨p,by omega⟩
    have hneighbor (b : W) (hab : J.Adj a b) :
        A.program.run J k ids' inp' (fun _ _ => false) t b =
          A.program.run H k ids inp (fun _ _ => false) t (f b) := by
      apply ih
      intro u ⟨p,hp⟩
      exact hall u ⟨.cons (hself.2.2.1 b hab) p,by simpa using Nat.succ_le_succ hp⟩
    have hfin : (univ.filter (J.Adj a)).image f = univ.filter (H.Adj (f a)) := by
      ext v
      simp only [mem_image,mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨b,hb,rfl⟩; exact hself.2.2.1 b hb
      · intro hv
        obtain ⟨b,hb,hf⟩ := hself.2.2.2 v hv
        exact ⟨b,hb,hf⟩
    rw [SmoothedMIS.LocalAlg.run,SmoothedMIS.LocalAlg.run]
    dsimp only
    rw [ih a hprev,←hfin]
    rw [image_val_of_injOn (fun b _ c _ h => hf h),Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b hb
    have hab := (mem_filter.mp hb).2
    exact congrArg A.program.send (hneighbor b hab)

lemma filtered_walk_base (r : ℕ) (S : Finset V) {a b : V}
    (w : (filteredPower H r S).Walk a b) :
    ∃ q : H.Walk a b, q.length ≤ r*w.length := by
  induction w with
  | nil => exact ⟨.nil,by simp⟩
  | cons h w ih =>
    obtain ⟨p,hp⟩ := h.2.2.2
    obtain ⟨q,hq⟩ := ih
    refine ⟨p.append q,?_⟩
    simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]
    nlinarith

lemma filtered_close_base (r t : ℕ) (S : Finset V) {a b : V}
    (h : Close (filteredPower H r S) t a b) : Close H (r*t) a b := by
  obtain ⟨w,hw⟩ := h
  obtain ⟨q,hq⟩ := filtered_walk_base H r S w
  exact ⟨q,hq.trans (Nat.mul_le_mul_left r hw)⟩

include hf in
lemma power_run_local {K I O : Type} (A : Deterministic K I O) (k : K)
    (ids : V → ℕ) (inp : V → I) (r t : ℕ) (S : Finset V) (S' : Finset W)
    (hgraph : ∀ a b, J.Adj a b ↔ H.Adj (f a) (f b)) (a : W)
    (hmem : ∀ u, Close H (r*(t+1)) (f a) (f u) → (u ∈ S' ↔ f u ∈ S))
    (hall : ∀ v, Close H (r*(t+1)) (f a) v → ∃ u, f u = v) :
    A.program.run (filteredPower J r S') k (ids ∘ f) (inp ∘ f) (fun _ _ => false) t a =
      A.program.run (filteredPower H r S) k ids inp (fun _ _ => false) t (f a) := by
  apply run_embedding (filteredPower H r S) (filteredPower J r S') f hf A k ids inp (ids ∘ f) (inp ∘ f) t a
  intro u hu
  have hbase := filtered_close_base H r t S hu
  obtain ⟨p,hp⟩ := hbase
  have hself : u ∈ S' ↔ f u ∈ S := hmem u ⟨p,by nlinarith⟩
  refine ⟨rfl,rfl,?_,?_⟩
  · intro w huw
    obtain ⟨q,hq⟩ := huw.2.2.2
    obtain ⟨q',hq'⟩ := walk_forward H J f (fun a b h => (hgraph a b).mp h) q
    have hw : w ∈ S' ↔ f w ∈ S := hmem w ⟨p.append q',by
      simp only [SimpleGraph.Walk.length_append]; nlinarith⟩
    exact ⟨hself.mp huw.1,hw.mp huw.2.1,fun he => huw.2.2.1 (hf he),q',hq'.trans_le hq⟩
  · intro v huv
    obtain ⟨q,hq⟩ := huv.2.2.2
    have hqs : ∀ b ∈ q.support, ∃ w, f w = b := by
      intro b hb
      apply hall b
      refine ⟨p.append (q.takeUntil b hb),?_⟩
      have hlen := q.length_takeUntil_le_length hb
      simp only [SimpleGraph.Walk.length_append]
      nlinarith
    obtain ⟨w,hw,q',hq'⟩ := walk_backward H J f hgraph q hqs
    have hwmem : w ∈ S' ↔ f w ∈ S := hmem w (hw ▸ (show Close H (r*(t+1)) (f a) v from
      ⟨p.append q,by simp only [SimpleGraph.Walk.length_append]; nlinarith⟩))
    refine ⟨w,?_,hw⟩
    refine ⟨hself.mpr huv.1,hwmem.mpr (hw.symm ▸ huv.2.1),?_,q',hq'.trans_le hq⟩
    intro he
    exact huv.2.2.1 (he.symm ▸ hw)

def misTime (zeta : ℕ) : ℕ :=
  BlockColorProof.misProgram.program.rounds ⟨10,zeta⟩

def netRadius (zeta j : ℕ) : ℕ := (misTime zeta+1)*(2^(j+1)-2)

lemma netRadius_step (zeta j : ℕ) :
    netRadius zeta (j+1) = netRadius zeta j + 2^(j+1)*(misTime zeta+1) := by
  have hp : 2 ≤ 2^(j+1) := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by omega : 1 ≤ j+1)
  unfold netRadius
  rw [pow_succ 2 (j+1)]
  rw [show 2^(j+1)*2-2 = (2^(j+1)-2)+2^(j+1) by omega,Nat.mul_add]
  ring

def genericLeaders (A : Deterministic BlockColorProof.ColorParameters ℕ Bool)
    (zeta : ℕ) (col : V → ℕ) : ℕ → Finset V
  | 0 => univ
  | j+1 => (genericLeaders A zeta col j).filter fun v =>
      A.program.output (filteredPower H (2^(j+1)) (genericLeaders A zeta col j))
        ⟨10,zeta⟩ (fun _ => 0) col (fun _ _ => false) v = true

lemma genericLeaders_eq (zeta : ℕ) (col : V → ℕ) (j : ℕ) :
    genericLeaders H BlockColorProof.misProgram zeta col j = leaders H zeta col j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [genericLeaders,leaders,leaderStep,ih]

include hf in
lemma genericLeaders_local (A : Deterministic BlockColorProof.ColorParameters ℕ Bool)
    (zeta : ℕ) (col : V → ℕ)
    (hgraph : ∀ a b, J.Adj a b ↔ H.Adj (f a) (f b)) (j : ℕ) (a : W)
    (hall : ∀ v, Close H ((A.program.rounds ⟨10,zeta⟩+1)*(2^(j+1)-2)) (f a) v → ∃ u, f u = v) :
    a ∈ genericLeaders J A zeta (col ∘ f) j ↔ f a ∈ genericLeaders H A zeta col j := by
  let T := A.program.rounds ⟨10,zeta⟩
  induction j generalizing a with
  | zero => simp only [genericLeaders,mem_univ]
  | succ j ih =>
    have he : (T+1)*(2^(j+1+1)-2) = (T+1)*(2^(j+1)-2)+2^(j+1)*(T+1) := by
      have hp : 2 ≤ 2^(j+1) := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by omega : 1 ≤ j+1)
      rw [pow_succ 2 (j+1)]
      rw [show 2^(j+1)*2-2 = (2^(j+1)-2)+2^(j+1) by omega,Nat.mul_add]
      ring
    change ∀ v, Close H ((T+1)*(2^(j+1+1)-2)) (f a) v → ∃ u, f u = v at hall
    have hlocal : ∀ u, Close H (2^(j+1)*(T+1)) (f a) (f u) →
        (u ∈ genericLeaders J A zeta (col ∘ f) j ↔ f u ∈ genericLeaders H A zeta col j) := by
      intro u ⟨p,hp⟩
      apply ih u
      intro v ⟨q,hq⟩
      apply hall v
      refine ⟨p.append q,?_⟩
      simp only [SimpleGraph.Walk.length_append]
      change q.length ≤ (T+1)*(2^(j+1)-2) at hq
      omega
    have hself := hlocal a ⟨.nil,by simp⟩
    have hcover : ∀ v, Close H (2^(j+1)*(T+1)) (f a) v → ∃ u, f u = v := by
      intro v ⟨p,hp⟩
      exact hall v ⟨p,by omega⟩
    have hrun := power_run_local H J f hf A ⟨10,zeta⟩ (fun _ => 0) col
      (2^(j+1)) T (genericLeaders H A zeta col j) (genericLeaders J A zeta (col ∘ f) j)
      hgraph a hlocal hcover
    rw [show ((fun _ : V => (0:ℕ)) ∘ f) = (fun _ : W => 0) from rfl] at hrun
    have hout : A.program.output
        (filteredPower J (2^(j+1)) (genericLeaders J A zeta (col ∘ f) j)) ⟨10,zeta⟩
        (fun _ => 0) (col ∘ f) (fun _ _ => false) a =
      A.program.output (filteredPower H (2^(j+1)) (genericLeaders H A zeta col j)) ⟨10,zeta⟩
        (fun _ => 0) col (fun _ _ => false) (f a) := congrArg A.program.out hrun
    simp only [genericLeaders,mem_filter]
    rw [hself,hout]

include hf in
lemma leaders_local (zeta : ℕ) (col : V → ℕ)
    (hgraph : ∀ a b, J.Adj a b ↔ H.Adj (f a) (f b)) (j : ℕ) (a : W)
    (hall : ∀ v, Close H (netRadius zeta j) (f a) v → ∃ u, f u = v) :
    a ∈ leaders J zeta (col ∘ f) j ↔ f a ∈ leaders H zeta col j := by
  have h := genericLeaders_local H J f hf BlockColorProof.misProgram zeta col hgraph j a hall
  simpa only [genericLeaders_eq] using h


include hf in
lemma component_threshold_local (ell : ℕ) (a : W)
    (hgraph : ∀ a b, J.Adj a b ↔ H.Adj (f a) (f b))
    (hall : ∀ v, Close H (ell-1) (f a) v → ∃ u, f u = v) :
    ell ≤ (comp J a).card ↔ ell ≤ (comp H (f a)).card := by
  have hsub : (comp J a).image f ⊆ comp H (f a) := by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    obtain ⟨p⟩ := (mem_filter.mp hb).2
    obtain ⟨q,hq⟩ := walk_forward H J f (fun a b h => (hgraph a b).mp h) p
    exact mem_filter.mpr ⟨mem_univ _,q.reachable⟩
  have hball : ball H (ell-1) (f a) ⊆ (comp J a).image f := by
    intro v hv
    obtain ⟨p,hp⟩ := (mem_filter.mp hv).2
    obtain ⟨b,hb,q,hq⟩ := walk_backward H J f hgraph p (by
      intro c hc
      exact hall c ⟨p.takeUntil c hc,(p.length_takeUntil_le_length hc).trans hp⟩)
    exact mem_image.mpr ⟨b,mem_filter.mpr ⟨mem_univ _,q.reachable⟩,hb⟩
  have hc := card_image_of_injective (comp J a) hf
  have hupper := card_le_card hsub
  have hlower := (ball_card_lower H (ell-1) (f a)).trans (card_le_card hball)
  rw [hc] at hupper hlower
  omega

lemma dist_forward (hforward : ∀ a b, J.Adj a b → H.Adj (f a) (f b))
    {a b : W} (hr : J.Reachable a b) : H.dist (f a) (f b) ≤ J.dist a b := by
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_dist
  obtain ⟨q,hq⟩ := walk_forward H J f hforward p
  exact (H.dist_le q).trans_eq (hq.trans hp)

include hf in
lemma distance_local (R : ℕ) (a b : W)
    (hgraph : ∀ a b, J.Adj a b ↔ H.Adj (f a) (f b))
    (hall : ∀ v, Close H R (f a) v → ∃ u, f u = v)
    (hr : H.Reachable (f a) (f b)) (hd : H.dist (f a) (f b) ≤ R) :
    J.Reachable a b ∧ J.dist a b = H.dist (f a) (f b) := by
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_dist
  obtain ⟨c,hc,q,hq⟩ := walk_backward H J f hgraph p (by
    intro v hv
    exact hall v ⟨p.takeUntil v hv,by have h := p.length_takeUntil_le_length hv; omega⟩)
  have he : c = b := hf hc
  subst c
  refine ⟨q.reachable,le_antisymm ((J.dist_le q).trans_eq (hq.trans hp)) ?_⟩
  exact dist_forward H J f (fun a b h => (hgraph a b).mp h) q.reachable

include hf in
lemma nearest_local (R : ℕ) (S : Finset V) (S' : Finset W) (key : V → ℕ)
    (a b : W) (hgraph : ∀ a b, J.Adj a b ↔ H.Adj (f a) (f b))
    (hall : ∀ v, Close H R (f a) v → ∃ u, f u = v)
    (hmem : ∀ u, Close H R (f a) (f u) → (u ∈ S' ↔ f u ∈ S))
    (hb : Nearest H S key (f a) (f b)) (hd : H.dist (f a) (f b) ≤ R) :
    Nearest J S' (key ∘ f) a b := by
  have hdb := distance_local H J f hf R a b hgraph hall hb.2.1 hd
  obtain ⟨p,hp⟩ := hb.2.1.exists_walk_length_eq_dist
  have hbc : Close H R (f a) (f b) := ⟨p,hp.trans_le hd⟩
  refine ⟨(hmem b hbc).mpr hb.1,hdb.1,fun m hm hr => ?_⟩
  by_cases hdm : J.dist a m ≤ R
  · obtain ⟨q,hq⟩ := hr.exists_walk_length_eq_dist
    obtain ⟨q',hq'⟩ := walk_forward H J f (fun a b h => (hgraph a b).mp h) q
    have hmS := (hmem m ⟨q',by omega⟩).mp hm
    have hmin := Prod.Lex.toLex_le_toLex.mp (hb.2.2 (f m) hmS q'.reachable)
    have hdf := dist_forward H J f (fun a b h => (hgraph a b).mp h) hr
    apply Prod.Lex.toLex_le_toLex.mpr
    rcases hmin with h | ⟨h,hkey⟩
    · left; omega
    · by_cases he : J.dist a b = J.dist a m
      · exact Or.inr ⟨he,hkey⟩
      · left; omega
  · apply Prod.Lex.toLex_le_toLex.mpr
    left
    omega


end Locality
end BlockProof

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace BlockProof
section View
variable {V W : Type} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (J : SimpleGraph W) (f : W → V) (hf : Function.Injective f)

def fullRadius (ell zeta : ℕ) : ℕ := netRadius zeta (netDepth ell)+33*ell

def blockAlgorithm (ell zeta : ℕ) (col key : V → ℕ) : V → Option V :=
  voronoi H ell (finalLeaders H ell zeta col) key

include hf in
lemma blockAlgorithm_local (ell zeta : ℕ) (hell : 1 ≤ ell) (col key : V → ℕ)
    (hi : Function.Injective key) (hD : ∀ v, H.degree v ≤ 2)
    (hcol : Separates H (64*ell) zeta col)
    (hgraph : ∀ a b, J.Adj a b ↔ H.Adj (f a) (f b)) (a : W)
    (hall : ∀ v, Close H (fullRadius ell zeta) (f a) v → ∃ u, f u = v) :
    (blockAlgorithm J ell zeta (col ∘ f) (key ∘ f) a).map f =
      blockAlgorithm H ell zeta col key (f a) := by
  let S := finalLeaders H ell zeta col
  let S' := finalLeaders J ell zeta (col ∘ f)
  have hnet := finalLeaders_spec H hD ell zeta hell col hcol
  have hcover := hnet.2
  have hcomp := component_threshold_local H J f hf ell a hgraph (by
    intro v ⟨p,hp⟩
    exact hall v ⟨p,by unfold fullRadius; omega⟩)
  by_cases hlarge : ell ≤ (comp H (f a)).card
  · obtain ⟨l,hl⟩ := nearest_exists H S key (f a) (by
      obtain ⟨l,hl,p,hp⟩ := hcover (f a)
      exact ⟨l,hl,p.reachable⟩)
    have hdist : H.dist (f a) l ≤ 32*ell := by
      obtain ⟨m,hm,p,hp⟩ := hcover (f a)
      exact (nearest_dist_le H S key hl hm p.reachable).trans ((H.dist_le p).trans hp)
    obtain ⟨p,hp⟩ := hl.2.1.exists_walk_length_eq_dist
    obtain ⟨b,hb⟩ := hall l ⟨p,by unfold fullRadius; omega⟩
    have hball : ∀ v, Close H (32*ell) (f a) v → ∃ u, f u = v := by
      intro v ⟨q,hq⟩
      exact hall v ⟨q,by unfold fullRadius; omega⟩
    have hmem : ∀ u, Close H (32*ell) (f a) (f u) → (u ∈ S' ↔ f u ∈ S) := by
      intro u ⟨q,hq⟩
      apply leaders_local H J f hf zeta col hgraph (netDepth ell) u
      intro v ⟨w,hw⟩
      apply hall v
      refine ⟨q.append w,?_⟩
      simp only [SimpleGraph.Walk.length_append]
      unfold fullRadius
      omega
    have hl' : Nearest H S key (f a) (f b) := by simpa only [hb] using hl
    have hdist' : H.dist (f a) (f b) ≤ 32*ell := by simpa only [hb] using hdist
    have hn := nearest_local H J f hf (32*ell) S S' key a b hgraph hball hmem hl' hdist'
    have heJ := voronoi_eq J ell S' (key ∘ f) (hi.comp hf) (hcomp.mpr hlarge) hn
    have heH := voronoi_eq H ell S key hi hlarge hl
    change (voronoi J ell S' (key ∘ f) a).map f = voronoi H ell S key (f a)
    rw [heJ,heH,Option.map_some,hb]
  · have hshortH : (comp H (f a)).card < ell := by omega
    have hshortJ : (comp J a).card < ell := by omega
    have heH := (voronoi_none H ell S key (32*ell) hcover (f a)).mpr hshortH
    have heJ : voronoi J ell S' (key ∘ f) a = none := by
      unfold voronoi
      rw [dif_neg (by rintro ⟨h,_⟩; omega)]
    change (voronoi J ell S' (key ∘ f) a).map f = voronoi H ell S key (f a)
    rw [heJ,heH,Option.map_none]

end View
end BlockProof

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace BlockSnapshot

@[ext] structure Record where
  identity : ℕ
  members : Finset ℕ
  color : ℕ

def localRecords (initial : Bool) (id : ℕ) (inp : StageInput) : Finset Record :=
  univ.image fun i : Fin inp.groups.length =>
    ⟨Nat.pair id i.val,inp.groups.get i,if initial then Nat.pair id i.val else inp.color i.val⟩

def graph (R : Finset Record) : SimpleGraph R where
  Adj a b := a.val.identity.unpair.1 ≠ b.val.identity.unpair.1 ∧
    b.val.identity.unpair.1 ∈ a.val.members ∧ a.val.identity.unpair.1 ∈ b.val.members
  symm := ⟨by intro a b h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

def output (ell zeta id : ℕ) (R : Finset Record) (i : ℕ) : Option Key :=
  if h : ∃ a : R, a.val.identity = Nat.pair id i then
    (BlockProof.voronoi (graph R) ell
      (BlockProof.finalLeaders (graph R) ell zeta (fun a => a.val.color))
      (fun a => a.val.identity) h.choose).map (fun a => a.val.identity.unpair)
  else none

structure State where
  knowledge : StageParameters
  id : ℕ
  records : Finset Record

def program (initial : Bool) (palette : StageParameters → ℕ) :
    Deterministic StageParameters StageInput (ℕ → Option Key) where
  program := {
    State := State
    Msg := Finset Record
    rounds := fun k => BlockProof.netRadius (palette k) (BlockProof.netDepth k.ell)+33*k.ell
    init := fun k id inp _ => ⟨k,id,localRecords initial id inp⟩
    send := State.records
    step := fun s msgs => {s with records := s.records ∪ msgs.toFinset.biUnion id}
    out := fun s => output s.knowledge.ell (palette s.knowledge) s.id s.records }
  tape_independent := by intros; rfl

def flood {N : ℕ} (G : SimpleGraph (Fin N)) (start : Fin N → Finset Record) :
    ℕ → Fin N → Finset Record
  | 0,v => start v
  | t+1,v => flood G start t v ∪
      (((univ.filter (G.Adj v)).val.map fun w => flood G start t w).toFinset.biUnion id)

lemma flood_succ_mem {N : ℕ} (G : SimpleGraph (Fin N)) (start : Fin N → Finset Record)
    (t : ℕ) (v : Fin N) (z : Record) :
    z ∈ flood G start (t+1) v ↔ z ∈ flood G start t v ∨
      ∃ w, G.Adj v w ∧ z ∈ flood G start t w := by
  simp only [flood,mem_union,mem_biUnion,Multiset.mem_toFinset,Multiset.mem_map,
    mem_val,mem_filter,mem_univ,true_and,id_eq]
  aesop

lemma flood_mono {N : ℕ} (G : SimpleGraph (Fin N)) (start : Fin N → Finset Record)
    (v : Fin N) : Monotone (fun t => flood G start t v) := by
  apply monotone_nat_of_le_succ
  intro t z hz
  exact (flood_succ_mem G start t v z).mpr (Or.inl hz)

lemma flood_auth {N : ℕ} (G : SimpleGraph (Fin N)) (start : Fin N → Finset Record)
    (P : Record → Prop) (hstart : ∀ v z, z ∈ start v → P z) (t : ℕ) :
    ∀ v z, z ∈ flood G start t v → P z := by
  induction t with
  | zero => exact hstart
  | succ t ih =>
    intro v z hz
    rcases (flood_succ_mem G start t v z).mp hz with hz | ⟨w,hw,hz⟩
    · exact ih v z hz
    · exact ih w z hz

lemma flood_walk {N : ℕ} (G : SimpleGraph (Fin N)) (start : Fin N → Finset Record)
    (z : Record) {v u : Fin N} (w : G.Walk v u) (hz : z ∈ start u) :
    z ∈ flood G start w.length v := by
  induction w with
  | nil => exact hz
  | cons h w ih =>
    exact (flood_succ_mem G start w.length _ z).mpr (Or.inr ⟨_,h,ih hz⟩)

lemma program_run {N : ℕ} (G : SimpleGraph (Fin N)) (initial : Bool)
    (palette : StageParameters → ℕ) (k : StageParameters) (ids : Fin N → ℕ)
    (inp : Fin N → StageInput) (t : ℕ) (v : Fin N) :
    (program initial palette).program.run G k ids inp (fun _ _ => false) t v =
      ⟨k,ids v,flood G (fun v => localRecords initial (ids v) (inp v)) t v⟩ := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih]
    simp only [program,flood]


section Valid
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (col : Copy p → ℕ)

def record (a : Copy p) : Record :=
  ⟨Nat.pair (ids a.1) a.2.val,(group p a).image ids,col a⟩

include hi in
lemma key_inj : Function.Injective (fun a : Copy p => Nat.pair (ids a.1) a.2.val) := by
  intro a b he
  have h := Nat.pair_eq_pair.mp he
  have hv : a.1 = b.1 := hi h.1
  cases a with
  | mk v i =>
    cases b with
    | mk w j =>
      dsimp at hv
      subst w
      have heij : i = j := Fin.ext h.2
      subst j
      rfl

include hi in
lemma record_inj : Function.Injective (record ids p col) := by
  intro a b he
  exact key_inj ids hi p (congrArg Record.identity he)

include hi in
lemma graph_record (R : Finset Record) (a b : R) (u v : Copy p)
    (ha : record ids p col u = a.val) (hb : record ids p col v = b.val) :
    (graph R).Adj a b ↔ (virtualGraph p).Adj u v := by
  change (a.val.identity.unpair.1 ≠ b.val.identity.unpair.1 ∧
    b.val.identity.unpair.1 ∈ a.val.members ∧ a.val.identity.unpair.1 ∈ b.val.members) ↔ _
  rw [←ha,←hb]
  simp only [record,Nat.unpair_pair]
  change (ids u.1 ≠ ids v.1 ∧ ids v.1 ∈ (group p u).image ids ∧
    ids u.1 ∈ (group p v).image ids) ↔ _
  simp only [Finset.mem_image,ne_eq,hi.eq_iff]
  simp only [exists_eq_right]
  rfl

def hosted (v : Fin N) : Finset Record :=
  (univ.filter (fun a : Copy p => a.1 = v)).image (record ids p col)

lemma flood_hosted_auth (t : ℕ) (v : Fin N) (z : Record)
    (hz : z ∈ flood G (hosted ids p col) t v) : ∃ a, record ids p col a = z := by
  apply flood_auth G (hosted ids p col) (fun z => ∃ a, record ids p col a = z) ?_ t v z hz
  intro v z hz
  obtain ⟨a,ha,he⟩ := mem_image.mp hz
  exact ⟨a,he⟩

lemma hosted_mem (a : Copy p) : record ids p col a ∈ hosted ids p col a.1 := by
  exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,rfl⟩,rfl⟩

lemma copy_walk (q : ℝ) (hp : ValidPairing G x q p) {a b : Copy p}
    (w : (virtualGraph p).Walk a b) : ∃ u : G.Walk a.1 b.1, u.length = w.length := by
  induction w with
  | nil => exact ⟨.nil,rfl⟩
  | @cons a b c h w ih =>
    obtain ⟨u,hu⟩ := ih
    have hab := (hp.2.2.1 a b.1 h.2.1).1
    exact ⟨.cons hab u,by simp [hu]⟩

lemma flood_virtual_ball (q : ℝ) (hp : ValidPairing G x q p) (t : ℕ) (a b : Copy p)
    (hclose : Close (virtualGraph p) t a b) :
    record ids p col b ∈ flood G (hosted ids p col) t a.1 := by
  obtain ⟨w,hw⟩ := hclose
  obtain ⟨u,hu⟩ := copy_walk G x p q hp w
  exact flood_mono G (hosted ids p col) a.1 (hu.trans_le hw)
    (flood_walk G (hosted ids p col) (record ids p col b) u (hosted_mem ids p col b))


end Valid
end BlockSnapshot

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace BlockSnapshot

lemma snapshot_correct {N : ℕ} (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (p : Pairing N) (col : Copy p → ℕ) (ell zeta : ℕ) (hell : 1 ≤ ell)
    (hD : ∀ a : Copy p, (virtualGraph p).degree a ≤ 2)
    (hcol : Separates (virtualGraph p) (64*ell) zeta col)
    (R : Finset Record) (hauth : ∀ z ∈ R, ∃ a, record ids p col a = z)
    (a : Copy p) (hself : record ids p col a ∈ R)
    (hall : ∀ b, Close (virtualGraph p) (BlockProof.fullRadius ell zeta) a b →
      record ids p col b ∈ R) :
    output ell zeta (ids a.1) R a.2.val =
      (BlockProof.blockAlgorithm (virtualGraph p) ell zeta col
        (fun b => Nat.pair (ids b.1) b.2.val) a).map (copyKey ids) := by
  let f : R → Copy p := fun z => (hauth z.val z.property).choose
  have hfval (z : R) : record ids p col (f z) = z.val := (hauth z.val z.property).choose_spec
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    rw [←hfval z,←hfval w,he]
  have hgraph (z w : R) : (graph R).Adj z w ↔ (virtualGraph p).Adj (f z) (f w) :=
    graph_record ids hi p col R z w (f z) (f w) (hfval z) (hfval w)
  have hkey : (fun z : R => z.val.identity) = (fun b : Copy p => Nat.pair (ids b.1) b.2.val) ∘ f := by
    funext z
    exact (congrArg Record.identity (hfval z)).symm
  have hc : (fun z : R => z.val.color) = col ∘ f := by
    funext z
    exact (congrArg Record.color (hfval z)).symm
  have hex : ∃ z : R, z.val.identity = Nat.pair (ids a.1) a.2.val := by
    exact ⟨⟨record ids p col a,hself⟩,rfl⟩
  have hroot : f hex.choose = a := by
    apply key_inj ids hi p
    exact (congrArg Record.identity (hfval hex.choose)).trans hex.choose_spec
  have hcover : ∀ b, Close (virtualGraph p) (BlockProof.fullRadius ell zeta) (f hex.choose) b →
      ∃ z : R, f z = b := by
    intro b hb
    have hmem := hall b (by simpa only [hroot] using hb)
    refine ⟨⟨record ids p col b,hmem⟩,?_⟩
    exact record_inj ids hi p col (hfval ⟨record ids p col b,hmem⟩)
  have hl := BlockProof.blockAlgorithm_local (virtualGraph p) (graph R) f hf ell zeta hell
    col (fun b => Nat.pair (ids b.1) b.2.val) (key_inj ids hi p) hD hcol hgraph hex.choose hcover
  rw [←hkey,←hc,hroot] at hl
  have hmap : (copyKey ids) ∘ f = (fun z : R => z.val.identity.unpair) := by
    funext z
    have he := congrArg Record.identity (hfval z)
    rw [←he]
    simp only [Function.comp_def,record,Nat.unpair_pair,copyKey]
  have hfinal := congrArg (Option.map (copyKey ids)) hl
  rw [Option.map_map,hmap] at hfinal
  unfold output
  rw [dif_pos hex]
  exact hfinal

end BlockSnapshot

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace BlockSnapshot

lemma localRecords_stage {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (c : Option (Copy p → ℕ))
    (initial : Bool) (v : Fin N) :
    localRecords initial (ids v)
      (stageInput G ids x p none c (fun _ => false) (fun _ => none) v) =
    hosted ids p (fun a => if initial then Nat.pair (ids a.1) a.2.val else
      (c.map (fun f => f a)).getD 0) v := by
  ext z
  constructor
  · intro hz
    obtain ⟨i,hi,he⟩ := mem_image.mp hz
    have hi' : i.val < (p v).length := by simpa only [stageInput,List.length_map] using i.isLt
    let a : Copy p := ⟨v,⟨i.val,hi'⟩⟩
    apply mem_image.mpr
    refine ⟨a,mem_filter.mpr ⟨mem_univ _,rfl⟩,?_⟩
    rw [←he]
    apply Record.ext
    · rfl
    · simp [a,record,group,stageInput,List.get_eq_getElem]
      change image ids (p v)[i.val] = ((p v).map (image ids))[i.val]
      simp only [List.getElem_map]
    · simp [a,record,stageInput,hi']
  · intro hz
    obtain ⟨a,ha,he⟩ := mem_image.mp hz
    have hv : a.1 = v := (mem_filter.mp ha).2
    cases a with
    | mk w i =>
      dsimp at hv
      subst w
      apply mem_image.mpr
      let j : Fin (stageInput G ids x p none c (fun _ => false) (fun _ => none) v).groups.length :=
        ⟨i.val,by simpa only [stageInput,List.length_map] using i.isLt⟩
      refine ⟨j,mem_univ _,?_⟩
      rw [←he]
      apply Record.ext
      · rfl
      · simp [j,record,group,stageInput,List.get_eq_getElem]
      · simp [j,record,stageInput,i.isLt]

def colors {N : ℕ} (initial : Bool) (ids : Fin N → ℕ) (p : Pairing N)
    (c : Option (Copy p → ℕ)) (a : Copy p) : ℕ :=
  if initial then Nat.pair (ids a.1) a.2.val else (c.map (fun f => f a)).getD 0

lemma program_correct {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (x : Sym2 (Fin N) → ℝ) (p : Pairing N)
    (initial : Bool) (palette : StageParameters → ℕ) (c : Option (Copy p → ℕ))
    (k : StageParameters) (hell : 1 ≤ k.ell) (hp : ValidPairing G x k.q p)
    (hcol : Separates (virtualGraph p) (64*k.ell) (palette k) (colors initial ids p c)) :
    ∃ B : BlockAssignment p, ValidBlocks k.ell B ∧
      ReportsBlocks ids (execute (program initial palette) G k ids
        (stageInput G ids x p none c (fun _ => false) (fun _ => none))) B := by
  let cc := colors initial ids p c
  let key := fun a : Copy p => Nat.pair (ids a.1) a.2.val
  let B := BlockProof.blockAlgorithm (virtualGraph p) k.ell (palette k) cc key
  have hd := BlockProof.virtual_degree G x k.q p hp
  refine ⟨B,BlockProof.blocks_exist G x k.q p hp k.ell (palette k) hell cc hcol key
    (key_inj ids hi p),?_⟩
  intro a
  unfold execute SmoothedMIS.LocalAlg.output
  rw [program_run]
  change output k.ell (palette k) (ids a.1)
    (flood G (fun v => localRecords initial (ids v)
      (stageInput G ids x p none c (fun _ => false) (fun _ => none) v))
      (BlockProof.fullRadius k.ell (palette k)) a.1) a.2.val = _
  have hstart : (fun v => localRecords initial (ids v)
      (stageInput G ids x p none c (fun _ => false) (fun _ => none) v)) = hosted ids p cc := by
    funext v
    exact localRecords_stage G ids x p c initial v
  rw [hstart]
  apply snapshot_correct ids hi p cc k.ell (palette k) hell hd hcol
  · exact flood_hosted_auth G ids p cc _ _
  · exact flood_virtual_ball G ids x p cc k.q hp _ a a ⟨.nil,by simp⟩
  · exact fun b hb => flood_virtual_ball G ids x p cc k.q hp _ a b hb


end BlockSnapshot

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace BlockProof

lemma radius_bound (ell zeta : ℕ) (hell : 1 ≤ ell) :
    fullRadius ell zeta ≤ (32*(10^64+3)+33)*ell*(1+logStar zeta) := by
  have hdepth := (netDepth_bounds ell hell).2.2
  have hvol : 2^(netDepth ell+1)-2 ≤ 32*ell := by rw [pow_succ]; omega
  have hheight : BlockColorProof.height zeta ≤ logStar zeta := by
    calc
      _ ≤ BlockColorProof.height (max 2 zeta) := BlockColorProof.height_mono (le_max_right _ _)
      _ = _ := BlockColorProof.height_max_two zeta
  have ht : misTime zeta+1 ≤ (10^64+3)*(1+logStar zeta) := by
    change 2*BlockColorProof.height zeta+10^64+1 ≤ _
    nlinarith
  have hh := Nat.mul_le_mul hvol ht
  unfold fullRadius netRadius
  nlinarith

lemma radius_ID_bound (ell n B : ℕ) (hell : 1 ≤ ell) :
    fullRadius ell ((max 2 n)^B) ≤
      (32*(10^64+2*(B+1)+1)+33)*ell*logStar n := by
  have hdepth := (netDepth_bounds ell hell).2.2
  have hvol : 2^(netDepth ell+1)-2 ≤ 32*ell := by rw [pow_succ]; omega
  have hheight := BlockColorProof.height_ID_bound n B
  have hlog : 1 ≤ logStar n := le_max_left _ _
  have ht : misTime ((max 2 n)^B)+1 ≤ (10^64+2*(B+1)+1)*logStar n := by
    change 2*BlockColorProof.height ((max 2 n)^B)+10^64+1 ≤ _
    nlinarith
  have hh := Nat.mul_le_mul hvol ht
  unfold fullRadius netRadius
  nlinarith

end BlockProof

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace BlockSnapshot

lemma copies_le_N {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (q : ℝ) (p : Pairing N) (hp : ValidPairing G x q p) (v : Fin N) : (p v).length ≤ N := by
  have hn (i : Fin (p v).length) : (group p ⟨v,i⟩).Nonempty := by
    have h := hp.1 ⟨v,i⟩
    apply card_pos.mp
    omega
  let pick (i : Fin (p v).length) := (hn i).choose
  have hpick (i : Fin (p v).length) : pick i ∈ group p ⟨v,i⟩ := (hn i).choose_spec
  have hinj : Function.Injective pick := by
    intro i j hij
    have hactive := hp.2.2.1 ⟨v,i⟩ (pick i) (hpick i)
    have hunique := (hp.2.1 v (pick i)).mp hactive
    exact hunique.unique (hpick i) (hij ▸ hpick j)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective pick hinj

lemma copyKey_bound {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (q : ℝ) (p : Pairing N) (hp : ValidPairing G x q p) (n b : ℕ) (hn : N ≤ n)
    (ids : Fin N → ℕ) (hi : Identifiers n (b+1) ids) (a : Copy p) :
    Nat.pair (ids a.1) a.2.val < (max 2 n)^(2*(b+1)) := by
  have hi' : a.2.val < (max 2 n)^(b+1) := by
    apply lt_of_lt_of_le (a.2.isLt.trans_le ((copies_le_N G x q p hp a.1).trans hn))
    calc
      n ≤ max 2 n := le_max_right _ _
      _ = (max 2 n)^1 := (pow_one _).symm
      _ ≤ (max 2 n)^(b+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmax : max (ids a.1) a.2.val < (max 2 n)^(b+1) := max_lt (hi.2 a.1) hi'
  apply lt_of_lt_of_le (Nat.pair_lt_max_add_one_sq _ _)
  have hp := Nat.pow_le_pow_left (show max (ids a.1) a.2.val+1 ≤ (max 2 n)^(b+1) by omega) 2
  simpa only [←pow_mul,Nat.mul_comm] using hp

end BlockSnapshot

open BlockSnapshot

theorem solution :
    ∀ b : ℕ, ∃ (A0 A1 : Deterministic StageParameters StageInput (ℕ → Option Key)) (C : ℝ),
      0 < C ∧
      (∀ k, 2 ≤ k.ell → A0.program.rounds k ≤ budget C (k.ell * (logStar k.n : ℝ))) ∧
      (∀ k, 2 ≤ k.ell → A1.program.rounds k ≤ budget C (k.ell * (1 + (logStar k.zeta : ℝ)))) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : StageParameters),
        2 ≤ k.ell → boundedGraph G k.n k.degree →
        ∀ (x : Sym2 (Fin N) → ℝ) (p : Pairing N), ValidPairing G x k.q p →
          ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
            (∃ B : BlockAssignment p, ValidBlocks k.ell B ∧
              ReportsBlocks ids (execute A0 G k ids
                (stageInput G ids x p none none (fun _ => false) (fun _ => none))) B) ∧
            ∀ col : Copy p → ℕ, Separates (virtualGraph p) (64 * k.ell) k.zeta col →
              ∃ B : BlockAssignment p, ValidBlocks k.ell B ∧
                ReportsBlocks ids (execute A1 G k ids
                  (stageInput G ids x p none (some col) (fun _ => false) (fun _ => none))) B := by
  intro b
  let B := 2*(b+1)
  let C : ℕ := 32*(10^64+2*(B+1)+3)+33
  let A0 := program true (fun k => (max 2 k.n)^B)
  let A1 := program false StageParameters.zeta
  have hC : 0 < C := by dsimp [C]; omega
  refine ⟨A0,A1,(C:ℝ),by exact_mod_cast hC,?_,?_,?_⟩
  · intro k hk
    have ht := BlockProof.radius_ID_bound k.ell k.n B (by omega)
    have hcoef : 32*(10^64+2*(B+1)+1)+33 ≤ C := by dsimp [C]; omega
    have hr : A0.program.rounds k ≤ C*k.ell*logStar k.n :=
      ht.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoef))
    have hb : budget (C:ℝ) (k.ell*(logStar k.n:ℝ)) = C*k.ell*logStar k.n := by
      norm_num [budget,←Nat.cast_mul] <;> ring
    rwa [hb]
  · intro k hk
    have ht := BlockProof.radius_bound k.ell k.zeta (by omega)
    have hcoef : 32*(10^64+3)+33 ≤ C := by dsimp [C]; omega
    have hr : A1.program.rounds k ≤ C*k.ell*(1+logStar k.zeta) :=
      ht.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoef))
    have hb : budget (C:ℝ) (k.ell*(1+(logStar k.zeta:ℝ))) = C*k.ell*(1+logStar k.zeta) := by
      have he : (C:ℝ)*(k.ell*(1+(logStar k.zeta:ℝ))) =
          ((C*k.ell*(1+logStar k.zeta):ℕ):ℝ) := by push_cast; ring
      unfold budget
      rw [he,Nat.ceil_natCast]
    rwa [hb]
  · intro N G k hk hbound x p hp ids hi
    constructor
    · have hc : Separates (virtualGraph p) (64*k.ell) ((max 2 k.n)^B)
          (colors true ids p none) := by
        constructor
        · intro a
          exact copyKey_bound G x k.q p hp k.n b hbound.1 ids hi a
        · intro a a' haa hclose he
          exact haa (key_inj ids hi.1 p he)
      exact program_correct G ids hi.1 x p true (fun k => (max 2 k.n)^B) none k (by omega) hp hc
    · intro col hc
      apply program_correct G ids hi.1 x p false StageParameters.zeta (some col) k (by omega) hp
      have he : colors false ids p (some col) = col := by funext a; simp [colors]
      rw [he]
      exact hc

end
