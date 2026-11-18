-- Prove2me | solution 1 for DistributedRounding.weighted_average_coloring
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:19:18.171209+00:00
-- url     : https://prove2.me/submissions/9a4cf04b-71f9-40cc-a5ef-db430d3c90f2

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_DistributedRounding_WeightedColoring

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


open Classical Finset Polynomial
open FasterDistributedMatching.ApproximateMatching
open BlockColorProof
namespace WeightedColor

lemma weighted_family (s k : ℕ) :
    ∃ (q d : ℕ) (S : Fin k → Finset (Fin (nextPalette s k))),
      0 < q ∧ s*d < q ∧
      (∀ c, (S c).card = q) ∧ ∀ c b, c ≠ b → (S c ∩ S b).card ≤ d := by
  let d := Nat.clog 2 k
  obtain ⟨q,hprime,hq,hqu⟩ := Nat.exists_prime_lt_and_le_two_mul (s*d+1) (by omega)
  letI : Fact q.Prime := ⟨hprime⟩
  have hq2 : 2 ≤ q := hprime.two_le
  have hcard : Fintype.card (Fin k) ≤ Fintype.card (Fin d → ZMod q) := by
    simp only [Fintype.card_fin,Fintype.card_fun,ZMod.card]
    exact (Nat.le_pow_clog (by decide) k).trans (Nat.pow_le_pow_left hq2 d)
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hcard2 : Fintype.card (ZMod q × ZMod q) ≤ nextPalette s k := by
    simp only [Fintype.card_prod,ZMod.card]
    unfold nextPalette
    change q*q ≤ 4*(s*d+1)^2
    nlinarith
  let E : (ZMod q × ZMod q) ↪ Fin (nextPalette s k) :=
    (Fintype.equivFin (ZMod q × ZMod q)).toEmbedding.trans (Fin.castLEEmb hcard2)
  let S : Fin k → Finset (Fin (nextPalette s k)) := fun c =>
    univ.image fun x : ZMod q => E (x,(poly (enc c)).eval x)
  have hinj (c : Fin k) : Function.Injective (fun x : ZMod q => E (x,(poly (enc c)).eval x)) := by
    intro x y h
    exact congrArg Prod.fst (E.injective h)
  refine ⟨q,d,S,by omega,by omega,?_,?_⟩
  · intro c
    simp only [S,card_image_of_injective _ (hinj c),card_univ,ZMod.card]
  · intro c b hcb
    have heq : S c ∩ S b =
        (univ.filter (fun x : ZMod q => (poly (enc c)).eval x = (poly (enc b)).eval x)).image
          (fun x => E (x,(poly (enc c)).eval x)) := by
      ext i
      constructor
      · intro hi
        obtain ⟨x,hx,hxi⟩ := mem_image.mp (mem_inter.mp hi).1
        obtain ⟨y,hy,hyi⟩ := mem_image.mp (mem_inter.mp hi).2
        have he := E.injective (hxi.trans hyi.symm)
        have hxy : x = y := congrArg Prod.fst he
        have hev : (poly (enc c)).eval x = (poly (enc b)).eval x := by
          simpa only [hxy] using congrArg Prod.snd he
        exact mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,hev⟩,hxi⟩
      · intro hi
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
        refine mem_inter.mpr ⟨mem_image.mpr ⟨x,mem_univ _,rfl⟩,?_⟩
        exact mem_image.mpr ⟨x,mem_univ _,by rw [(mem_filter.mp hx).2]⟩
    rw [heq,card_image_of_injective _ (hinj c)]
    convert collisions (enc c) (enc b) (fun he => hcb (enc.injective he)) using 1 <;>
      congr 1 <;> ext x <;> simp

lemma nextPalette_mono_s (k : ℕ) : Monotone (fun s => nextPalette s k) := by
  intro a b hab
  unfold nextPalette
  exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.mul_le_mul_right (Nat.clog 2 k) hab) 1) 2)

lemma nextPalette_mono_k (s : ℕ) : Monotone (nextPalette s) := by
  intro a b hab
  unfold nextPalette
  exact BlockColorProof.nextPalette_mono s hab

lemma scaled_threshold (Q : ℕ) (hQ : 2 ≤ Q) : (2*Q)^64 ≤ Q^128 := by
  calc
    _ ≤ (Q^2)^64 := Nat.pow_le_pow_left (by nlinarith : 2*Q ≤ Q^2) 64
    _ = _ := by rw [←pow_mul]

lemma clog_scaled_threshold (Q : ℕ) (hQ : 2 ≤ Q) : Nat.clog 2 ((4*Q)^128) ≤ Q^128 := by
  have hclog : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow
    (show Q ≤ 2^Q from (Nat.lt_pow_self (by decide : 1 < 2)).le)
  have hbase : 4*Q ≤ Q^3 := by nlinarith [Nat.pow_le_pow_left hQ 2]
  have hpow : (4*Q)^128 ≤ (2^(Nat.clog 2 Q))^384 := by
    calc
      _ ≤ (Q^3)^128 := Nat.pow_le_pow_left hbase 128
      _ = Q^384 := by rw [←pow_mul]
      _ ≤ _ := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) Q) 384
  have hlog : Nat.clog 2 ((4*Q)^128) ≤ 384*Nat.clog 2 Q := by
    apply Nat.clog_le_of_le_pow
    simpa only [←pow_mul,mul_comm] using hpow
  have hbig : 384*Q ≤ Q^128 := by
    calc
      _ ≤ 2^127*Q := Nat.mul_le_mul_right Q (by norm_num)
      _ ≤ Q^127*Q := Nat.mul_le_mul_right Q (Nat.pow_le_pow_left hQ 127)
      _ = _ := (pow_succ Q 127).symm
  exact hlog.trans ((Nat.mul_le_mul_left 384 hclog).trans hbig)

lemma variable_two_step (Q k : ℕ) (hQ : 2 ≤ Q) (hk : 2 ≤ k) :
    nextPalette Q (nextPalette (2*Q) k) ≤ max (Q^128) (Nat.clog 2 k) := by
  calc
    _ ≤ nextPalette (2*Q) (nextPalette (2*Q) k) := nextPalette_mono_s _ (by omega)
    _ ≤ max ((2*Q)^64) (Nat.clog 2 k) := two_step_palette (2*Q) k (by omega) hk
    _ ≤ _ := max_le_max (scaled_threshold Q hQ) le_rfl

def compressedPalette (Q k : ℕ) : ℕ → ℕ
  | 0 => k
  | t+1 => nextPalette Q (nextPalette (2*Q) (compressedPalette (4*Q) k t))

lemma compressedPalette_ge_two (Q k t : ℕ) (hk : 2 ≤ k) : 2 ≤ compressedPalette Q k t := by
  cases t with
  | zero => exact hk
  | succ t =>
    change 2 ≤ 4*(Q * Nat.clog 2 (nextPalette (2*Q) (compressedPalette (4*Q) k t)) + 1)^2
    have h : 0 < (Q * Nat.clog 2 (nextPalette (2*Q) (compressedPalette (4*Q) k t)) + 1)^2 := by positivity
    omega

lemma compressedPalette_bound (Q k t : ℕ) (hQ : 2 ≤ Q) (hk : 2 ≤ k) :
    compressedPalette Q k t ≤ max (Q^128) ((Nat.clog 2)^[t] k) := by
  induction t generalizing Q with
  | zero => exact le_max_right _ _
  | succ t ih =>
    have hh := ih (4*Q) (by omega)
    have hlog : Nat.clog 2 (compressedPalette (4*Q) k t) ≤
        max (Q^128) ((Nat.clog 2)^[t+1] k) := by
      have hmono := Nat.clog_mono_right 2 hh
      have hmax : Nat.clog 2 (max ((4*Q)^128) ((Nat.clog 2)^[t] k)) =
          max (Nat.clog 2 ((4*Q)^128)) (Nat.clog 2 ((Nat.clog 2)^[t] k)) := by
        rcases le_total ((4*Q)^128) ((Nat.clog 2)^[t] k) with h | h
        · rw [max_eq_right h,max_eq_right (Nat.clog_mono_right 2 h)]
        · rw [max_eq_left h,max_eq_left (Nat.clog_mono_right 2 h)]
      rw [hmax] at hmono
      apply hmono.trans
      rw [Function.iterate_succ_apply']
      exact max_le_max (clog_scaled_threshold Q hQ) le_rfl
    apply le_trans (variable_two_step Q _ hQ (compressedPalette_ge_two _ _ _ hk))
    exact max_le (le_max_left _ _) hlog

lemma clog_height_terminal (k : ℕ) : (Nat.clog 2)^[height k] k ≤ 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k ≤ 1
    · rw [height,dif_pos hk]
      exact hk
    · have hk2 : 2 ≤ k := by omega
      rw [height,dif_neg hk,Nat.add_comm 1,Function.iterate_succ_apply]
      exact ih _ (clog_lt_self k hk2)

lemma compressedPalette_terminal (Q zeta : ℕ) (hQ : 2 ≤ Q) :
    compressedPalette Q (max 2 zeta) (logStar zeta) ≤ Q^128 := by
  have hb := compressedPalette_bound Q (max 2 zeta) (height (max 2 zeta)) hQ (le_max_left _ _)
  have ht := clog_height_terminal (max 2 zeta)
  have hp : 1 ≤ Q^128 := Nat.one_le_pow _ _ (by omega)
  rw [max_eq_left (ht.trans hp)] at hb
  simpa only [height_max_two] using hb

lemma weighted_choice {C A : Type} [Fintype C] [Fintype A]
    (S : C → Finset A) (s q d : ℕ) (hq : 0 < q) (hsd : s*d ≤ q)
    (hcard : ∀ c, (S c).card = q)
    (hinter : ∀ c b, c ≠ b → (S c ∩ S b).card ≤ d)
    (c : C) (ns : Finset C) (hns : c ∉ ns) (weight : C → ℝ)
    (hw : ∀ b ∈ ns, 0 ≤ weight b) :
    ∃ i ∈ S c, (s:ℝ)*(∑ b ∈ ns, if i ∈ S b then weight b else 0) ≤ ∑ b ∈ ns, weight b := by
  let total := ∑ b ∈ ns, weight b
  have ht : 0 ≤ total := sum_nonneg hw
  have hsum : (∑ i ∈ S c, ∑ b ∈ ns, if i ∈ S b then weight b else 0) ≤ (d:ℝ)*total := by
    rw [sum_comm]
    calc
      _ = ∑ b ∈ ns, ((S c ∩ S b).card:ℝ)*weight b := by
        apply sum_congr rfl
        intro b hb
        rw [←sum_filter]
        simp only [filter_mem_eq_inter,sum_const,nsmul_eq_mul]
      _ ≤ ∑ b ∈ ns, (d:ℝ)*weight b := by
        apply sum_le_sum
        intro b hb
        apply mul_le_mul_of_nonneg_right _ (hw b hb)
        exact_mod_cast hinter c b (fun he => hns (he.symm ▸ hb))
      _ = _ := (mul_sum ns (fun b => weight b) (d:ℝ)).symm
  apply exists_le_of_sum_le (card_pos.mp (by rw [hcard]; exact hq))
  calc
    _ = (s:ℝ)*(∑ i ∈ S c, ∑ b ∈ ns, if i ∈ S b then weight b else 0) := (mul_sum _ _ _).symm
    _ ≤ (s:ℝ)*((d:ℝ)*total) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg s)
    _ ≤ (q:ℝ)*total := by
      have hh : (s:ℝ)*(d:ℝ) ≤ (q:ℝ) := by exact_mod_cast hsd
      nlinarith
    _ = ∑ _ ∈ S c, total := by simp only [sum_const,nsmul_eq_mul,hcard]


lemma fixed_degree_family (s d k : ℕ) (hd : 1 ≤ d) (hk : k ≤ s^d) :
    ∃ (q : ℕ) (S : Fin k → Finset (Fin ((4*(s*d+1)^2)))),
      0 < q ∧ s*d < q ∧
      (∀ c, (S c).card = q) ∧ ∀ c b, c ≠ b → (S c ∩ S b).card ≤ d := by
  obtain ⟨q,hprime,hq,hqu⟩ := Nat.exists_prime_lt_and_le_two_mul (s*d+1) (by omega)
  letI : Fact q.Prime := ⟨hprime⟩
  have hq2 : 2 ≤ q := hprime.two_le
  have hcard : Fintype.card (Fin k) ≤ Fintype.card (Fin d → ZMod q) := by
    simp only [Fintype.card_fin,Fintype.card_fun,ZMod.card]
    exact hk.trans (Nat.pow_le_pow_left (by nlinarith : s ≤ q) d)
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hcard2 : Fintype.card (ZMod q × ZMod q) ≤ (4*(s*d+1)^2) := by
    simp only [Fintype.card_prod,ZMod.card]
    change q*q ≤ 4*(s*d+1)^2
    nlinarith
  let E : (ZMod q × ZMod q) ↪ Fin ((4*(s*d+1)^2)) :=
    (Fintype.equivFin (ZMod q × ZMod q)).toEmbedding.trans (Fin.castLEEmb hcard2)
  let S : Fin k → Finset (Fin ((4*(s*d+1)^2))) := fun c =>
    univ.image fun x : ZMod q => E (x,(poly (enc c)).eval x)
  have hinj (c : Fin k) : Function.Injective (fun x : ZMod q => E (x,(poly (enc c)).eval x)) := by
    intro x y h
    exact congrArg Prod.fst (E.injective h)
  refine ⟨q,S,by omega,by omega,?_,?_⟩
  · intro c
    simp only [S,card_image_of_injective _ (hinj c),card_univ,ZMod.card]
  · intro c b hcb
    have heq : S c ∩ S b =
        (univ.filter (fun x : ZMod q => (poly (enc c)).eval x = (poly (enc b)).eval x)).image
          (fun x => E (x,(poly (enc c)).eval x)) := by
      ext i
      constructor
      · intro hi
        obtain ⟨x,hx,hxi⟩ := mem_image.mp (mem_inter.mp hi).1
        obtain ⟨y,hy,hyi⟩ := mem_image.mp (mem_inter.mp hi).2
        have he := E.injective (hxi.trans hyi.symm)
        have hxy : x = y := congrArg Prod.fst he
        have hev : (poly (enc c)).eval x = (poly (enc b)).eval x := by
          simpa only [hxy] using congrArg Prod.snd he
        exact mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,hev⟩,hxi⟩
      · intro hi
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
        refine mem_inter.mpr ⟨mem_image.mpr ⟨x,mem_univ _,rfl⟩,?_⟩
        exact mem_image.mpr ⟨x,mem_univ _,by rw [(mem_filter.mp hx).2]⟩
    rw [heq,card_image_of_injective _ (hinj c)]
    convert collisions (enc c) (enc b) (fun he => hcb (enc.injective he)) using 1 <;>
      congr 1 <;> ext x <;> simp

lemma averaging_choice {C A : Type} [Fintype A]
    (S : C → Finset A) (s q d : ℕ) (hq : 0 < q) (hsd : s*d ≤ q)
    (hcard : ∀ c, (S c).card = q)
    (c : C) (ns : Finset C)
    (hinter : ∀ b ∈ ns, (S c ∩ S b).card ≤ d) (weight : C → ℝ)
    (hw : ∀ b ∈ ns, 0 ≤ weight b) :
    ∃ i ∈ S c, (s:ℝ)*(∑ b ∈ ns, if i ∈ S b then weight b else 0) ≤ ∑ b ∈ ns, weight b := by
  let total := ∑ b ∈ ns, weight b
  have ht : 0 ≤ total := sum_nonneg hw
  have hsum : (∑ i ∈ S c, ∑ b ∈ ns, if i ∈ S b then weight b else 0) ≤ (d:ℝ)*total := by
    rw [sum_comm]
    calc
      _ = ∑ b ∈ ns, ((S c ∩ S b).card:ℝ)*weight b := by
        apply sum_congr rfl
        intro b hb
        rw [←sum_filter]
        simp only [filter_mem_eq_inter,sum_const,nsmul_eq_mul]
      _ ≤ ∑ b ∈ ns, (d:ℝ)*weight b := by
        apply sum_le_sum
        intro b hb
        apply mul_le_mul_of_nonneg_right _ (hw b hb)
        exact_mod_cast hinter b hb
      _ = _ := (mul_sum ns (fun b => weight b) (d:ℝ)).symm
  apply exists_le_of_sum_le (card_pos.mp (by rw [hcard]; exact hq))
  calc
    _ = (s:ℝ)*(∑ i ∈ S c, ∑ b ∈ ns, if i ∈ S b then weight b else 0) := (mul_sum _ _ _).symm
    _ ≤ (s:ℝ)*((d:ℝ)*total) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg s)
    _ ≤ (q:ℝ)*total := by
      have hh : (s:ℝ)*(d:ℝ) ≤ (q:ℝ) := by exact_mod_cast hsd
      nlinarith
    _ = ∑ _ ∈ S c, total := by simp only [sum_const,nsmul_eq_mul,hcard]


structure PaletteFamily (s k n : ℕ) where
  q : ℕ
  d : ℕ
  sets : Fin k → Finset (Fin n)
  qpos : 0 < q
  precision : s*d ≤ q
  size : ∀ c, (sets c).card = q
  intersection : ∀ c b, c ≠ b → (sets c ∩ sets b).card ≤ d

def binaryFamily (s k : ℕ) : PaletteFamily s k (nextPalette s k) := Classical.choice (by
  obtain ⟨q,d,S,hq,hsd,hsize,hint⟩ := weighted_family s k
  exact ⟨⟨q,d,S,hq,hsd.le,hsize,hint⟩⟩)

def finalFamily (s : ℕ) : PaletteFamily s (s^128) (4*(s*128+1)^2) := Classical.choice (by
  obtain ⟨q,S,hq,hsd,hsize,hint⟩ := fixed_degree_family s 128 (s^128) (by decide) le_rfl
  exact ⟨⟨q,128,S,hq,hsd.le,hsize,hint⟩⟩)

def best {s k n : ℕ} (F : PaletteFamily s k n) (c : Fin k) (cost : Fin n → ℝ) : Fin n :=
  (exists_min_image (F.sets c) cost (card_pos.mp (by rw [F.size]; exact F.qpos))).choose

lemma best_mem {s k n : ℕ} (F : PaletteFamily s k n) (c : Fin k) (cost : Fin n → ℝ) :
    best F c cost ∈ F.sets c :=
  (exists_min_image (F.sets c) cost (card_pos.mp (by rw [F.size]; exact F.qpos))).choose_spec.1

lemma best_le {s k n : ℕ} (F : PaletteFamily s k n) (c : Fin k) (cost : Fin n → ℝ)
    (i : Fin n) (hi : i ∈ F.sets c) : cost (best F c cost) ≤ cost i :=
  (exists_min_image (F.sets c) cost (card_pos.mp (by rw [F.size]; exact F.qpos))).choose_spec.2 i hi


end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace WeightedColor

def candidateCost {s k n : ℕ} (F : PaletteFamily s k n) (c : ℕ)
    (msgs : Multiset (ℕ × ℝ)) (i : Fin n) : ℝ :=
  (msgs.map fun m => if h : m.1 < k then
    if m.1 ≠ c ∧ i ∈ F.sets ⟨m.1,h⟩ then m.2 else 0 else 0).sum

def reduce {s k n : ℕ} (F : PaletteFamily s k n) (c : ℕ) (msgs : Multiset (ℕ × ℝ)) : ℕ :=
  if h : c < k then (best F ⟨c,h⟩ (candidateCost F c msgs)).val else 0

lemma reduce_mem {s k n : ℕ} (F : PaletteFamily s k n) (c : ℕ)
    (msgs : Multiset (ℕ × ℝ)) (hc : c < k) :
    ∃ i : Fin n, reduce F c msgs = i.val ∧ i ∈ F.sets ⟨c,hc⟩ := by
  refine ⟨best F ⟨c,hc⟩ (candidateCost F c msgs),?_,best_mem F _ _⟩
  simp only [reduce,dif_pos hc]

section Graph
variable {V : Type} [Fintype V] (H : SimpleGraph V) {s k n : ℕ}
    (F : PaletteFamily s k n) (col : V → ℕ) (weight : V → V → ℝ)

def messages (v : V) : Multiset (ℕ × ℝ) :=
  (H.neighborFinset v).val.map fun u => (col u,weight v u)

def update (v : V) : ℕ := reduce F (col v) (messages H col weight v)

def defect (v : V) : ℝ := ∑ u ∈ H.neighborFinset v, if col u = col v then weight v u else 0

def totalWeight (v : V) : ℝ := ∑ u ∈ H.neighborFinset v, weight v u

lemma candidateCost_eq (hc : ∀ u, col u < k) (v : V) (c : ℕ) (i : Fin n) :
    candidateCost F c (messages H col weight v) i =
      ∑ u ∈ H.neighborFinset v, if col u ≠ c ∧ i ∈ F.sets ⟨col u,hc u⟩ then weight v u else 0 := by
  unfold candidateCost messages
  rw [Multiset.map_map]
  simp only [Function.comp_def]
  have he : (fun u : V =>
      (if h : (col u,weight v u).1 < k then
        if (col u,weight v u).1 ≠ c ∧ i ∈ F.sets ⟨(col u,weight v u).1,h⟩ then
          (col u,weight v u).2 else 0 else 0)) =
      (fun u => if col u ≠ c ∧ i ∈ F.sets ⟨col u,hc u⟩ then weight v u else 0) := by
    funext u
    rw [dif_pos (hc u)]
  change ((H.neighborFinset v).val.map (fun u => _)).sum = _
  rw [he]
  rfl

lemma update_lt (hc : ∀ u, col u < k) (v : V) : update H F col weight v < n := by
  obtain ⟨i,hi,hmem⟩ := reduce_mem F (col v) (messages H col weight v) (hc v)
  change reduce F (col v) (messages H col weight v) < n
  rw [hi]
  exact i.isLt

lemma update_cost_bound (hc : ∀ u, col u < k) (hw : ∀ v u, 0 ≤ weight v u) (v : V) :
    (s:ℝ)*candidateCost F (col v) (messages H col weight v)
      (best F ⟨col v,hc v⟩ (candidateCost F (col v) (messages H col weight v))) ≤ totalWeight H weight v := by
  let ns := (H.neighborFinset v).filter (fun u => col u ≠ col v)
  let sets := fun u : V => F.sets ⟨col u,hc u⟩
  have hchoice := averaging_choice sets s F.q F.d F.qpos F.precision
    (fun u => F.size ⟨col u,hc u⟩) v ns (by
      intro u hu
      convert F.intersection ⟨col v,hc v⟩ ⟨col u,hc u⟩
        (fun he => (mem_filter.mp hu).2 (congrArg Fin.val he).symm) using 1 <;>
        congr 1 <;> ext i <;> simp only [sets,mem_inter])
    (weight v) (fun u hu => hw v u)
  obtain ⟨i,hi,hb⟩ := hchoice
  have he (j : Fin n) : candidateCost F (col v) (messages H col weight v) j =
      ∑ u ∈ ns, if j ∈ sets u then weight v u else 0 := by
    rw [candidateCost_eq H F col weight hc,Finset.sum_filter]
    apply sum_congr rfl
    intro u hu
    by_cases hne : col u ≠ col v <;> simp [hne,ns,sets]
  have hbest := best_le F ⟨col v,hc v⟩ (candidateCost F (col v) (messages H col weight v)) i hi
  calc
    _ ≤ (s:ℝ)*candidateCost F (col v) (messages H col weight v) i :=
      mul_le_mul_of_nonneg_left hbest (Nat.cast_nonneg s)
    _ ≤ ∑ u ∈ ns, weight v u := by
      rw [he]
      convert hb using 1 <;> congr 1 <;> apply sum_congr rfl <;>
        intro u hu <;> split_ifs <;> rfl
    _ ≤ totalWeight H weight v := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun u _ _ => hw v u)

lemma update_defect_bound (hc : ∀ u, col u < k) (hw : ∀ v u, 0 ≤ weight v u) (v : V) :
    (s:ℝ)*defect H (update H F col weight) weight v ≤
      (s:ℝ)*defect H col weight v+totalWeight H weight v := by
  let chosen := fun u => best F ⟨col u,hc u⟩ (candidateCost F (col u) (messages H col weight u))
  have hval (u : V) : update H F col weight u = (chosen u).val := by
    unfold update reduce
    rw [dif_pos (hc u)]
  have hraw : defect H (update H F col weight) weight v ≤ defect H col weight v+
      candidateCost F (col v) (messages H col weight v) (chosen v) := by
    simp only [defect]
    rw [candidateCost_eq H F col weight hc,←sum_add_distrib]
    apply sum_le_sum
    intro u hu
    by_cases hnew : update H F col weight u = update H F col weight v
    · by_cases hold : col u = col v
      · simp [hnew,hold]
      · have hmem : chosen v ∈ F.sets ⟨col u,hc u⟩ := by
          have he : chosen u = chosen v := Fin.ext (by rw [←hval,←hval]; exact hnew)
          rw [←he]
          exact best_mem F _ _
        simp [hnew,hold,hmem]
    · simp only [hnew,ite_false]
      have hh := hw v u
      exact add_nonneg (by split_ifs <;> linarith) (by split_ifs <;> linarith)
  have hcost := update_cost_bound H F col weight hc hw v
  have hscale := mul_le_mul_of_nonneg_left hraw (Nat.cast_nonneg s)
  nlinarith


end Graph
end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
open BlockColorProof
namespace WeightedColor
section Compress
variable {V : Type} [Fintype V] (H : SimpleGraph V) (weight : V → V → ℝ)

def compressColors (Q k : ℕ) (col : V → ℕ) : ℕ → V → ℕ
  | 0 => col
  | t+1 =>
    let middle := update H (binaryFamily (2*Q) (compressedPalette (4*Q) k t))
      (compressColors (4*Q) k col t) weight
    update H (binaryFamily Q (nextPalette (2*Q) (compressedPalette (4*Q) k t))) middle weight

lemma compressColors_lt (Q k t : ℕ) (col : V → ℕ) (hc : ∀ v, col v < k) :
    ∀ v, compressColors H weight Q k col t v < compressedPalette Q k t := by
  induction t generalizing Q with
  | zero => exact hc
  | succ t ih =>
    have hm := update_lt H (binaryFamily (2*Q) (compressedPalette (4*Q) k t))
      (compressColors H weight (4*Q) k col t) weight (ih (4*Q))
    exact update_lt H (binaryFamily Q (nextPalette (2*Q) (compressedPalette (4*Q) k t))) _ weight hm

lemma compressColors_defect (Q k t : ℕ) (hQ : 0 < Q) (col : V → ℕ)
    (hc : ∀ v, col v < k) (hw : ∀ v u, 0 ≤ weight v u) : ∀ v,
    (Q:ℝ)*defect H (compressColors H weight Q k col t) weight v ≤
      (Q:ℝ)*defect H col weight v+2*totalWeight H weight v := by
  induction t generalizing Q with
  | zero =>
    intro v
    have ht : 0 ≤ totalWeight H weight v := sum_nonneg (fun u hu => hw v u)
    change _ ≤ _
    dsimp only [compressColors]
    linarith
  | succ t ih =>
    intro v
    let first := compressColors H weight (4*Q) k col t
    let middle := update H (binaryFamily (2*Q) (compressedPalette (4*Q) k t)) first weight
    have hfirst : ∀ v, first v < compressedPalette (4*Q) k t := compressColors_lt H weight _ _ _ col hc
    have hmiddle : ∀ v, middle v < nextPalette (2*Q) (compressedPalette (4*Q) k t) :=
      update_lt H _ first weight hfirst
    have h₁ := ih (4*Q) (by omega) v
    have h₂ := update_defect_bound H (binaryFamily (2*Q) (compressedPalette (4*Q) k t))
      first weight hfirst hw v
    have h₃ := update_defect_bound H (binaryFamily Q (nextPalette (2*Q) (compressedPalette (4*Q) k t)))
      middle weight hmiddle hw v
    change (Q:ℝ)*defect H (update H _ middle weight) weight v ≤ _
    change ((4*Q:ℕ):ℝ)*defect H first weight v ≤ _ at h₁
    push_cast at h₁ h₂
    nlinarith

def foldUpdates : List ℕ → ℕ → (V → ℕ) → ℕ × (V → ℕ)
  | [],k,col => (k,col)
  | s::rest,k,col => foldUpdates rest (nextPalette s k) (update H (binaryFamily s k) col weight)

lemma foldUpdates_append (as bs : List ℕ) (k : ℕ) (col : V → ℕ) :
    foldUpdates H weight (as++bs) k col =
      foldUpdates H weight bs (foldUpdates H weight as k col).1 (foldUpdates H weight as k col).2 := by
  induction as generalizing k col with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append,foldUpdates]
    exact ih _ _

def precisionList (Q : ℕ) : ℕ → List ℕ
  | 0 => []
  | t+1 => precisionList (4*Q) t ++ [2*Q,Q]

lemma precisionList_length (Q t : ℕ) : (precisionList Q t).length = 2*t := by
  induction t generalizing Q with
  | zero => rfl
  | succ t ih => simp only [precisionList,List.length_append,List.length_cons,List.length_nil,ih]; omega

lemma foldUpdates_precisions (Q k t : ℕ) (col : V → ℕ) :
    foldUpdates H weight (precisionList Q t) k col =
      (compressedPalette Q k t,compressColors H weight Q k col t) := by
  induction t generalizing Q with
  | zero => rfl
  | succ t ih =>
    rw [precisionList,foldUpdates_append,ih]
    rfl

end Compress

structure ColorState where
  ownID : ℕ
  weights : ℕ → ℝ
  palette : ℕ
  precisions : List ℕ
  color : ℕ

def colorProgram : Deterministic (ℕ × List ℕ) ((ℕ → ℝ) × ℕ) ℕ where
  program := {
    State := ColorState
    Msg := ℕ × ℕ
    rounds := fun k => k.2.length
    init := fun k id inp _ => ⟨id,inp.1,k.1,k.2,inp.2⟩
    send := fun s => (s.ownID,s.color)
    step := fun st msgs => match st.precisions with
      | [] => st
      | s::rest => {st with
          palette := nextPalette s st.palette,
          precisions := rest,
          color := reduce (binaryFamily s st.palette) st.color
            (msgs.map fun m => (m.2,st.weights m.1))}
    out := ColorState.color }
  tape_independent := by intros; rfl

lemma run_shift {V K I O : Type} [Fintype V] (H : SimpleGraph V)
    (A : Deterministic K I O) (k k' : K) (ids : V → ℕ) (inp inp' : V → I)
    (hfirst : ∀ v, A.program.run H k ids inp (fun _ _ => false) 1 v =
      A.program.run H k' ids inp' (fun _ _ => false) 0 v) (t : ℕ) :
    ∀ v, A.program.run H k ids inp (fun _ _ => false) (t+1) v =
      A.program.run H k' ids inp' (fun _ _ => false) t v := by
  induction t with
  | zero => exact hfirst
  | succ t ih =>
    intro v
    conv_lhs => rw [SmoothedMIS.LocalAlg.run]
    conv_rhs => rw [SmoothedMIS.LocalAlg.run]
    simp only [ih]

lemma colorProgram_run {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ)
    (weights : V → ℕ → ℝ) (col : V → ℕ) (ss : List ℕ) (k : ℕ) (v : V) :
    colorProgram.program.run H (k,ss) ids (fun v => (weights v,col v)) (fun _ _ => false) ss.length v =
      ⟨ids v,weights v,(foldUpdates H (fun v u => weights v (ids u)) ss k col).1,[],
        (foldUpdates H (fun v u => weights v (ids u)) ss k col).2 v⟩ := by
  induction ss generalizing k col with
  | nil => rfl
  | cons s ss ih =>
    let weight := fun v u => weights v (ids u)
    let next := update H (binaryFamily s k) col weight
    have hfirst (v : V) : colorProgram.program.run H (k,s::ss) ids (fun v => (weights v,col v))
        (fun _ _ => false) 1 v = colorProgram.program.run H (nextPalette s k,ss) ids
          (fun v => (weights v,next v)) (fun _ _ => false) 0 v := by
      have hn : univ.filter (H.Adj v) = H.neighborFinset v := by ext u; simp
      simp only [SmoothedMIS.LocalAlg.run,colorProgram,Multiset.map_map,Function.comp_def]
      rw [hn]
      rfl
    rw [List.length_cons,run_shift H colorProgram (k,s::ss) (nextPalette s k,ss) ids
      (fun v => (weights v,col v)) (fun v => (weights v,next v)) hfirst ss.length,ih]
    rfl

end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
open BlockColorProof
namespace WeightedColor

structure ColorRule where
  precision : ℕ
  input : ℕ
  output : ℕ
  family : PaletteFamily precision input output

section Rules
variable {V : Type} [Fintype V] (H : SimpleGraph V) (weight : V → V → ℝ)

def foldRules : List ColorRule → (V → ℕ) → (V → ℕ)
  | [],col => col
  | r::rs,col => foldRules rs (update H r.family col weight)

lemma foldRules_append (as bs : List ColorRule) (col : V → ℕ) :
    foldRules H weight (as++bs) col = foldRules H weight bs (foldRules H weight as col) := by
  induction as generalizing col with
  | nil => rfl
  | cons a as ih => exact ih _

end Rules

def binaryRules (Q k : ℕ) : ℕ → List ColorRule
  | 0 => []
  | t+1 =>
    let K := compressedPalette (4*Q) k t
    binaryRules (4*Q) k t ++
      [⟨2*Q,K,nextPalette (2*Q) K,binaryFamily (2*Q) K⟩,
       ⟨Q,nextPalette (2*Q) K,nextPalette Q (nextPalette (2*Q) K),binaryFamily Q (nextPalette (2*Q) K)⟩]

def fullRules (Q zeta : ℕ) : List ColorRule :=
  binaryRules Q (max 2 zeta) (logStar zeta) ++ [⟨Q,Q^128,4*(Q*128+1)^2,finalFamily Q⟩]

lemma binaryRules_length (Q k t : ℕ) : (binaryRules Q k t).length = 2*t := by
  induction t generalizing Q with
  | zero => rfl
  | succ t ih => simp only [binaryRules,List.length_append,List.length_cons,List.length_nil,ih]; omega

lemma fullRules_length (Q zeta : ℕ) : (fullRules Q zeta).length = 2*logStar zeta+1 := by
  simp only [fullRules,List.length_append,List.length_cons,List.length_nil,binaryRules_length]

lemma foldRules_binary {V : Type} [Fintype V] (H : SimpleGraph V) (weight : V → V → ℝ)
    (Q k t : ℕ) (col : V → ℕ) : foldRules H weight (binaryRules Q k t) col =
      compressColors H weight Q k col t := by
  induction t generalizing Q with
  | zero => rfl
  | succ t ih =>
    rw [binaryRules,foldRules_append,ih]
    rfl

lemma fullRules_correct {V : Type} [Fintype V] (H : SimpleGraph V) (weight : V → V → ℝ)
    (Q zeta : ℕ) (hQ : 2 ≤ Q) (col : V → ℕ) (hc : ∀ v, col v < zeta)
    (hw : ∀ v u, 0 ≤ weight v u) :
    (∀ v, foldRules H weight (fullRules Q zeta) col v < 4*(Q*128+1)^2) ∧
    ∀ v, (Q:ℝ)*defect H (foldRules H weight (fullRules Q zeta) col) weight v ≤
      (Q:ℝ)*defect H col weight v+3*totalWeight H weight v := by
  have hc' : ∀ v, col v < max 2 zeta := fun v => (hc v).trans_le (le_max_right _ _)
  let mid := compressColors H weight Q (max 2 zeta) col (logStar zeta)
  have hm : ∀ v, mid v < Q^128 := fun v =>
    (compressColors_lt H weight Q (max 2 zeta) (logStar zeta) col hc' v).trans_le
      (compressedPalette_terminal Q zeta hQ)
  have he : foldRules H weight (fullRules Q zeta) col = update H (finalFamily Q) mid weight := by
    rw [fullRules,foldRules_append,foldRules_binary]
    rfl
  rw [he]
  refine ⟨update_lt H (finalFamily Q) mid weight hm,fun v => ?_⟩
  have h₁ := compressColors_defect H weight Q (max 2 zeta) (logStar zeta) (by omega) col hc' hw v
  have h₂ := update_defect_bound H (finalFamily Q) mid weight hm hw v
  nlinarith

structure RuleState where
  ownID : ℕ
  weights : ℕ → ℝ
  rules : List ColorRule
  color : ℕ

def ruleProgram : Deterministic (List ColorRule) ((ℕ → ℝ) × ℕ) ℕ where
  program := {
    State := RuleState
    Msg := ℕ × ℕ
    rounds := List.length
    init := fun k id inp _ => ⟨id,inp.1,k,inp.2⟩
    send := fun s => (s.ownID,s.color)
    step := fun st msgs => match st.rules with
      | [] => st
      | r::rest => {st with
          rules := rest,
          color := reduce r.family st.color (msgs.map fun m => (m.2,st.weights m.1))}
    out := RuleState.color }
  tape_independent := by intros; rfl

lemma ruleProgram_run {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ)
    (weights : V → ℕ → ℝ) (col : V → ℕ) (rs : List ColorRule) (v : V) :
    ruleProgram.program.run H rs ids (fun v => (weights v,col v)) (fun _ _ => false) rs.length v =
      ⟨ids v,weights v,[],(foldRules H (fun v u => weights v (ids u)) rs col) v⟩ := by
  induction rs generalizing col with
  | nil => rfl
  | cons r rs ih =>
    let weight := fun v u => weights v (ids u)
    let next := update H r.family col weight
    have hfirst (v : V) : ruleProgram.program.run H (r::rs) ids (fun v => (weights v,col v))
        (fun _ _ => false) 1 v = ruleProgram.program.run H rs ids
          (fun v => (weights v,next v)) (fun _ _ => false) 0 v := by
      have hn : univ.filter (H.Adj v) = H.neighborFinset v := by ext u; simp
      simp only [SmoothedMIS.LocalAlg.run,ruleProgram,Multiset.map_map,Function.comp_def]
      rw [hn]
      rfl
    rw [List.length_cons,run_shift H ruleProgram (r::rs) rs ids
      (fun v => (weights v,col v)) (fun v => (weights v,next v)) hfirst rs.length,ih]
    rfl

end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace WeightedColor

section Affine
variable {F : Type} [Field F] [Fintype F]

def affine (a : Fˣ × F) (x : F) : F := (a.1:F)*x+a.2

lemma affine_bijective (a : Fˣ × F) : Function.Bijective (affine a) := by
  have hi : Function.Injective (affine a) := by
    intro x y h
    exact mul_left_cancel₀ a.1.ne_zero (add_right_cancel h)
  exact ⟨hi,Finite.surjective_of_injective hi⟩

lemma affine_collision_unique (a b : Fˣ × F) (hab : a ≠ b) (x y : F)
    (hx : affine a x = affine b x) (hy : affine a y = affine b y) : x = y := by
  by_contra hxy
  have hp : ((a.1:F)-(b.1:F))*(x-y) = 0 := by
    dsimp only [affine] at hx hy
    linear_combination hx-hy
  have hs : (a.1:F) = (b.1:F) := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hxy))
  have ht : a.2 = b.2 := by
    dsimp only [affine] at hx
    rw [hs] at hx
    exact add_left_cancel hx
  exact hab (Prod.ext (Units.ext hs) ht)

end Affine

lemma schedule_family (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ (p : ℕ) (schedule : Fin (4*(Q*128+1)^2) → Fin p → Fin p),
      1000*Q < p ∧ p ≤ 2002*Q ∧
      (∀ c, Function.Bijective (schedule c)) ∧
      ∀ c b, c ≠ b → (univ.filter (fun t => schedule c t = schedule b t)).card ≤ 1 := by
  obtain ⟨p,hprime,hp,hpu⟩ := Nat.exists_prime_lt_and_le_two_mul (1000*Q+1) (by omega)
  letI : Fact p.Prime := ⟨hprime⟩
  letI : NeZero p := ⟨hprime.ne_zero⟩
  have hsize : Fintype.card (Fin (4*(Q*128+1)^2)) ≤ Fintype.card ((ZMod p)ˣ × ZMod p) := by
    simp only [Fintype.card_fin,Fintype.card_prod,ZMod.card_units,ZMod.card]
    have h128 : Q*128+1 ≤ 129*Q := by omega
    have hsmall : 4*(Q*128+1)^2 ≤ 4*(129*Q)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left h128 2)
    have hprod : (1000*Q)*(1000*Q) ≤ (p-1)*p := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le hsize
  let E := (ZMod.finEquiv p).toEquiv
  let schedule := fun c : Fin (4*(Q*128+1)^2) => fun t : Fin p => E.symm (affine (enc c) (E t))
  refine ⟨p,schedule,by omega,by omega,?_,?_⟩
  · intro c
    exact E.symm.bijective.comp ((affine_bijective (enc c)).comp E.bijective)
  · intro c b hcb
    apply card_le_one.mpr
    intro x hx y hy
    apply E.injective
    have hx' : affine (enc c) (E x) = affine (enc b) (E x) := E.symm.injective ((mem_filter.mp hx).2)
    have hy' : affine (enc c) (E y) = affine (enc b) (E y) := E.symm.injective ((mem_filter.mp hy).2)
    exact affine_collision_unique (enc c) (enc b) (fun h => hcb (enc.injective h)) (E x) (E y) hx' hy'

end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace WeightedColor
section Commit
variable {V : Type} [Fintype V] (H : SimpleGraph V) (weight : V → V → ℝ)
    (col : V → ℕ) {p : ℕ} (schedule : V → Fin p → ℕ)

def commitBad (state : V → Option ℕ) (i : Fin p) (v : V) : ℝ :=
  ∑ u ∈ H.neighborFinset v, if col u ≠ col v ∧
    (state u = some (schedule v i) ∨ state u = none ∧ schedule u i = schedule v i)
    then weight v u else 0

def commits : ℕ → V → Option ℕ
  | 0 => fun _ => none
  | t+1 => fun v =>
      match commits t v with
      | some a => some a
      | none => if h : t < p then
          if (p:ℝ)*commitBad H weight col schedule (commits t) ⟨t,h⟩ v ≤ 3*totalWeight H weight v
          then some (schedule v ⟨t,h⟩) else none
        else none

lemma commits_succ_some (t : ℕ) (v : V) (a : ℕ)
    (h : commits H weight col schedule t v = some a) :
    commits H weight col schedule (t+1) v = some a := by
  rw [commits]
  dsimp only
  rw [h]

lemma commits_persistent (i j : ℕ) (hij : i ≤ j) (v : V) (a : ℕ)
    (h : commits H weight col schedule i v = some a) :
    commits H weight col schedule j v = some a := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction r with
  | zero => exact h
  | succ r ih => exact commits_succ_some H weight col schedule _ v a ih

lemma commits_none_earlier (i j : ℕ) (hij : i ≤ j) (v : V)
    (h : commits H weight col schedule j v = none) : commits H weight col schedule i v = none := by
  cases he : commits H weight col schedule i v with
  | none => rfl
  | some a =>
    have hp := commits_persistent H weight col schedule i j hij v a he
    rw [h] at hp
    contradiction

lemma occupied_card (state : ℕ → V → Option ℕ)
    (hpersist : ∀ i j, i ≤ j → ∀ u a, state i u = some a → state j u = some a)
    (hinj : ∀ v, Function.Injective (schedule v)) (v u : V) :
    (univ.filter (fun i : Fin p => state i.val u = some (schedule v i))).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  have hi' := (mem_filter.mp hi).2
  have hj' := (mem_filter.mp hj).2
  apply hinj v
  rcases le_total i.val j.val with hij | hij
  · have h := hpersist i.val j.val hij u (schedule v i) hi'
    exact Option.some.inj (h.symm.trans hj')
  · have h := hpersist j.val i.val hij u (schedule v j) hj'
    exact Option.some.inj (hi'.symm.trans h)

lemma conflict_card (state : ℕ → V → Option ℕ)
    (hpersist : ∀ i j, i ≤ j → ∀ u a, state i u = some a → state j u = some a)
    (hinj : ∀ v, Function.Injective (schedule v))
    (hpair : ∀ v u, col v ≠ col u → (univ.filter (fun i => schedule v i = schedule u i)).card ≤ 1)
    (v u : V) (hne : col u ≠ col v) :
    (univ.filter (fun i : Fin p => state i.val u = some (schedule v i) ∨
      state i.val u = none ∧ schedule u i = schedule v i)).card ≤ 2 := by
  let A := univ.filter (fun i : Fin p => state i.val u = some (schedule v i))
  let B := univ.filter (fun i : Fin p => schedule u i = schedule v i)
  have hsub : (univ.filter (fun i : Fin p => state i.val u = some (schedule v i) ∨
      state i.val u = none ∧ schedule u i = schedule v i)) ⊆ A ∪ B := by
    intro i hi
    rcases (mem_filter.mp hi).2 with h | h
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_univ _,h⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _,h.2⟩))
  have ha : A.card ≤ 1 := occupied_card schedule state hpersist hinj v u
  have hb : B.card ≤ 1 := hpair u v hne
  exact (card_le_card hsub).trans ((card_union_le A B).trans (by omega))

lemma commitBad_sum_bound (state : ℕ → V → Option ℕ)
    (hpersist : ∀ i j, i ≤ j → ∀ u a, state i u = some a → state j u = some a)
    (hinj : ∀ v, Function.Injective (schedule v))
    (hpair : ∀ v u, col v ≠ col u → (univ.filter (fun i => schedule v i = schedule u i)).card ≤ 1)
    (hw : ∀ v u, 0 ≤ weight v u) (v : V) :
    (∑ i : Fin p, commitBad H weight col schedule (state i.val) i v) ≤ 2*totalWeight H weight v := by
  unfold commitBad
  rw [sum_comm]
  calc
    _ ≤ ∑ u ∈ H.neighborFinset v, 2*weight v u := by
      apply sum_le_sum
      intro u hu
      by_cases hne : col u ≠ col v
      · simp only [ne_eq,hne,not_false_eq_true,true_and]
        rw [←sum_filter,sum_const,nsmul_eq_mul]
        have hc := conflict_card col schedule state hpersist hinj hpair v u hne
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hw v u)
      · simp only [hne,false_and,ite_false,sum_const_zero]
        have hh := hw v u
        positivity
    _ = _ := (mul_sum _ _ _).symm

lemma commits_all (hp : 0 < p) (hinj : ∀ v, Function.Injective (schedule v))
    (hpair : ∀ v u, col v ≠ col u → (univ.filter (fun i => schedule v i = schedule u i)).card ≤ 1)
    (hw : ∀ v u, 0 ≤ weight v u) (v : V) :
    ∃ a, commits H weight col schedule p v = some a := by
  cases he : commits H weight col schedule p v with
  | some a => exact ⟨a,rfl⟩
  | none =>
    have hbad (i : Fin p) : 3*totalWeight H weight v <
        (p:ℝ)*commitBad H weight col schedule (commits H weight col schedule i.val) i v := by
      have hpre := commits_none_earlier H weight col schedule i.val p i.isLt.le v he
      have hpost := commits_none_earlier H weight col schedule (i.val+1) p (by omega) v he
      rw [commits] at hpost
      dsimp only at hpost
      rw [hpre,dif_pos i.isLt] at hpost
      by_contra hn
      have hh : (p:ℝ)*commitBad H weight col schedule (commits H weight col schedule i.val) i v ≤
          3*totalWeight H weight v := by linarith
      rw [if_pos hh] at hpost
      contradiction
    have hne : (univ : Finset (Fin p)).Nonempty := ⟨⟨0,hp⟩,mem_univ _⟩
    have hstrict := sum_lt_sum_of_nonempty hne (fun i _ => hbad i)
    have hpersist : ∀ i j, i ≤ j → ∀ u a,
        commits H weight col schedule i u = some a → commits H weight col schedule j u = some a := by
      intro i j hij u a h
      exact commits_persistent H weight col schedule i j hij u a h
    have hupper := commitBad_sum_bound H weight col schedule (commits H weight col schedule) hpersist hinj hpair hw v
    have hT : 0 ≤ totalWeight H weight v := sum_nonneg (fun u hu => hw v u)
    have hpR : 0 < (p:ℝ) := by exact_mod_cast hp
    have hs : (p:ℝ)*(3*totalWeight H weight v) < (p:ℝ)*
        (∑ i : Fin p, commitBad H weight col schedule (commits H weight col schedule i.val) i v) := by
      simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←mul_sum] using hstrict
    have hh := mul_le_mul_of_nonneg_left hupper hpR.le
    nlinarith


lemma commits_origin (t : ℕ) (v : V) (a : ℕ)
    (ha : commits H weight col schedule t v = some a) :
    ∃ i : Fin p, i.val < t ∧ a = schedule v i ∧
      commits H weight col schedule i.val v = none ∧
      commits H weight col schedule (i.val+1) v = some a ∧
      (p:ℝ)*commitBad H weight col schedule (commits H weight col schedule i.val) i v ≤
        3*totalWeight H weight v := by
  induction t with
  | zero => simp [commits] at ha
  | succ t ih =>
    cases hs : commits H weight col schedule t v with
    | some b =>
      have hab : b = a := by
        have hh := ha
        rw [commits] at hh
        dsimp only at hh
        rw [hs] at hh
        exact Option.some.inj hh
      subst b
      obtain ⟨i,hi,h₁,h₂,h₃,h₄⟩ := ih hs
      exact ⟨i,by omega,h₁,h₂,h₃,h₄⟩
    | none =>
      have hh := ha
      rw [commits] at hh
      dsimp only at hh
      rw [hs] at hh
      split_ifs at hh with ht hb
      have he : a = schedule v ⟨t,ht⟩ := (Option.some.inj hh).symm
      exact ⟨⟨t,ht⟩,Nat.lt_succ_self t,he,hs,ha,hb⟩


end Commit
end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace WeightedColor

lemma neighbor_sum_swap {V : Type} [Fintype V] (H : SimpleGraph V) (f : V → V → ℝ) :
    (∑ v, ∑ u ∈ H.neighborFinset v, f v u) = ∑ v, ∑ u ∈ H.neighborFinset v, f u v := by
  have hn (v : V) : H.neighborFinset v = univ.filter (H.Adj v) := by ext u; simp
  simp only [hn,Finset.sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  rw [H.adj_comm]

section Charge
variable {V : Type} [Fintype V] {p : ℕ} (schedule : V → Fin p → ℕ)
    (state : ℕ → V → Option ℕ) (tau : V → Fin p) (out : V → ℕ)

lemma compatible_at
    (hpersist : ∀ i j, i ≤ j → ∀ u a, state i u = some a → state j u = some a)
    (hstart : ∀ v, state (tau v).val v = none)
    (hdone : ∀ v, state ((tau v).val+1) v = some (out v))
    (horigin : ∀ v, out v = schedule v (tau v))
    (v u : V) (horder : (tau u).val ≤ (tau v).val) (hnew : out u = out v) :
    state (tau v).val u = some (schedule v (tau v)) ∨
      state (tau v).val u = none ∧ schedule u (tau v) = schedule v (tau v) := by
  by_cases hlt : (tau u).val < (tau v).val
  · left
    have h := hpersist ((tau u).val+1) (tau v).val (by omega) u (out u) (hdone u)
    rwa [hnew,horigin v] at h
  · right
    have he : tau u = tau v := Fin.ext (by omega)
    constructor
    · simpa only [he] using hstart u
    · have hu := horigin u
      rw [he] at hu
      exact hu.symm.trans (hnew.trans (horigin v))

lemma final_different_charge (H : SimpleGraph V) (weight : V → V → ℝ) (col : V → ℕ)
    (hw : ∀ v u, 0 ≤ weight v u) (hsym : ∀ v u, weight v u = weight u v)
    (hpersist : ∀ i j, i ≤ j → ∀ u a, state i u = some a → state j u = some a)
    (hstart : ∀ v, state (tau v).val v = none)
    (hdone : ∀ v, state ((tau v).val+1) v = some (out v))
    (horigin : ∀ v, out v = schedule v (tau v)) :
    (∑ v, ∑ u ∈ H.neighborFinset v,
      if out u = out v ∧ col u ≠ col v then weight v u else 0) ≤
      2*∑ v, commitBad H weight col schedule (state (tau v).val) (tau v) v := by
  let B := fun v u => if col u ≠ col v ∧
      (state (tau v).val u = some (schedule v (tau v)) ∨
        state (tau v).val u = none ∧ schedule u (tau v) = schedule v (tau v))
      then weight v u else 0
  have hB (v u : V) : 0 ≤ B v u := by dsimp only [B]; split_ifs <;> first | exact hw v u | rfl
  have hpoint (v u : V) :
      (if out u = out v ∧ col u ≠ col v then weight v u else 0) ≤ B v u+B u v := by
    by_cases hm : out u = out v ∧ col u ≠ col v
    · rw [if_pos hm]
      rcases le_total (tau u).val (tau v).val with h | h
      · have hc := compatible_at schedule state tau out hpersist hstart hdone horigin v u h hm.1
        have hb : B v u = weight v u := if_pos ⟨hm.2,hc⟩
        rw [hb]
        linarith [hB u v]
      · have hc := compatible_at schedule state tau out hpersist hstart hdone horigin u v h hm.1.symm
        have hb : B u v = weight u v := if_pos ⟨Ne.symm hm.2,hc⟩
        rw [hb,hsym u v]
        linarith [hB v u]
    · rw [if_neg hm]
      exact add_nonneg (hB v u) (hB u v)
  calc
    _ ≤ ∑ v, ∑ u ∈ H.neighborFinset v, (B v u+B u v) :=
      sum_le_sum (fun v _ => sum_le_sum (fun u _ => hpoint v u))
    _ = (∑ v, ∑ u ∈ H.neighborFinset v, B v u)+
        (∑ v, ∑ u ∈ H.neighborFinset v, B u v) := by simp only [sum_add_distrib]
    _ = 2*∑ v, ∑ u ∈ H.neighborFinset v, B v u := by rw [←neighbor_sum_swap H B]; ring
    _ = _ := rfl


end Charge
end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace WeightedColor
section Result
variable {V : Type} [Fintype V] (H : SimpleGraph V) (weight : V → V → ℝ)
    (col : V → ℕ) {p : ℕ} (schedule : V → Fin p → ℕ)

def commitOutput (v : V) : ℕ := (commits H weight col schedule p v).getD 0

lemma commit_data (hp : 0 < p) (hinj : ∀ v, Function.Injective (schedule v))
    (hpair : ∀ v u, col v ≠ col u → (univ.filter (fun i => schedule v i = schedule u i)).card ≤ 1)
    (hw : ∀ v u, 0 ≤ weight v u) : ∃ tau : V → Fin p,
    (∀ v, commits H weight col schedule p v = some (commitOutput H weight col schedule v)) ∧
    ∀ v, commitOutput H weight col schedule v = schedule v (tau v) ∧
      commits H weight col schedule (tau v).val v = none ∧
      commits H weight col schedule ((tau v).val+1) v = some (commitOutput H weight col schedule v) ∧
      (p:ℝ)*commitBad H weight col schedule (commits H weight col schedule (tau v).val) (tau v) v ≤
        3*totalWeight H weight v := by
  have hout (v : V) : commits H weight col schedule p v = some (commitOutput H weight col schedule v) := by
    obtain ⟨a,ha⟩ := commits_all H weight col schedule hp hinj hpair hw v
    change commits H weight col schedule p v = some ((commits H weight col schedule p v).getD 0)
    rw [ha]
    rfl
  have horigin (v : V) := commits_origin H weight col schedule p v (commitOutput H weight col schedule v) (hout v)
  let tau := fun v => (horigin v).choose
  refine ⟨tau,hout,fun v => ?_⟩
  exact (horigin v).choose_spec.2

lemma commit_average_bound (Q : ℕ) (hp : 0 < p) (hQp : 6*Q ≤ p)
    (hinj : ∀ v, Function.Injective (schedule v))
    (hpair : ∀ v u, col v ≠ col u → (univ.filter (fun i => schedule v i = schedule u i)).card ≤ 1)
    (hbound : ∀ v i, schedule v i < p)
    (hw : ∀ v u, 0 ≤ weight v u) (hsym : ∀ v u, weight v u = weight u v)
    (hfirst : ∀ v, (Q:ℝ)*defect H col weight v ≤ 3*totalWeight H weight v) :
    (∀ v, commitOutput H weight col schedule v < p) ∧
    (Q:ℝ)*(∑ v, defect H (commitOutput H weight col schedule) weight v) ≤
      4*(∑ v, totalWeight H weight v) := by
  obtain ⟨tau,hout,hdata⟩ := commit_data H weight col schedule hp hinj hpair hw
  let out := commitOutput H weight col schedule
  have hpersist : ∀ i j, i ≤ j → ∀ u a,
      commits H weight col schedule i u = some a → commits H weight col schedule j u = some a := by
    intro i j hij u a h
    exact commits_persistent H weight col schedule i j hij u a h
  have hcharge := final_different_charge schedule (commits H weight col schedule) tau out H weight col hw hsym
    hpersist (fun v => (hdata v).2.1) (fun v => (hdata v).2.2.1) (fun v => (hdata v).1)
  let diff := ∑ v, ∑ u ∈ H.neighborFinset v, if out u = out v ∧ col u ≠ col v then weight v u else 0
  let total := ∑ v, totalWeight H weight v
  let bad := ∑ v, commitBad H weight col schedule (commits H weight col schedule (tau v).val) (tau v) v
  have hdiff0 : 0 ≤ diff := sum_nonneg (fun v _ => sum_nonneg (fun u _ => by split_ifs <;> first | exact hw v u | rfl))
  have hcost : (p:ℝ)*bad ≤ 3*total := by
    have hh := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => (hdata v).2.2.2)
    simpa only [←mul_sum] using hh
  have hlarge : 6*(Q:ℝ) ≤ (p:ℝ) := by exact_mod_cast hQp
  have hd : (Q:ℝ)*diff ≤ total := by
    have hs := mul_le_mul_of_nonneg_left hcharge (Nat.cast_nonneg p)
    have hh := mul_le_mul_of_nonneg_right hlarge hdiff0
    change (p:ℝ)*diff ≤ (p:ℝ)*(2*bad) at hs
    nlinarith
  have hsplit : (∑ v, defect H out weight v) ≤ (∑ v, defect H col weight v)+diff := by
    unfold defect
    dsimp only [diff]
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro v hv
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro u hu
    have hwu := hw v u
    by_cases h₁ : out u = out v <;> by_cases h₂ : col u = col v <;> simp [h₁,h₂,hwu]
  have hinit : (Q:ℝ)*(∑ v, defect H col weight v) ≤ 3*total := by
    have hh := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hfirst v)
    simpa only [←mul_sum] using hh
  refine ⟨fun v => ?_,?_⟩
  · rw [(hdata v).1]
    exact hbound v (tau v)
  · have hh := mul_le_mul_of_nonneg_left hsplit (Nat.cast_nonneg Q)
    nlinarith

end Result
end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace WeightedColor

inductive ColorAction where
  | recolor (rule : ColorRule)
  | commit (p : ℕ) (schedule : ℕ → ℕ → ℕ) (time : ℕ)

abbrev Configuration (V : Type) := (V → ℕ) × (V → Option ℕ)

section Actions
variable {V : Type} [Fintype V] (H : SimpleGraph V) (weight : V → V → ℝ)

def actionBad (col : V → ℕ) (selected : V → Option ℕ) (schedule : ℕ → ℕ → ℕ)
    (i : ℕ) (v : V) : ℝ :=
  ∑ u ∈ H.neighborFinset v, if col u ≠ col v ∧
    (selected u = some (schedule (col v) i) ∨
      selected u = none ∧ schedule (col u) i = schedule (col v) i) then weight v u else 0

def applyAction : ColorAction → Configuration V → Configuration V
  | .recolor r,(col,selected) => (update H r.family col weight,selected)
  | .commit p schedule i,(col,selected) =>
      (col,fun v => match selected v with
        | some a => some a
        | none => if (p:ℝ)*actionBad H weight col selected schedule i v ≤ 3*totalWeight H weight v
          then some (schedule (col v) i) else none)

def foldActions : List ColorAction → Configuration V → Configuration V
  | [],conf => conf
  | a::as,conf => foldActions as (applyAction H weight a conf)

lemma foldActions_append (as bs : List ColorAction) (conf : Configuration V) :
    foldActions H weight (as++bs) conf = foldActions H weight bs (foldActions H weight as conf) := by
  induction as generalizing conf with
  | nil => rfl
  | cons a as ih => exact ih _

lemma foldActions_recolor (rs : List ColorRule) (col : V → ℕ) (selected : V → Option ℕ) :
    foldActions H weight (rs.map ColorAction.recolor) (col,selected) = (foldRules H weight rs col,selected) := by
  induction rs generalizing col with
  | nil => rfl
  | cons r rs ih => exact ih _

end Actions

structure ActionState where
  ownID : ℕ
  weights : ℕ → ℝ
  actions : List ColorAction
  color : ℕ
  selected : Option ℕ

abbrev ActionInput := (ℕ → ℝ) × ℕ × Option ℕ

def actionProgram : Deterministic (List ColorAction) ActionInput ℕ where
  program := {
    State := ActionState
    Msg := ℕ × ℕ × Option ℕ
    rounds := List.length
    init := fun k id inp _ => ⟨id,inp.1,k,inp.2.1,inp.2.2⟩
    send := fun s => (s.ownID,s.color,s.selected)
    step := fun st msgs => match st.actions with
      | [] => st
      | a::rest => match a with
        | .recolor r => {st with
            actions := rest,
            color := reduce r.family st.color (msgs.map fun m => (m.2.1,st.weights m.1))}
        | .commit p schedule i => {st with
            actions := rest,
            selected := match st.selected with
              | some a => some a
              | none => if (p:ℝ)*(msgs.map (fun m =>
                  if m.2.1 ≠ st.color ∧
                    (m.2.2 = some (schedule st.color i) ∨
                      m.2.2 = none ∧ schedule m.2.1 i = schedule st.color i)
                  then st.weights m.1 else 0)).sum ≤
                    3*(msgs.map fun m => st.weights m.1).sum
                then some (schedule st.color i) else none}
    out := fun s => s.selected.getD 0 }
  tape_independent := by intros; rfl

lemma actionProgram_run {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ)
    (weights : V → ℕ → ℝ) (col : V → ℕ) (selected : V → Option ℕ)
    (as : List ColorAction) (v : V) :
    actionProgram.program.run H as ids (fun v => (weights v,col v,selected v)) (fun _ _ => false) as.length v =
      ⟨ids v,weights v,[],(foldActions H (fun v u => weights v (ids u)) as (col,selected)).1 v,
        (foldActions H (fun v u => weights v (ids u)) as (col,selected)).2 v⟩ := by
  induction as generalizing col selected with
  | nil => rfl
  | cons a as ih =>
    let weight := fun v u => weights v (ids u)
    let conf := applyAction H weight a (col,selected)
    have hfirst (v : V) : actionProgram.program.run H (a::as) ids (fun v => (weights v,col v,selected v))
        (fun _ _ => false) 1 v = actionProgram.program.run H as ids
          (fun v => (weights v,conf.1 v,conf.2 v)) (fun _ _ => false) 0 v := by
      have hn : univ.filter (H.Adj v) = H.neighborFinset v := by ext u; simp
      cases a with
      | recolor r =>
        simp only [SmoothedMIS.LocalAlg.run,actionProgram,Multiset.map_map,Function.comp_def]
        rw [hn]
        rfl
      | commit p schedule i =>
        simp only [SmoothedMIS.LocalAlg.run,actionProgram,Multiset.map_map,Function.comp_def]
        rw [hn]
        rfl
    rw [List.length_cons,run_shift H actionProgram (a::as) as ids
      (fun v => (weights v,col v,selected v)) (fun v => (weights v,conf.1 v,conf.2 v)) hfirst as.length,ih]
    rfl

end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace WeightedColor

def natSchedule {R p : ℕ} (schedule : Fin R → Fin p → Fin p) (c i : ℕ) : ℕ :=
  if hc : c < R then if hi : i < p then (schedule ⟨c,hc⟩ ⟨i,hi⟩).val else 0 else 0

lemma natSchedule_eq {R p : ℕ} (schedule : Fin R → Fin p → Fin p) (c : Fin R) (i : Fin p) :
    natSchedule schedule c.val i.val = (schedule c i).val := by
  simp only [natSchedule,dif_pos c.isLt,dif_pos i.isLt]

def commitActions (p : ℕ) (schedule : ℕ → ℕ → ℕ) (t : ℕ) : List ColorAction :=
  (List.range t).map fun i => .commit p schedule i

lemma commitActions_length (p : ℕ) (schedule : ℕ → ℕ → ℕ) (t : ℕ) :
    (commitActions p schedule t).length = t := by simp only [commitActions,List.length_map,List.length_range]

lemma foldActions_commit {V : Type} [Fintype V] (H : SimpleGraph V) (weight : V → V → ℝ)
    (col : V → ℕ) {p : ℕ} (schedule : V → Fin p → ℕ) (natSched : ℕ → ℕ → ℕ)
    (hnat : ∀ v i, natSched (col v) i.val = schedule v i) (t : ℕ) (ht : t ≤ p) :
    foldActions H weight (commitActions p natSched t) (col,fun _ => none) =
      (col,commits H weight col schedule t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have htp : t < p := by omega
    have ih := ih (by omega)
    have he : commitActions p natSched (t+1) = commitActions p natSched t ++ [.commit p natSched t] := by
      simp only [commitActions,List.range_succ,List.map_append,List.map_singleton]
    rw [he,foldActions_append,ih]
    change applyAction H weight (.commit p natSched t) (col,commits H weight col schedule t) = _
    have hbad (v : V) : actionBad H weight col (commits H weight col schedule t) natSched t v =
        commitBad H weight col schedule (commits H weight col schedule t) ⟨t,htp⟩ v := by
      unfold actionBad commitBad
      apply sum_congr rfl
      intro u hu
      rw [hnat v ⟨t,htp⟩,hnat u ⟨t,htp⟩]
    apply Prod.ext
    · rfl
    · funext v
      dsimp only [applyAction]
      rw [commits]
      dsimp only
      cases hs : commits H weight col schedule t v with
      | some a => simp only [hs]
      | none =>
        simp only [hs,dif_pos htp,hbad]
        rw [hnat v ⟨t,htp⟩]

end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching
namespace WeightedColor

structure ScheduleData (Q : ℕ) where
  p : ℕ
  schedule : Fin (4*(Q*128+1)^2) → Fin p → Fin p
  lower : 1000*Q < p
  upper : p ≤ 2002*Q
  bijective : ∀ c, Function.Bijective (schedule c)
  collision : ∀ c b, c ≠ b → (univ.filter (fun i => schedule c i = schedule b i)).card ≤ 1

def scheduleData (Q : ℕ) (hQ : 1 ≤ Q) : ScheduleData Q := Classical.choice (by
  obtain ⟨p,sched,hlo,hup,hbij,hcol⟩ := schedule_family Q hQ
  exact ⟨⟨p,sched,hlo,hup,hbij,hcol⟩⟩)

def averagePlan (Q zeta : ℕ) : List ColorAction :=
  if hQ : 1 ≤ Q then
    let D := scheduleData Q hQ
    (fullRules Q zeta).map ColorAction.recolor ++ commitActions D.p (natSchedule D.schedule) D.p
  else []

def averageProgram : Deterministic (ℕ × ℕ) ((ℕ → ℝ) × ℕ) ℕ where
  program := {
    State := ActionState
    Msg := actionProgram.program.Msg
    rounds := fun k => (averagePlan k.1 k.2).length
    init := fun k id inp tape => actionProgram.program.init (averagePlan k.1 k.2) id (inp.1,inp.2,none) tape
    send := actionProgram.program.send
    step := actionProgram.program.step
    out := actionProgram.program.out }
  tape_independent := by intros; rfl

lemma averageProgram_run {V : Type} [Fintype V] (H : SimpleGraph V)
    (k : ℕ × ℕ) (ids : V → ℕ) (inp : V → (ℕ → ℝ) × ℕ) (t : ℕ) : ∀ v,
    averageProgram.program.run H k ids inp (fun _ _ => false) t v =
      actionProgram.program.run H (averagePlan k.1 k.2) ids
        (fun v => ((inp v).1,(inp v).2,none)) (fun _ _ => false) t v := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    conv_lhs => rw [SmoothedMIS.LocalAlg.run]
    simp only [ih]
    rfl

lemma averageProgram_output {N : ℕ} (H : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (Q zeta : ℕ) (weights : Fin N → ℕ → ℝ) (col : Fin N → ℕ) (v : Fin N) :
    execute averageProgram H (Q,zeta) ids (fun v => (weights v,col v)) v =
      ((foldActions H (fun v u => weights v (ids u)) (averagePlan Q zeta) (col,fun _ => none)).2 v).getD 0 := by
  unfold execute SmoothedMIS.LocalAlg.output
  rw [averageProgram_run]
  change actionProgram.program.out (actionProgram.program.run H (averagePlan Q zeta) ids
    (fun v => (weights v,col v,none)) (fun _ _ => false) (averagePlan Q zeta).length v) = _
  rw [actionProgram_run]
  rfl

lemma averageProgram_rounds (Q zeta : ℕ) (hQ : 1 ≤ Q) :
    averageProgram.program.rounds (Q,zeta) = 2*logStar zeta+1+(scheduleData Q hQ).p := by
  change (averagePlan Q zeta).length = _
  rw [averagePlan,dif_pos hQ]
  simp only [List.length_append,List.length_map,fullRules_length,commitActions_length]

lemma averageProgram_time (Q zeta : ℕ) (hQ : 2 ≤ Q) :
    averageProgram.program.rounds (Q,zeta) ≤ 2004*(Q+logStar zeta) := by
  rw [averageProgram_rounds Q zeta (by omega)]
  have hp := (scheduleData Q (by omega : 1 ≤ Q)).upper
  omega

lemma averageProgram_correct {N : ℕ} (H : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (weights : Fin N → ℕ → ℝ) (col : Fin N → ℕ) (Q zeta : ℕ) (hQ : 2 ≤ Q)
    (hc : Proper H zeta col)
    (hw : ∀ v u, 0 ≤ weights v (ids u))
    (hsym : ∀ v u, weights v (ids u) = weights u (ids v)) :
    let out := execute averageProgram H (Q,zeta) ids (fun v => (weights v,col v))
    (∀ v, out v < 2002*Q) ∧
    (Q:ℝ)*(∑ v, defect H out (fun v u => weights v (ids u)) v) ≤
      4*(∑ v, totalWeight H (fun v u => weights v (ids u)) v) := by
  let weight := fun v u => weights v (ids u)
  let mid := foldRules H weight (fullRules Q zeta) col
  have hmid := fullRules_correct H weight Q zeta hQ col hc.1 hw
  have hzero (v : Fin N) : defect H col weight v = 0 := by
    apply sum_eq_zero
    intro u hu
    exact if_neg ((hc.2 v u ((SimpleGraph.mem_neighborFinset H v u).mp hu)).symm)
  have hfirst (v : Fin N) : (Q:ℝ)*defect H mid weight v ≤ 3*totalWeight H weight v := by
    have h := hmid.2 v
    rw [hzero] at h
    simpa only [mul_zero,zero_add] using h
  let D := scheduleData Q (by omega)
  let sched := fun v : Fin N => fun i : Fin D.p => (D.schedule ⟨mid v,hmid.1 v⟩ i).val
  have hp : 0 < D.p := by have h := D.lower; omega
  have hQp : 6*Q ≤ D.p := by have h := D.lower; omega
  have hinj (v : Fin N) : Function.Injective (sched v) := by
    intro i j he
    exact (D.bijective ⟨mid v,hmid.1 v⟩).1 (Fin.ext he)
  have hpair (v u : Fin N) (hne : mid v ≠ mid u) :
      (univ.filter (fun i => sched v i = sched u i)).card ≤ 1 := by
    have hh := D.collision ⟨mid v,hmid.1 v⟩ ⟨mid u,hmid.1 u⟩
      (fun he => hne (congrArg Fin.val he))
    convert hh using 1 <;> congr 1 <;> ext i <;> simp only [sched,mem_filter,mem_univ,true_and,Fin.val_inj]
  have hnat (v : Fin N) (i : Fin D.p) : natSchedule D.schedule (mid v) i.val = sched v i :=
    natSchedule_eq D.schedule ⟨mid v,hmid.1 v⟩ i
  have hfold : foldActions H weight (averagePlan Q zeta) (col,fun _ => none) =
      (mid,commits H weight mid sched D.p) := by
    rw [averagePlan,dif_pos (by omega : 1 ≤ Q),foldActions_append,foldActions_recolor]
    exact foldActions_commit H weight mid sched (natSchedule D.schedule) hnat D.p le_rfl
  have hout : execute averageProgram H (Q,zeta) ids (fun v => (weights v,col v)) =
      commitOutput H weight mid sched := by
    funext v
    rw [averageProgram_output,hfold]
    rfl
  have hres := commit_average_bound H weight mid sched Q hp hQp hinj hpair
    (fun v i => (D.schedule ⟨mid v,hmid.1 v⟩ i).isLt) hw hsym hfirst
  dsimp only
  rw [hout]
  exact ⟨fun v => (hres.1 v).trans_le D.upper,hres.2⟩


end WeightedColor

end

section


open Classical Finset
open FasterDistributedMatching.ApproximateMatching

theorem solution : DistributedRounding.WeightedAverageColoring := by
  refine ⟨WeightedColor.averageProgram,2004,by decide,WeightedColor.averageProgram_time,?_⟩
  intro N H ids weights col Q zeta hQ hc hw hsym
  have h := WeightedColor.averageProgram_correct H ids weights col Q zeta hQ hc hw hsym
  refine ⟨fun v => (h.1 v).trans_le (Nat.mul_le_mul_right Q (by decide : 2002 ≤ 2004)),?_⟩
  exact h.2

end
