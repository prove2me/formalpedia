-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.power_coloring
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:23:46.107689+00:00
-- url     : https://prove2.me/submissions/666243a0-6894-417d-918d-2716536d88d8

import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_line_simulation
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing
import Mathlib.NumberTheory.Bertrand

open Classical Finset Polynomial
open FasterDistributedMatching.ApproximateMatching

noncomputable section
namespace PowerColorProof

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

def colorProgram : Deterministic ColorParameters Unit ℕ where
  program := {
    State := ColorState
    Msg := ℕ
    rounds := fun k => 2*height k.palette
    init := fun k id _ _ => ⟨k.degree,max (k.degree^64) k.palette,id⟩
    send := ColorState.color
    step := fun s msgs => ⟨s.degree,paddedNext s.degree s.palette,
      localReduce s.degree s.palette s.color msgs.toFinset⟩
    out := ColorState.color }
  tape_independent := by intros; rfl

lemma colorProgram_invariant {V : Type} [Fintype V] (H : SimpleGraph V)
    (k : ColorParameters) (ids : V → ℕ) (hi : Function.Injective ids)
    (hid : ∀ v, ids v < k.palette) (hD : ∀ v, H.degree v ≤ k.degree) (t : ℕ) :
    let run := colorProgram.program.run H k ids (fun _ => ()) (fun _ _ => false)
    (∀ v, (run t v).degree = k.degree ∧
      (run t v).palette = (paddedNext k.degree)^[t] (max (k.degree^64) k.palette)) ∧
    Proper H ((paddedNext k.degree)^[t] (max (k.degree^64) k.palette))
      (fun v => (run t v).color) := by
  dsimp only
  induction t with
  | zero =>
    refine ⟨fun v => ⟨rfl,rfl⟩,fun v => (hid v).trans_le (le_max_right _ _),?_⟩
    intro v w hvw heq
    exact H.ne_of_adj hvw (hi heq)
  | succ t ih =>
    obtain ⟨hstate,hproper⟩ := ih
    let run := colorProgram.program.run H k ids (fun _ => ()) (fun _ _ => false)
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
    (k : ColorParameters) (ids : V → ℕ) (hi : Function.Injective ids)
    (hid : ∀ v, ids v < k.palette) (hD2 : 2 ≤ k.degree) (hD : ∀ v, H.degree v ≤ k.degree) :
    Proper H (k.degree^64)
      (colorProgram.program.output H k ids (fun _ => ()) (fun _ _ => false)) := by
  have h := colorProgram_invariant H k ids hi hid hD (2*height k.palette)
  have hp := palette_iterations k.degree k.palette hD2
  exact ⟨fun v => (h.2.1 v).trans_le hp,h.2.2⟩

lemma colorProgram_rounds (D n B : ℕ) :
    colorProgram.program.rounds ⟨D,(max 2 n)^B⟩ ≤ 2*(B+1)*logStar n := by
  change 2*height ((max 2 n)^B) ≤ _
  have h := Nat.mul_le_mul_left 2 (height_ID_bound n B)
  simpa only [mul_assoc] using h

lemma lineGraph_degree {N : ℕ} (G : SimpleGraph (Fin N)) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (e : G.edgeSet) : (lineGraph G).degree e ≤ 2*D := by
  obtain ⟨ev,he⟩ := e
  obtain ⟨⟨u,v⟩,rfl⟩ := ev.exists_rep
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  let S := (lineGraph G).neighborFinset ⟨s(u,v),he⟩
  have hinj : Set.InjOn (fun f : G.edgeSet => f.val) (S : Set G.edgeSet) :=
    fun _ _ _ _ h => Subtype.ext h
  have hsub : S.image (fun f : G.edgeSet => f.val) ⊆ G.incidenceFinset u ∪ G.incidenceFinset v := by
    intro f hf
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hf
    have h := (SimpleGraph.mem_neighborFinset _ _ _).mp ha
    obtain ⟨w,hw,hwa⟩ := h.2
    rcases Sym2.mem_iff.mp hw with hwu | hwv
    · exact mem_union_left _ ((G.mem_incidenceFinset u a.val).mpr ⟨a.property,hwu ▸ hwa⟩)
    · exact mem_union_right _ ((G.mem_incidenceFinset v a.val).mpr ⟨a.property,hwv ▸ hwa⟩)
  calc
    S.card = (S.image (fun f : G.edgeSet => f.val)).card := (card_image_iff.mpr hinj).symm
    _ ≤ (G.incidenceFinset u ∪ G.incidenceFinset v).card := card_le_card hsub
    _ ≤ (G.incidenceFinset u).card+(G.incidenceFinset v).card := card_union_le _ _
    _ ≤ 2*D := by rw [G.card_incidenceFinset_eq_degree,G.card_incidenceFinset_eq_degree]; nlinarith [hD u,hD v]

lemma close_zero {V : Type} (H : SimpleGraph V) (a b : V) : Close H 0 a b ↔ a = b := by
  constructor
  · rintro ⟨w,hw⟩
    exact w.eq_of_length_eq_zero (by omega)
  · intro h
    subst b
    exact ⟨.nil,by simp⟩

def ball {V : Type} [Fintype V] (H : SimpleGraph V) (r : ℕ) (a : V) : Finset V :=
  univ.filter (Close H r a)

lemma ball_zero {V : Type} [Fintype V] (H : SimpleGraph V) (a : V) : ball H 0 a = {a} := by
  ext b
  simp [ball,close_zero,eq_comm]

lemma ball_succ_subset {V : Type} [Fintype V] (H : SimpleGraph V) (r : ℕ) (a : V) :
    ball H (r+1) a ⊆ ball H r a ∪ (ball H r a).biUnion (fun v => H.neighborFinset v) := by
  intro c hc
  obtain ⟨w,hw⟩ := (mem_filter.mp hc).2
  have hlen : w.reverse.length ≤ r+1 := by simpa using hw
  cases hrev : w.reverse with
  | nil =>
    exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,.intro .nil (by simp)⟩)
  | @cons c b a h tail =>
    have ht : tail.length ≤ r := by
      rw [hrev,SimpleGraph.Walk.length_cons] at hlen
      omega
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨b,mem_filter.mpr ⟨mem_univ b,tail.reverse,by simpa using ht⟩,?_⟩
    simpa using h.symm

lemma card_ball {V : Type} [Fintype V] (H : SimpleGraph V) (D : ℕ)
    (hD : ∀ v, H.degree v ≤ D) (r : ℕ) (a : V) : (ball H r a).card ≤ (D+1)^r := by
  induction r with
  | zero => simp [ball_zero]
  | succ r ih =>
    calc
      _ ≤ (ball H r a ∪ (ball H r a).biUnion (fun v => H.neighborFinset v)).card :=
        card_le_card (ball_succ_subset H r a)
      _ ≤ (ball H r a).card+((ball H r a).biUnion (fun v => H.neighborFinset v)).card := card_union_le _ _
      _ ≤ (ball H r a).card+∑ v ∈ ball H r a, (H.neighborFinset v).card :=
        Nat.add_le_add_left card_biUnion_le _
      _ ≤ (ball H r a).card+∑ _ ∈ ball H r a, D := by
        apply Nat.add_le_add_left
        exact sum_le_sum fun v _ => by simpa using hD v
      _ = (D+1)*(ball H r a).card := by simp; ring
      _ ≤ (D+1)*(D+1)^r := Nat.mul_le_mul_left _ ih
      _ = (D+1)^(r+1) := by ring

lemma power_degree {V : Type} [Fintype V] (H : SimpleGraph V) (D : ℕ)
    (hD : ∀ v, H.degree v ≤ D) (r : ℕ) (a : V) :
    (graphPower H r).degree a ≤ (D+1)^r := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply le_trans (card_le_card (show (graphPower H r).neighborFinset a ⊆ ball H r a from ?_)) (card_ball H D hD r a)
  intro b hb
  have h := (SimpleGraph.mem_neighborFinset _ _ _).mp hb
  exact mem_filter.mpr ⟨mem_univ b,h.2⟩

def auxDegree (D ell : ℕ) : ℕ := (max 2 D)^(770*ell)
def idPalette (n b : ℕ) : ℕ := (max 2 n)^(2*(b+1))

lemma auxDegree_two (D ell : ℕ) (hell : 2 ≤ ell) : 2 ≤ auxDegree D ell := by
  have he : 1 ≤ 770*ell := by omega
  unfold auxDegree
  calc
    2 ≤ max 2 D := le_max_left _ _
    _ = (max 2 D)^1 := by rw [pow_one]
    _ ≤ (max 2 D)^(770*ell) := Nat.pow_le_pow_right (by omega : 0 < max 2 D) he

lemma power_line_degree {N : ℕ} (G : SimpleGraph (Fin N)) (D ell : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (hell : 2 ≤ ell) (e : G.edgeSet) :
    (graphPower (lineGraph G) (256*ell+1)).degree e ≤ auxDegree D ell := by
  have hb : 2 ≤ max 2 D := le_max_left _ _
  have hDle : D ≤ max 2 D := le_max_right _ _
  have hsq : 4 ≤ (max 2 D)^2 :=
    (by norm_num : 4 ≤ 2^2).trans (Nat.pow_le_pow_left hb 2)
  have hcube : 4*(max 2 D) ≤ (max 2 D)^3 := by
    simpa only [pow_succ] using Nat.mul_le_mul_right (max 2 D) hsq
  have hbase : 2*D+1 ≤ (max 2 D)^3 := by omega
  calc
    _ ≤ (2*D+1)^(256*ell+1) := power_degree (lineGraph G) (2*D) (lineGraph_degree G D hD) _ e
    _ ≤ ((max 2 D)^3)^(256*ell+1) := Nat.pow_le_pow_left hbase _
    _ = (max 2 D)^(3*(256*ell+1)) := by rw [pow_mul]
    _ ≤ (max 2 D)^(770*ell) := Nat.pow_le_pow_right (by omega : 0 < max 2 D) (by omega)

lemma edgeIdentity_bound {N : ℕ} (G : SimpleGraph (Fin N)) (n b : ℕ)
    (ids : Fin N → ℕ) (hi : Identifiers n (b+1) ids) (e : G.edgeSet) :
    edgeIdentity ids e.val < idPalette n b := by
  obtain ⟨ev,he⟩ := e
  obtain ⟨⟨u,v⟩,rfl⟩ := ev.exists_rep
  change Nat.pair (min (ids u) (ids v)) (max (ids u) (ids v)) < _
  have hmax : max (min (ids u) (ids v)) (max (ids u) (ids v)) < (max 2 n)^(b+1) := by
    exact max_lt (lt_of_le_of_lt (min_le_left _ _) (hi.2 u)) (max_lt (hi.2 u) (hi.2 v))
  apply lt_of_lt_of_le (Nat.pair_lt_max_add_one_sq _ _)
  have hp := Nat.pow_le_pow_left (show max (min (ids u) (ids v)) (max (ids u) (ids v))+1 ≤ (max 2 n)^(b+1) by omega) 2
  simpa only [idPalette,← pow_mul,Nat.mul_comm] using hp

end PowerColorProof

namespace EdgeWrapper

def hostedRecords {I : Type} (id : ℕ) (ns : Finset ℕ) (x : I) : Finset (ℕ × I) :=
  (ns.filter (fun j => id ≤ j)).image fun j => (Nat.pair (min id j) (max id j),x)

abbrev hostedUnits (id : ℕ) (ns : Finset ℕ) : Finset (ℕ × Unit) := hostedRecords id ns ()

def key (i j : ℕ) : ℕ := Nat.pair (min i j) (max i j)

def read {M : Type} (msgs : Multiset (M ⊕ (ℕ × (ℕ → Option ℕ)))) (id j : ℕ) : ℕ :=
  if h : ∃ f : ℕ → Option ℕ, Sum.inr (id,f) ∈ msgs then (h.choose j).getD 0 else 0

structure State {L : Type} (S : Deterministic L (Finset ℕ × Finset (ℕ × Unit)) (ℕ → Option ℕ)) where
  id : ℕ
  neighbors : Finset ℕ
  remaining : ℕ
  simulated : S.program.State
  result : ℕ → ℕ

def wrapper {K L : Type}
    (S : Deterministic L (Finset ℕ × Finset (ℕ × Unit)) (ℕ → Option ℕ)) (param : K → L) :
    Deterministic K (Finset ℕ) (ℕ → ℕ) where
  program := {
    State := State S
    Msg := S.program.Msg ⊕ (ℕ × (ℕ → Option ℕ))
    rounds := fun k => S.program.rounds (param k)+1
    init := fun k id ns _ => ⟨id,ns,S.program.rounds (param k),
      S.program.init (param k) id (ns,hostedUnits id ns) (fun _ => false),fun _ => 0⟩
    send := fun s => if 0 < s.remaining then Sum.inl (S.program.send s.simulated)
      else Sum.inr (s.id,S.program.out s.simulated)
    step := fun s msgs => if 0 < s.remaining then
      {s with remaining := s.remaining-1, simulated := (S.program.step s.simulated
        (msgs.filterMap fun m => match m with | .inl m => some m | .inr _ => none))}
      else {s with result := (fun j => if s.id ≤ j then (S.program.out s.simulated (key s.id j)).getD 0
        else read msgs j (key s.id j))}
    out := State.result }
  tape_independent := by intros; rfl

set_option backward.isDefEq.respectTransparency false in
lemma hostedUnits_eq {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (v : Fin N) :
    hostedUnits (ids v) (neighborIDs G ids v) = (lineInput G ids (fun _ => ()) v).2 := by
  classical
  letI : DecidableEq Unit := Classical.decEq _
  ext z
  constructor
  · intro hz
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
    obtain ⟨w,hw,hwj⟩ := mem_image.mp (mem_filter.mp hj).1
    have hvw : G.Adj v w := by simpa using hw
    have hid : ids v ≤ ids w := by simpa only [hwj] using (mem_filter.mp hj).2
    apply mem_image.mpr
    refine ⟨⟨s(v,w),G.mem_edgeSet.mpr hvw⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
    · refine ⟨Sym2.mem_mk_left v w,?_⟩
      intro u hu
      rcases Sym2.mem_iff.mp hu with rfl | rfl <;> omega
    · simp only [edgeIdentity,Sym2.lift_mk,hwj]
  · intro hz
    obtain ⟨e,he,rfl⟩ := mem_image.mp hz
    have hv := (mem_filter.mp he).2
    obtain ⟨w,hew⟩ := Sym2.mem_iff_exists.mp hv.1
    have hvw : G.Adj v w := G.mem_edgeSet.mp (by simpa only [hew] using e.property)
    apply mem_image.mpr
    refine ⟨ids w,mem_filter.mpr ⟨mem_image.mpr ⟨w,by simpa using hvw,rfl⟩,
      hv.2 w (by simpa only [hew] using Sym2.mem_mk_right v w)⟩,?_⟩
    rw [hew]
    simp only [edgeIdentity,Sym2.lift_mk]

def localInput {N : ℕ} (ids : Fin N → ℕ) (ns : Fin N → Finset ℕ) (v : Fin N) :
    Finset ℕ × Finset (ℕ × Unit) := (ns v,hostedUnits (ids v) (ns v))

lemma localInput_eq {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) :
    localInput ids (neighborIDs G ids) = lineInput G ids (fun _ => ()) := by
  funext v
  exact Prod.ext rfl (hostedUnits_eq G ids v)

lemma run_prefix {K L : Type}
    (S : Deterministic L (Finset ℕ × Finset (ℕ × Unit)) (ℕ → Option ℕ)) (param : K → L)
    {N : ℕ} (G : SimpleGraph (Fin N)) (k : K) (ids : Fin N → ℕ) (ns : Fin N → Finset ℕ)
    (t : ℕ) (ht : t ≤ S.program.rounds (param k)) : ∀ v,
    (wrapper S param).program.run G k ids ns (fun _ _ => false) t v =
      ⟨ids v,ns v,S.program.rounds (param k)-t,
        S.program.run G (param k) ids (localInput ids ns) (fun _ _ => false) t v,fun _ => 0⟩ := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    have hpos : 0 < S.program.rounds (param k)-t := by omega
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih (by omega)]
    simp only [wrapper]
    simp only [hpos,if_true,Multiset.filterMap_map,Function.comp_def]
    change (⟨ids v,ns v,S.program.rounds (param k)-t-1,
      S.program.step (S.program.run G (param k) ids (localInput ids ns) (fun _ _ => false) t v)
        (Multiset.filterMap (some ∘ (fun w => S.program.send
          (S.program.run G (param k) ids (localInput ids ns) (fun _ _ => false) t w)))
          (univ.filter (G.Adj v)).val),fun _ => 0⟩ : State S) = _
    rw [Multiset.filterMap_eq_map]
    congr 1

lemma read_neighbor {N : ℕ} {M : Type} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (outs : Fin N → ℕ → Option ℕ)
    (v w : Fin N) (hvw : G.Adj v w) (j : ℕ) :
    read (((univ.filter (G.Adj v)).val.map fun u =>
      (Sum.inr (ids u,outs u) : M ⊕ (ℕ × (ℕ → Option ℕ))))) (ids w) j =
        (outs w j).getD 0 := by
  unfold read
  have hex : ∃ f : ℕ → Option ℕ,
      Sum.inr (ids w,f) ∈ ((univ.filter (G.Adj v)).val.map fun u =>
        (Sum.inr (ids u,outs u) : M ⊕ (ℕ × (ℕ → Option ℕ)))) := by
    refine ⟨outs w,Multiset.mem_map.mpr ⟨w,?_,rfl⟩⟩
    simpa using hvw
  rw [dif_pos hex]
  have hm := hex.choose_spec
  obtain ⟨u,hu,heq⟩ := Multiset.mem_map.mp hm
  have hp := Sum.inr.inj heq
  have hid : u = w := hi (congrArg Prod.fst hp)
  have hf : outs w = hex.choose := by simpa only [hid] using congrArg Prod.snd hp
  rw [← hf]

lemma output_formula {K L : Type}
    (S : Deterministic L (Finset ℕ × Finset (ℕ × Unit)) (ℕ → Option ℕ)) (param : K → L)
    {N : ℕ} (G : SimpleGraph (Fin N)) (k : K) (ids : Fin N → ℕ) (ns : Fin N → Finset ℕ)
    (v : Fin N) (j : ℕ) :
    execute (wrapper S param) G k ids ns v j =
      if ids v ≤ j then
        (S.program.output G (param k) ids (localInput ids ns) (fun _ _ => false) v (key (ids v) j)).getD 0
      else read ((univ.filter (G.Adj v)).val.map fun u =>
        (Sum.inr (ids u,S.program.output G (param k) ids (localInput ids ns) (fun _ _ => false) u) :
          S.program.Msg ⊕ (ℕ × (ℕ → Option ℕ)))) j (key (ids v) j) := by
  unfold execute SmoothedMIS.LocalAlg.output
  change (wrapper S param).program.out
    ((wrapper S param).program.run G k ids ns (fun _ _ => false) (S.program.rounds (param k)+1) v) j = _
  rw [SmoothedMIS.LocalAlg.run]
  simp only [run_prefix S param G k ids ns _ le_rfl]
  simp only [wrapper,Nat.sub_self,Nat.lt_irrefl,if_false]

lemma edge_output {K L : Type}
    (S : Deterministic L (Finset ℕ × Finset (ℕ × Unit)) (ℕ → Option ℕ)) (param : K → L)
    {N : ℕ} (G : SimpleGraph (Fin N)) (k : K) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (colors : G.edgeSet → ℕ)
    (hS : ∀ (e : G.edgeSet) (u : Fin N), HostsEdge ids e.val u →
      S.program.output G (param k) ids (lineInput G ids (fun _ => ())) (fun _ _ => false) u
        (edgeIdentity ids e.val) = some (colors e))
    (v w : Fin N) (hvw : G.Adj v w) :
    execute (wrapper S param) G k ids (neighborIDs G ids) v (ids w) =
      colors ⟨s(v,w),G.mem_edgeSet.mpr hvw⟩ := by
  rw [output_formula,localInput_eq]
  let e : G.edgeSet := ⟨s(v,w),G.mem_edgeSet.mpr hvw⟩
  have hk : key (ids v) (ids w) = edgeIdentity ids e.val := rfl
  by_cases hv : ids v ≤ ids w
  · have hhost : HostsEdge ids e.val v := by
      refine ⟨Sym2.mem_mk_left v w,?_⟩
      intro u hu
      rcases Sym2.mem_iff.mp hu with rfl | rfl <;> omega
    rw [if_pos hv,hk,hS e v hhost]
    rfl
  · have hhost : HostsEdge ids e.val w := by
      refine ⟨Sym2.mem_mk_right v w,?_⟩
      intro u hu
      rcases Sym2.mem_iff.mp hu with rfl | rfl <;> omega
    rw [if_neg hv,read_neighbor G ids hi _ v w hvw,hk,hS e w hhost]
    rfl

end EdgeWrapper

namespace ColorIdentityProof

def ends (j : ℕ) : Finset ℕ := {j.unpair.1,j.unpair.2}
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)

lemma ends_key (e : Sym2 (Fin N)) : ends (edgeIdentity ids e) = e.toFinset.image ids := by
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  by_cases h : ids u ≤ ids v
  · simp [ends,edgeIdentity,Sym2.toFinset_mk_eq,min_eq_left h,max_eq_right h]
  · simp [ends,edgeIdentity,Sym2.toFinset_mk_eq,min_eq_right (le_of_not_ge h),
      max_eq_left (le_of_not_ge h),pair_comm]

lemma mem_ends_key (hi : Function.Injective ids) (e : Sym2 (Fin N)) (v : Fin N) :
    ids v ∈ ends (edgeIdentity ids e) ↔ v ∈ e := by
  rw [ends_key]
  constructor
  · intro hm
    obtain ⟨w,hw,h⟩ := mem_image.mp hm
    exact hi h ▸ (Sym2.mem_toFinset.mp hw)
  · intro h
    exact mem_image.mpr ⟨v,Sym2.mem_toFinset.mpr h,rfl⟩

lemma edgeIdentity_injective (hi : Function.Injective ids) : Function.Injective (edgeIdentity ids) := by
  intro e f hef
  apply Sym2.ext
  intro v
  rw [← mem_ends_key ids hi e v, ← mem_ends_key ids hi f v,hef]

lemma edgeKey_injective (hi : Function.Injective ids) :
    Function.Injective (fun e : G.edgeSet => edgeIdentity ids e.val) := by
  intro e f h
  apply Subtype.ext
  exact edgeIdentity_injective ids hi h


end ColorIdentityProof

namespace PowerColorProof

def parameters (b : ℕ) (k : Bounds × ℕ) : ColorParameters × ℕ :=
  (⟨auxDegree k.1.degree k.2,idPalette k.1.n b⟩,256*k.2+1)

end PowerColorProof

open PowerColorProof

theorem solution :
    ∀ b : ℕ, ∃ (A : Deterministic (Bounds × ℕ) (Finset ℕ) (ℕ → ℕ)) (C : ℝ) (a : ℕ),
      0 < C ∧ 1 ≤ a ∧
      (∀ k ell, 2 ≤ ell → A.program.rounds (k,ell) ≤ budget C (ell * (logStar k.n : ℝ))) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds) (ell : ℕ),
        2 ≤ ell → boundedGraph G k.n k.degree →
        ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
          ∃ chi : Sym2 (Fin N) → ℕ,
            (∀ u v, G.Adj u v →
              execute A G (k,ell) ids (neighborIDs G ids) u (ids v) = chi s(u,v) ∧
              execute A G (k,ell) ids (neighborIDs G ids) v (ids u) = chi s(u,v)) ∧
            Proper (graphPower (lineGraph G) (256 * ell + 1))
              ((max 2 k.degree) ^ (a * ell)) (fun e => chi e.val) := by
  intro b
  obtain ⟨C,hC,hLine⟩ := line_simulation
  obtain ⟨S,hSr,hSo⟩ := hLine ColorParameters Unit ℕ colorProgram
  let B := 2*(b+1)
  let C0 := C*300*(2*(B+1)+1)+1
  let param := parameters b
  let A := EdgeWrapper.wrapper S param
  refine ⟨A,(C0 : ℝ),49280,by exact_mod_cast (show 0 < C0 by dsimp [C0]; omega),by decide,?_,?_⟩
  · intro k ell hell
    have hR := hSr (param (k,ell)).1 (param (k,ell)).2
    have hT : colorProgram.program.rounds (param (k,ell)).1 ≤ 2*(B+1)*logStar k.n :=
      colorProgram_rounds (auxDegree k.degree ell) k.n B
    have hL : 1 ≤ logStar k.n := le_max_left _ _
    have hnat : A.program.rounds (k,ell) ≤ C0*ell*logStar k.n := by
      change S.program.rounds (param (k,ell))+1 ≤ _
      calc
        _ ≤ C*(256*ell+3)*(2*(B+1)*logStar k.n+1)+1 := by
          exact Nat.add_le_add_right (hR.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hT 1))) 1
        _ ≤ C*(300*ell)*((2*(B+1)+1)*logStar k.n)+1 := by
          gcongr
          · omega
          · nlinarith
        _ ≤ C0*ell*logStar k.n := by
          dsimp [C0]
          have hpos : 1 ≤ ell*logStar k.n := by nlinarith
          nlinarith
    have hb : budget (C0 : ℝ) (ell*(logStar k.n : ℝ)) = C0*ell*logStar k.n := by
      norm_num [budget,← Nat.cast_mul] <;> ring
    rw [hb]
    exact hnat
  · intro N G k ell hell hG ids hi
    let H := graphPower (lineGraph G) (256*ell+1)
    let par := (parameters b (k,ell)).1
    let edgeIDs : G.edgeSet → ℕ := fun e => edgeIdentity ids e.val
    let colors : G.edgeSet → ℕ := colorProgram.program.output H par edgeIDs (fun _ => ()) (fun _ _ => false)
    have hp : Proper H ((auxDegree k.degree ell)^64) colors :=
      colorProgram_correct H par edgeIDs (ColorIdentityProof.edgeKey_injective G ids hi.1)
        (edgeIdentity_bound G k.n b ids hi) (auxDegree_two k.degree ell hell)
        (power_line_degree G k.degree ell hG.2 hell)
    let chi : Sym2 (Fin N) → ℕ := fun e => if he : e ∈ G.edgeSet then colors ⟨e,he⟩ else 0
    have hchi (e : G.edgeSet) : chi e.val = colors e := dif_pos e.property
    have hhost (e : G.edgeSet) (u : Fin N) (hu : HostsEdge ids e.val u) :
        S.program.output G (param (k,ell)) ids (lineInput G ids (fun _ => ())) (fun _ _ => false) u
          (edgeIdentity ids e.val) = some (colors e) :=
      hSo N G ids hi.1 par (256*ell+1) (fun _ => ()) e u hu
    have hedge (u v : Fin N) (huv : G.Adj u v) :
        execute A G (k,ell) ids (neighborIDs G ids) u (ids v) = chi s(u,v) := by
      calc
        _ = colors ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ :=
          EdgeWrapper.edge_output S param G (k,ell) ids hi.1 colors hhost u v huv
        _ = _ := (hchi ⟨s(u,v),G.mem_edgeSet.mpr huv⟩).symm
    refine ⟨chi,?_,?_⟩
    · intro u v huv
      exact ⟨hedge u v huv,by simpa only [Sym2.eq_swap] using hedge v u huv.symm⟩
    · have hpalette : (auxDegree k.degree ell)^64 = (max 2 k.degree)^(49280*ell) := by
        rw [auxDegree,← pow_mul]
        congr 1
        ring
      have hfun : (fun e : G.edgeSet => chi e.val) = colors := funext hchi
      rw [hfun,← hpalette]
      exact hp
