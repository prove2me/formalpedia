-- Prove2me | solution 1 for DirectedHamiltonicity.Main.finite_coin_weighted_parity_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:24:42.896184+00:00
-- url     : https://prove2.me/submissions/4c9da95b-a0b5-41b9-b565-de40ebf378a1

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_DetSum
import Theorems.Thm_DirectedHamiltonicity_Main_lemma8
import Theorems.Thm_DirectedHamiltonicity_Main_lemma9
import Theorems.Thm_DirectedHamiltonicity_Main_lemma10


open scoped BigOperators
namespace DirectedHamiltonicity.Sampling
open Finset

/-- Count ordered independent samples which all avoid a predicate. -/
theorem avoid_count {A : Type*} [Fintype A] (p : A → Prop) (M : ℕ) [DecidablePred p]
    [DecidablePred (fun f : Fin M → A => ∀ i, p (f i))] :
    (univ.filter (fun f : Fin M → A => ∀ i, p (f i))).card =
      (univ.filter p).card ^ M := by
  classical
  let e : {f : Fin M → A // ∀ i, p (f i)} ≃ (Fin M → {a : A // p a}) :=
    { toFun := fun f i => ⟨f.1 i, f.2 i⟩
      invFun := fun g => ⟨fun i => (g i).1, fun i => (g i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype] using Fintype.card_congr e

/-- Union bound as an integer count, with a finite set of possible failures. -/
theorem exists_count {A X : Type*} [Fintype A] (s : Finset X) (p : X → A → Prop)
    [∀ x, DecidablePred (p x)] [DecidablePred (fun a => ∃ x ∈ s, p x a)] :
    (univ.filter (fun a => ∃ x ∈ s, p x a)).card ≤
      ∑ x ∈ s, (univ.filter (p x)).card := by
  classical
  rw [show univ.filter (fun a => ∃ x ∈ s, p x a) = s.biUnion (fun x => univ.filter (p x)) by
    ext a; simp]
  exact card_biUnion_le

/-- Each truncated execution would list more than 12M objects. -/
theorem cutoff_count {R : Type*} [Fintype R] (cost : R → ℕ) (M : ℕ)
    (hm : 0 < M) (avg : (∑ r, cost r) = Fintype.card R * M) :
    12 * (univ.filter (fun r => 12*M < cost r)).card ≤ Fintype.card R := by
  classical
  let bad := univ.filter (fun r => 12*M < cost r)
  have h : ∑ r ∈ bad, 12*M ≤ ∑ r ∈ bad, cost r :=
    sum_le_sum fun r hr => (mem_filter.mp hr).2.le
  have j := sum_le_univ_sum_of_nonneg (s := bad) (fun r => Nat.zero_le (cost r))
  change 12*bad.card ≤ _
  simp only [sum_const, smul_eq_mul] at h
  rw [avg] at j
  exact Nat.le_of_mul_le_mul_right (c := M) (by nlinarith) hm

/-- A block of at least 1/p independent trials misses with probability at most 1/2. -/
theorem miss_block (p : ℝ) (K : ℕ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (budget : 1 ≤ K*p) :
    (1-p)^K ≤ 1/2 := by
  have bern : 1+(K:ℝ)*p ≤ (1+p)^K := by
    clear budget
    induction K with
    | zero => simp
    | succ n ih =>
      have h := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1+p)
      push_cast
      rw [pow_succ]
      nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hp) hp]
  have prod : (1-p)^K * (1+p)^K ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) (by nlinarith [sq_nonneg p])
  have hn := pow_nonneg (by linarith : 0 ≤ 1-p) K
  have ht := mul_le_mul_of_nonneg_left (show 2 ≤ (1+p)^K by linarith) hn
  linarith

end DirectedHamiltonicity.Sampling

namespace DirectedHamiltonicity.Sampling
open Finset
/-- Decode all binary strings of one fixed length to integer residues and then uniformly
enumerated abstract outcomes. Complete blocks cover each outcome equally often. -/
noncomputable def sampleResidue {A : Type*} [Fintype A] [Nonempty A] (L : ℕ)
    (f : Fin L → Bool) : A :=
  (Fintype.equivFin A).symm ⟨(Fintype.equivFin (Fin L → Bool) f).val % Fintype.card A,
    Nat.mod_lt _ Fintype.card_pos⟩

open Classical in
theorem residue_lower {A : Type*} [Fintype A] [Nonempty A] (S : Finset A) (L : ℕ) :
    (2^L/Fintype.card A)*S.card ≤ (univ.filter (fun f : Fin L → Bool => sampleResidue L f ∈ S)).card := by
  classical
  let N := Fintype.card A
  let D := 2^L
  let q := D/N
  have Npos : 0 < N := Fintype.card_pos
  have Dcard : Fintype.card (Fin L → Bool) = D := by simp [D]
  let good := univ.filter (fun f : Fin L → Bool => sampleResidue L f ∈ S)
  have hblock := Nat.div_mul_le_self D N
  let pack (u : Fin q × ↥S) : Fin (Fintype.card (Fin L → Bool)) :=
    ⟨u.1.val*N + (Fintype.equivFin A u.2.1).val, by
      rw [Dcard]
      have x := (Fintype.equivFin A u.2.1).isLt
      have y := Nat.mul_le_mul_right N (show u.1.val+1 ≤ q from u.1.isLt)
      rw [Nat.succ_mul] at y; change _ < N at x; dsimp only [q] at y; omega⟩
  let encode (u : Fin q × ↥S) := (Fintype.equivFin (Fin L → Bool)).symm (pack u)
  have decode (u : Fin q × ↥S) : sampleResidue L (encode u) = u.2.val := by
    apply (Fintype.equivFin A).injective
    apply Fin.ext
    have v := (Fintype.equivFin A u.2.1).isLt
    simp [sampleResidue,encode,pack,N,Nat.add_mod,Nat.mod_eq_of_lt v]
  let e (u : Fin q × ↥S) : ↥good := ⟨encode u,mem_filter.mpr ⟨mem_univ _,decode u ▸ u.2.2⟩⟩
  have inject : Function.Injective e := by
    intro u v eq
    have h : encode u = encode v := congrArg Subtype.val eq
    have snd : u.2 = v.2 := Subtype.ext ((decode u).symm.trans ((congrArg (sampleResidue L) h).trans (decode v)))
    have packed := congrArg (fun z : (Fin L → Bool) => ((Fintype.equivFin _) z).val) h
    simp only [encode,Equiv.apply_symm_apply,pack,snd,add_left_inj] at packed
    have fst : u.1.val=v.1.val := Nat.eq_of_mul_eq_mul_right Npos packed
    exact Prod.ext (Fin.ext fst) snd
  have cap := Fintype.card_le_of_injective e inject
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] using cap

open Classical in
theorem fairResidues {A : Type*} [Fintype A] [Nonempty A] (S : Finset A) (L : ℕ)
    (many : 40*Fintype.card A ≤ 2^L) (ideal : 41*Fintype.card A ≤ 48*S.card) :
    5*2^L ≤ 6*(univ.filter (fun f : Fin L → Bool => sampleResidue L f ∈ S)).card := by
  classical
  let N := Fintype.card A
  let D := 2^L
  let q := D/N
  let good := univ.filter (fun f : Fin L → Bool => sampleResidue L f ∈ S)
  have Npos : 0 < N := Fintype.card_pos
  have usable : q*S.card ≤ good.card := residue_lower S L
  have hq : 40 ≤ q := (Nat.le_div_iff_mul_le Npos).2 many
  have rem := Nat.mod_lt D Npos
  have divmod := Nat.mod_add_div D N
  have count := Nat.mul_le_mul_left q ideal
  have extra := Nat.mul_le_mul_right N hq
  change 5*D ≤ 6*good.card
  dsimp only [N] at extra
  change 41*N ≤ 48*S.card at ideal
  change q*(41*N) ≤ q*(48*S.card) at count
  change D%N+N*q=D at divmod
  nlinarith
end DirectedHamiltonicity.Sampling

namespace DirectedHamiltonicity.Sampling
open Finset

/-- An explicit bound on the number of trial sequences missing at least one required item.
K trials form a block; n+4 independent blocks suffice for a 1/16 error budget. -/
theorem coverage_count {A X : Type*} [Fintype A] [Nonempty A] [DecidableEq X] (s : Finset X)
    (sample : A → Finset X) (n K : ℕ) (number : s.card ≤ 2^n)
    (hit : ∀ x ∈ s, (Fintype.card A : ℝ) ≤ K * ((univ.filter (fun a => x ∈ sample a)).card : ℕ))
    :
    let M := K*(n+4)
    16 * (univ.filter (fun f : Fin M → A => ∃ x ∈ s, ∀ j, x ∉ sample (f j))).card ≤
      Fintype.card (Fin M → A) := by
  classical
  intro M
  let N := Fintype.card A
  have Npos : (0:ℝ) < N := by exact_mod_cast Fintype.card_pos (α := A)
  have oneItem (x : X) (hx : x ∈ s) :
      ((univ.filter (fun f : Fin M → A => ∀ j, x ∉ sample (f j))).card : ℝ) ≤
      N^M * ((1/2 : ℝ)^(n+4)) := by
    let good := (univ.filter (fun a => x ∈ sample a)).card
    let bad := (univ.filter (fun a => x ∉ sample a)).card
    have split : good + bad = N := card_filter_add_card_filter_not _
    have split' : (good:ℝ) + bad = N := by exact_mod_cast split
    let p : ℝ := good/N
    have hp : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) Npos.le
    have hp1 : p ≤ 1 := (div_le_one Npos).2 (by linarith [Nat.cast_nonneg (α:=ℝ) bad])
    have cost : 1 ≤ (K:ℝ)*p := by
      rw [show (K:ℝ)*p = ((K:ℝ)*good)/N by dsimp [p]; ring]
      exact (one_le_div Npos).2 (hit x hx)
    have frac : (bad:ℝ) = N*(1-p) := by
      dsimp [p]; field_simp; nlinarith
    rw [avoid_count (fun a => x ∉ sample a) M]
    change (((bad^M : ℕ) : ℝ)) ≤ _
    push_cast
    rw [frac, mul_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg Npos.le _)
    rw [show M = K*(n+4) from rfl, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (by linarith) _) (miss_block p K hp hp1 cost) _
  have union := exists_count s (fun x (f : Fin M → A) => ∀ j, x ∉ sample (f j))
  have U : ((univ.filter (fun f : Fin M → A => ∃ x ∈ s, ∀ j, x ∉ sample (f j))).card : ℝ)
      ≤ ∑ x ∈ s, ((univ.filter (fun f : Fin M → A => ∀ j, x ∉ sample (f j))).card:ℝ) := by
    exact_mod_cast union
  have U' := U.trans (sum_le_sum oneItem)
  rw [sum_const, nsmul_eq_mul] at U'
  have hs : (s.card:ℝ) ≤ 2^n := by exact_mod_cast number
  have U'' := U'.trans (mul_le_mul_of_nonneg_right hs
    (mul_nonneg (pow_nonneg Npos.le _) (by positivity)))
  have simpl : 16 * ((2:ℝ)^n * ((N:ℝ)^M * (1/2:ℝ)^(n+4))) = (N:ℝ)^M := by
    rw [pow_add, one_div, inv_pow, inv_pow]; have hh : (2:ℝ)^n ≠ 0 := by positivity
    field_simp; ring
  rw [Fintype.card_fun, Fintype.card_fin]
  change 16*_ ≤ N^M
  exact_mod_cast (show (16:ℝ)*_ ≤ (N:ℝ)^M from
    (mul_le_mul_of_nonneg_left U'' (by norm_num : (0:ℝ) ≤ 16)).trans_eq simpl)
end DirectedHamiltonicity.Sampling

namespace DirectedHamiltonicity.Sampling
open Finset

private theorem count_pairs {R A : Type*} [Fintype R] [Fintype A] (p : R → A → Prop)
    [∀ r, DecidablePred (p r)] [DecidablePred (fun q : R × A => p q.1 q.2)] :
    (univ.filter (fun q : R × A => p q.1 q.2)).card =
      ∑ r, (univ.filter (p r)).card := by
  classical
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  apply sum_congr rfl; intro x _; apply sum_congr rfl; intro a _
  by_cases h : p x a <;> simp [h]

/-- Count the good outcomes in the joint experiment: R is shared by all trials.
Coverage is bounded conditional on R, whereas the expected list size is taken over R. -/
theorem experiment_margin {A R X : Type*} [Fintype R] [Fintype A] [Nonempty A] [DecidableEq X]
    (targets : R → Finset X) (sample : R → A → Finset X) (n K : ℕ) (Kpos : 0 < K)
    (number : ∀ r, (targets r).card ≤ 2^n)
    (hit : ∀ r x, x ∈ targets r →
      (Fintype.card A : ℝ) ≤ K * ((univ.filter (fun a => x ∈ sample r a)).card : ℕ))
    (mean : ∀ a, ∑ r, (sample r a).card = Fintype.card R) :
    let M := K*(n+4)
    48 * (univ.filter (fun q : R × (Fin M → A) =>
      (∑ j, (sample q.1 (q.2 j)).card) ≤ 12*M ∧
      ∀ x ∈ targets q.1, ∃ j, x ∈ sample q.1 (q.2 j))).card ≥
        41 * Fintype.card (R × (Fin M → A)) := by
  classical
  intro M
  let F := Fin M → A
  let cost (q : R × F) : ℕ := ∑ j, (sample q.1 (q.2 j)).card
  let miss (r : R) (f : F) := ∃ x ∈ targets r, ∀ j, x ∉ sample r (f j)
  let uncovered := univ.filter (fun q : R × F => miss q.1 q.2)
  let overBudget := univ.filter (fun q : R × F => 12*M < cost q)
  let good := univ.filter (fun q : R × F => cost q ≤ 12*M ∧
    ∀ x ∈ targets q.1, ∃ j, x ∈ sample q.1 (q.2 j))
  change 41 * Fintype.card (R × F) ≤ 48*good.card
  have per (r : R) := coverage_count (targets r) (sample r) n K (number r) (hit r)
  have hav : 16*uncovered.card ≤ Fintype.card (R × F) := by
    change 16*(univ.filter (fun q : R × F => miss q.1 q.2)).card ≤ _
    rw [count_pairs miss, mul_sum, Fintype.card_prod]
    calc
      _ ≤ ∑ _r : R, Fintype.card F := sum_le_sum (fun r _ => per r)
      _ = _ := by simp
  have avg : ∑ q, cost q = Fintype.card (R × F)*M := by
    rw [Fintype.sum_prod_type, sum_comm]
    have col (f : F) : ∑ r, cost (r, f) = M*Fintype.card R := by
      dsimp [cost]; rw [sum_comm]; simp [mean]
    simp_rw [col]
    rw [Fintype.card_prod]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hcost : 12*overBudget.card ≤ Fintype.card (R × F) :=
    cutoff_count cost M (Nat.mul_pos Kpos (by omega)) avg
  have partition : (univ : Finset (R × F)) ⊆ good ∪ (overBudget ∪ uncovered) := by
    intro q _
    by_cases time : cost q ≤ 12*M
    · by_cases cov : ∀ x ∈ targets q.1, ∃ j, x ∈ sample q.1 (q.2 j)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,time,cov⟩)
      · push Not at cov
        exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,cov⟩))
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,by omega⟩))
  have hcard := (card_le_card partition).trans (card_union_le good (overBudget ∪ uncovered))
  have hboth := card_union_le overBudget uncovered
  rw [card_univ] at hcard
  omega
end DirectedHamiltonicity.Sampling

namespace DirectedHamiltonicity.Sampling
open Finset Main Main.Multidigraph Polynomial

private theorem allDets {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (r : (i : Internal s t) → Finset (H.incomingWeights w i.1)) :
    H.hamPathPoly (fun e => (X : (ZMod 2)[X]) ^ w e) s t =
      ∑ x, (H.augLaplacian w s t x r).det := by
  classical
  exact Main.lemma8 (V := V) (E := E) (EA := H.AugArc w s t r) H s t hst hn.1 hn.2.1 hn.2.2.1
    (fun e => (X : (ZMod 2)[X]) ^ w e) (H.augGraph w s t r) (fun _ => rfl)
    (fun a => a.1.2.2) (fun a => (X : (ZMod 2)[X]) ^ a.2.val.val)

private theorem zeroDet {V E : Type} [Fintype V] [vDec : DecidableEq V] [Fintype E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (r : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (x : Finset (Internal s t)) (hx : x ∉ H.survivors w s t r) :
    (H.augLaplacian w s t x r).det = 0 := by
  classical
  have equal : vDec = Classical.decEq V := Subsingleton.elim _ _
  subst vDec
  unfold Multidigraph.survivors at hx
  simp only [mem_filter, mem_univ, true_and] at hx
  push Not at hx
  obtain ⟨i, _, row⟩ := hx
  exact Matrix.det_eq_zero_of_row_eq_zero (A := H.augLaplacian w s t x r)
    ⟨i.1,i.2.1⟩ (fun j => congrFun row j)

private theorem detSum {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (r : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (U : Finset (Finset (Internal s t))) (cov : H.survivors w s t r ⊆ U) :
    ∑ x ∈ U, (H.augLaplacian w s t x r).det =
      H.hamPathPoly (fun e => (X : (ZMod 2)[X]) ^ w e) s t := by
  classical
  refine Eq.trans ?_ (allDets H w s t hst hn r).symm
  exact sum_subset (subset_univ U) (fun x _ h => zeroDet H w s t r x (fun hx => h (cov hx)))

open Classical in
/-- With one common random augmentation and independent coefficient tuples, truncating
at 12M outputs and deduplicating still gives the entire path polynomial with probability ≥5/6. -/
theorem paritySampling_margin {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (d : ℕ) (hd : 1 ≤ d) (deg : ∀ v, (H.incomingWeights w v).card ≤ d) :
    let n := Fintype.card V
    let M := ⌈(2-(1/2:ℝ)^d)^(n-2)⌉₊ * (n+4)
    let R := (i : Internal s t) → Finset (H.incomingWeights w i.1)
    let A := H.NonzeroCoeffs w s t
    let S := fun (r : R) (a : A) => H.sampled w s t (fun i => (a i).1) r
    48 * (univ.filter (fun q : R × (Fin M → A) =>
      (∑ j, (S q.1 (q.2 j)).card) ≤ 12*M ∧
      ∑ x ∈ univ.biUnion (fun j => S q.1 (q.2 j)), (H.augLaplacian w s t x q.1).det =
        H.hamPathPoly (fun e => (X : (ZMod 2)[X]) ^ w e) s t)).card ≥
      41 * Fintype.card (R × (Fin M → A)) := by
  classical
  intro n M R A S
  let b := (2-(1/2:ℝ)^d)^(n-2)
  let K := ⌈b⌉₊
  have bpos : 0 < b := by
    apply pow_pos
    have h := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n:=d)
    linarith
  have kp : 0 < K := Nat.ceil_pos.mpr bpos
  let : Nonempty A := ⟨fun _ => ⟨1, one_ne_zero⟩⟩
  have apos : (0:ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have rpos : (0:ℝ) < Fintype.card R := by
    let : Nonempty R := ⟨fun _ => ∅⟩
    exact_mod_cast Fintype.card_pos (α := R)
  have number (r : R) : (H.survivors w s t r).card ≤ 2^n := by
    have hI := Fintype.card_subtype_le (fun v : V => v ≠ s ∧ v ≠ t)
    exact (card_le_univ _).trans ((Fintype.card_finset (α := Internal s t)).le.trans
      (Nat.pow_le_pow_right (by decide) hI))
  have hit (r : R) (x) (hx : x ∈ H.survivors w s t r) :
      (Fintype.card A:ℝ) ≤ K*((univ.filter (fun a : A => x ∈ S r a)).card:ℕ) := by
    have h9 := Main.lemma9 H w s t hst hn d hd deg r x hx
    have hh : b⁻¹ ≤ ((univ.filter (fun a : A => x ∈ S r a)).card:ℝ)/Fintype.card A :=
      h9.2.trans_eq h9.1.symm
    have hh' := (le_div_iff₀ apos).1 hh
    have hh'' := mul_le_mul_of_nonneg_left hh' bpos.le
    rw [← mul_assoc, mul_inv_cancel₀ bpos.ne', one_mul] at hh''
    exact hh''.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  have mean (a : A) : ∑ r, (S r a).card = Fintype.card R := by
    have h10 := Main.lemma10 H w s t hst hn a
    have h' := (div_eq_iff rpos.ne').mp h10
    rw [one_mul] at h'
    exact_mod_cast h'
  have joint := experiment_margin (H.survivors w s t) S n K kp number hit mean
  apply joint.trans
  apply Nat.mul_le_mul_left
  apply card_le_card
  intro q hq
  simp only [mem_filter, mem_univ, true_and] at hq
  obtain ⟨time, cov⟩ := hq
  apply mem_filter.mpr
  refine ⟨mem_univ _,time,detSum H w s t hst hn q.1 _ ?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := cov x hx
  exact mem_biUnion.mpr ⟨j,mem_univ _,hj⟩

end DirectedHamiltonicity.Sampling

namespace DirectedHamiltonicity.Sampling
open Main Main.Multidigraph Polynomial Finset

theorem coefficient {V E : Type} [Fintype V] [Fintype E] (H : Multidigraph V E)
    (w : E → ℕ) (s t : V) (B : ℕ) :
    (H.hamPathPoly (fun e => (X : (ZMod 2)[X]) ^ w e) s t).coeff B =
      (H.weightedPathCount w s t B : ZMod 2) := by
  classical
  rw [Multidigraph.hamPathPoly, Polynomial.finsetSum_coeff, Multidigraph.weightedPathCount,
    Finset.card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro p _
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.coeff_X_pow]
  simp only [Multidigraph.pathWeight, Int.natCast_inj]
  split <;> (rename_i h; simp_all [eq_comm])

end DirectedHamiltonicity.Sampling

namespace DirectedHamiltonicity.Sampling
open Finset Main Main.Multidigraph Polynomial
open Classical in
theorem weighted_parity_margin {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (d : ℕ) (hd : 1 ≤ d) (deg : ∀ v, (H.incomingWeights w v).card ≤ d) :
    let n := Fintype.card V
    let M := ⌈(2-(1/2:ℝ)^d)^(n-2)⌉₊ * (n+4)
    let R := (i : Internal s t) → Finset (H.incomingWeights w i.1)
    let A := H.NonzeroCoeffs w s t
    let S := fun (r : R) (a : A) => H.sampled w s t (fun i => (a i).1) r
    48 * (univ.filter (fun q : R × (Fin M → A) =>
      (∑ j, (S q.1 (q.2 j)).card) ≤ 12*M ∧
      ∀ B : ℤ,
        (if B < 0 then (0 : ZMod 2) else
          (∑ x ∈ univ.biUnion (fun j => S q.1 (q.2 j)),
            (H.augLaplacian w s t x q.1).det).coeff B.toNat) =
          (H.weightedPathCount w s t B : ZMod 2))).card ≥
      41 * Fintype.card (R × (Fin M → A)) := by
  classical
  intro n M R A S
  have h := paritySampling_margin H w s t hst hn d hd deg
  apply h.trans
  apply Nat.mul_le_mul_left
  apply card_le_card
  intro q hq
  simp only [mem_filter,mem_univ,true_and] at hq ⊢
  obtain ⟨fee,eq⟩ := hq
  refine ⟨fee,?_⟩
  intro B
  by_cases neg : B < 0
  · rw [if_pos neg]
    have hzero : H.weightedPathCount w s t B = 0 := by
      rw [Multidigraph.weightedPathCount, Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.mpr
      intro p _
      have nonneg := Int.natCast_nonneg (pathWeight w p)
      omega
    simp [hzero]
  · rw [if_neg neg,eq,coefficient,Int.toNat_of_nonneg (by omega : 0 ≤ B)]
end DirectedHamiltonicity.Sampling

namespace DirectedHamiltonicity.Sampling
open Finset Main Main.Multidigraph Polynomial
end DirectedHamiltonicity.Sampling

open DirectedHamiltonicity.Sampling Finset DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph Polynomial
open Classical in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (d : ℕ) (hd : 1 ≤ d) (deg : ∀ v, (H.incomingWeights w v).card ≤ d) :
    let n := Fintype.card V
    let M := ⌈(2-(1/2:ℝ)^d)^(n-2)⌉₊ * (n+4)
    let R := (i : Internal s t) → Finset (H.incomingWeights w i.1)
    let A := H.NonzeroCoeffs w s t
    let S := fun (r : R) (a : A) => H.sampled w s t (fun i => (a i).1) r
    let Ω := R × (Fin M → A)
    let good := univ.filter (fun q : R × (Fin M → A) =>
      (∑ j, (S q.1 (q.2 j)).card) ≤ 12*M ∧
      ∀ B : ℤ,
        (if B < 0 then (0 : ZMod 2) else
          (∑ x ∈ univ.biUnion (fun j => S q.1 (q.2 j)),
            (H.augLaplacian w s t x q.1).det).coeff B.toNat) =
          (H.weightedPathCount w s t B : ZMod 2))
    (41*Fintype.card Ω ≤ 48*good.card) ∧
      ∀ L : ℕ, 40*Fintype.card Ω ≤ 2^L →
        ∃ draw : (Fin L → Bool) → Ω,
          (∀ U : Finset Ω, (2^L/Fintype.card Ω)*U.card ≤
            (univ.filter (fun c => draw c ∈ U)).card) ∧
          5*2^L ≤ 6*(univ.filter (fun c => draw c ∈ good)).card := by
  classical
  intro n M R A S Ω good
  let : Nonempty Ω := ⟨(fun _ => ∅,fun _ _ => ⟨1,one_ne_zero⟩)⟩
  have margin : 41*Fintype.card Ω ≤ 48*good.card := weighted_parity_margin H w s t hst hn d hd deg
  refine ⟨margin,?_⟩
  intro L many
  exact ⟨sampleResidue L,fun U => residue_lower U L,fairResidues good L many margin⟩
