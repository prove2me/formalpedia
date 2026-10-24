-- Prove2me | solution 1 for FuzzyExtractors.EditSketch.lemma_7_3_recovery
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T16:40:42.477724+00:00
-- url     : https://prove2.me/submissions/d7b28867-38f8-47b1-95a3-0bd78daae4bb

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

open FuzzyExtractors.EditSketch
namespace ShingleSupport

theorem at_mem {𝓕 : Type} [Fintype 𝓕] [Inhabited 𝓕] (c : ℕ) (w : List 𝓕)
    (i : ℕ) (hi : i + c ≤ w.length) : shingleAt c w i ∈ shingles c w := by
  classical
  simp only [shingles, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨i, fun k => ?_⟩
  have hk : i + (k : ℕ) < w.length := by omega
  simp [shingleAt, List.getElem?_eq_getElem hk]

theorem card_le {𝓕 : Type} [Fintype 𝓕] [Inhabited 𝓕] (c : ℕ) (w : List 𝓕)
    (hc : 1 ≤ c) : (shingles c w).card ≤ w.length - c + 1 := by
  classical
  have hsub : shingles c w ⊆ (Finset.range (w.length - c + 1)).image (shingleAt c w) := by
    intro u hu
    simp only [shingles, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨i, hi⟩ := hu
    have hlast := (List.getElem?_eq_some_iff.mp (hi ⟨c-1, by omega⟩)).1
    have hib : i < w.length - c + 1 := by dsimp only at hlast; omega
    refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hib, ?_⟩
    funext k
    obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp (hi k)
    simpa [shingleAt, List.getElem?_eq_getElem hk] using heq
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simp))

theorem gc_lt {𝓕 : Type} [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (c n : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) (w : EditSpace 𝓕 n)
    (j : Fin ⌈(n : ℝ) / c⌉₊) : gc c w j < n - c + 1 := by
  classical
  have hi : min ((j : ℕ) * c) (n-c) + c ≤ w.1.length := by
    have h := min_le_right ((j : ℕ) * c) (n-c)
    rw [w.2]
    omega
  have hm := at_mem c w.1 (min ((j : ℕ) * c) (n-c)) hi
  have hlt : gc c w j < (shingles c w.1).card := by
    apply Finset.card_lt_card
    exact Finset.filter_ssubset.mpr ⟨_, hm, lt_irrefl _⟩
  exact hlt.trans_le (by simpa [w.2] using card_le c w.1 hc)

theorem recovery_range {𝓕 : Type} [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (n c : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) :
    ∃ T : Finset (Fin ⌈(n : ℝ) / c⌉₊ → ℕ),
      (T.card : ℝ) ≤ (2 : ℝ) ^ ((⌈(n : ℝ) / c⌉₊ : ℝ) *
        Real.logb 2 ((n : ℝ) - c + 1)) ∧ ∀ w : EditSpace 𝓕 n, gc c w ∈ T := by
  classical
  let f : (Fin ⌈(n : ℝ) / c⌉₊ → Fin (n-c+1)) → (Fin ⌈(n : ℝ) / c⌉₊ → ℕ) :=
    fun v j => (v j : ℕ)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · have h := Finset.card_image_le (s := Finset.univ) (f := f)
    have hp : (n : ℝ) - c + 1 > 0 := by
      have h : (c : ℝ) ≤ n := by exact_mod_cast hcn
      linarith
    rw [mul_comm _ (Real.logb _ _), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hp]
    have hcast : ((n-c+1 : ℕ) : ℝ) = (n : ℝ) - c + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hcn, Nat.cast_one]
    calc
      ((Finset.univ.image f).card : ℝ) ≤ ((n-c+1)^⌈(n : ℝ) / c⌉₊ : ℕ) := by
        exact_mod_cast (by simpa using h)
      _ = ((n : ℝ) - c + 1) ^ (⌈(n : ℝ) / c⌉₊ : ℝ) := by simp [hcast]
  · intro w
    refine Finset.mem_image.mpr ⟨(fun j => ⟨gc c w j, gc_lt c n hc hcn w j⟩), by simp, rfl⟩

theorem rank_inj {α : Type*} [LinearOrder α] (s : Finset α) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s)
    (he : (s.filter (· < a)).card = (s.filter (· < b)).card) : a = b := by
  classical
  have hlt {x y : α} (hx : x ∈ s) (hxy : x < y) :
      (s.filter (· < x)).card < (s.filter (· < y)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro z hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
        ((Finset.mem_filter.mp hz).2).trans hxy⟩
    · intro heq
      have hmem : x ∈ s.filter (· < y) := Finset.mem_filter.mpr ⟨hx,hxy⟩
      rw [← heq] at hmem
      exact (lt_irrefl x) (Finset.mem_filter.mp hmem).2
  rcases lt_trichotomy a b with h | h | h
  · have := hlt ha h; omega
  · exact h
  · have := hlt hb h; omega

theorem recovery_injective {𝓕 : Type} [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (n c : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) :
    Function.Injective (fun w : EditSpace 𝓕 n => (shingles c w.1, gc c w)) := by
  classical
  intro w v h
  have hs := congrArg Prod.fst h
  change shingles c w.1 = shingles c v.1 at hs
  have hg := congrArg Prod.snd h
  change gc c w = gc c v at hg
  have hb (j : Fin ⌈(n : ℝ) / c⌉₊) :
      shingleAt c w.1 (min ((j : ℕ)*c) (n-c)) =
      shingleAt c v.1 (min ((j : ℕ)*c) (n-c)) := by
    have hi : min ((j : ℕ)*c) (n-c) + c ≤ n := by
      have := min_le_right ((j : ℕ)*c) (n-c); omega
    have hw := at_mem c w.1 _ (by simpa [w.2] using hi)
    have hv := at_mem c v.1 _ (by simpa [v.2] using hi)
    have he := congrFun hg j
    change ((shingles c w.1).filter _).card = ((shingles c v.1).filter _).card at he
    rw [← hs] at hv he
    have hlt (x y : Fin c → 𝓕) (hx : x ∈ shingles c w.1) (hxy : toLex x < toLex y) :
        ((shingles c w.1).filter (fun u => toLex u < toLex x)).card <
        ((shingles c w.1).filter (fun u => toLex u < toLex y)).card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro z hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
          ((Finset.mem_filter.mp hz).2).trans hxy⟩
      · intro heq
        have hmem : x ∈ (shingles c w.1).filter (fun u => toLex u < toLex y) :=
          Finset.mem_filter.mpr ⟨hx,hxy⟩
        rw [← heq] at hmem
        exact (lt_irrefl _) (Finset.mem_filter.mp hmem).2
    rcases lt_trichotomy (toLex (shingleAt c w.1 (min ((j : ℕ)*c) (n-c))))
        (toLex (shingleAt c v.1 (min ((j : ℕ)*c) (n-c)))) with h | h | h
    · have := hlt _ _ hw h; omega
    · exact toLex.injective h
    · have := hlt _ _ hv h; omega
  apply Subtype.ext
  apply List.ext_getElem (by simp [w.2,v.2])
  intro k hkw hkv
  have hkn : k < n := by simpa [w.2] using hkw
  have hjc := Nat.div_mul_le_self k c
  have hj : k/c < ⌈(n : ℝ)/c⌉₊ := by
    apply Nat.lt_ceil.mpr
    apply (lt_div_iff₀ (by exact_mod_cast (show 0 < c by omega))).mpr
    exact_mod_cast (lt_of_le_of_lt hjc hkn)
  have hkc : k < (k/c)*c+c := by
    have hm := Nat.mod_lt k (show 0 < c by omega)
    have he := Nat.mod_add_div k c
    rw [Nat.mul_comm c (k/c)] at he
    omega
  let i := min ((k/c)*c) (n-c)
  have hik : i ≤ k := (min_le_left _ _).trans hjc
  have hki : k-i < c := by
    dsimp [i]
    rcases le_total ((k/c)*c) (n-c) with hi | hi
    · rw [min_eq_left hi]; omega
    · rw [min_eq_right hi]; omega
  have he := congrFun (hb ⟨k/c,hj⟩) ⟨k-i,hki⟩
  have hsum : i+(k-i)=k := Nat.add_sub_of_le hik
  simpa [shingleAt, show min ((k/c)*c) (n-c) = i from rfl, hsum,
    List.getElem?_eq_getElem hkw, List.getElem?_eq_getElem hkv] using he

theorem recovery_of_distortion (𝓕 : Type) [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (n c t₁ : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n)
    (hlip : ∀ w w' : EditSpace 𝓕 n, editDis w w' ≤ t₁ →
      symmDiffDis (shingles c w.1) (shingles c w'.1) ≤ (2*c-1)*t₁) :
    IsEmbeddingWithRecovery (editDis (𝓕 := 𝓕) (n := n)) symmDiffDis t₁ ((2*c-1)*t₁)
      ((⌈(n : ℝ)/c⌉₊ : ℝ)*Real.logb 2 ((n : ℝ)-c+1))
      (fun w => shingles c w.1) (gc c) :=
  ⟨hlip, recovery_range n c hc hcn, recovery_injective n c hc hcn⟩

#print axioms recovery_of_distortion
#print axioms recovery_range
#print axioms recovery_injective
end ShingleSupport

open MasekPaterson.Shared FuzzyExtractors.EditSketch
namespace EditCost
def cost {α : Type*} (S : List (EditOp α)) : ℕ :=
  (S.map fun o => if o.src.isSome ∧ o.tgt.isSome then 2 else 1).sum

lemma cast_cost {α : Type} (S : List (EditOp α)) : (cost S : ℝ) = seqCost gammaIndel S := by
  induction S with
  | nil => simp [cost,seqCost]
  | cons o S ih =>
    simp only [cost,List.map_cons,List.sum_cons,Nat.cast_add] at *
    rw [ih]
    simp [seqCost,gammaIndel]

lemma prepend {α : Type*} {S : List (EditOp α)} {A B : List α} (h : Takes S A B) (p : List α) :
    Takes S (p++A) (p++B) := by
  induction h with
  | nil A => exact Takes.nil _
  | @cons o S A C B hy ht ih =>
    apply Takes.cons (s:=o) _ ih
    obtain ⟨σ,τ,ha,hc⟩ := hy
    exact ⟨p++σ,τ,by simp [ha,List.append_assoc],by simp [hc,List.append_assoc]⟩

lemma reachable {α : Type*} (A B : List α) : ∃ S, Takes S A B := by
  induction A generalizing B with
  | nil =>
    induction B with
    | nil => exact ⟨[],Takes.nil []⟩
    | cons b B ih =>
      obtain ⟨S,hS⟩ := ih
      refine ⟨insOp b :: S, Takes.cons (C := [b]) ?_ ?_⟩
      · exact ⟨[],[],by simp [insOp],by simp [insOp]⟩
      · simpa using prepend hS [b]
  | cons a A ih =>
    obtain ⟨S,hS⟩ := ih B
    refine ⟨delOp a :: S, Takes.cons ?_ hS⟩
    exact ⟨[],A,by simp [delOp],by simp [delOp]⟩

theorem attained {α : Type} (A B : List α) :
    ∃ S, Takes S A B ∧ (cost S : ℝ) = editDist gammaIndel A B := by
  classical
  have hex : ∃ n : ℕ, ∃ S, Takes S A B ∧ cost S = n := by
    obtain ⟨S,hS⟩ := reachable A B
    exact ⟨cost S,S,hS,rfl⟩
  obtain ⟨S,hS,hc⟩ := Nat.find_spec hex
  refine ⟨S,hS,?_⟩
  have hset : BddBelow {x : ℝ | ∃ T : List (EditOp α), Takes T A B ∧ x=seqCost gammaIndel T} := by
    refine ⟨0,?_⟩
    rintro x ⟨T,hT,rfl⟩
    rw [← cast_cost]
    positivity
  unfold editDist
  apply le_antisymm
  · refine le_csInf (s := {x : ℝ | ∃ T : List (EditOp α), Takes T A B ∧ x=seqCost gammaIndel T}) ?_ ?_
    · exact ⟨seqCost gammaIndel S,S,hS,rfl⟩
    rintro x ⟨T,hT,rfl⟩
    rw [← cast_cost,hc]
    exact_mod_cast Nat.find_min' hex (show ∃ U, Takes U A B ∧ cost U=cost T from ⟨T,hT,rfl⟩)
  · exact csInf_le hset ⟨S,hS,cast_cost S⟩

theorem floor_witness {α : Type} (A B : List α) :
    ∃ S, Takes S A B ∧ cost S = ⌊editDist gammaIndel A B⌋₊ := by
  obtain ⟨S,hS,he⟩ := attained A B
  exact ⟨S,hS,by rw [← he,Nat.floor_natCast]⟩
end EditCost
#print axioms EditCost.floor_witness

open FuzzyExtractors.EditSketch
namespace ShingleWindows
variable {α : Type} [Fintype α] [Inhabited α] [DecidableEq α]

lemma mem_iff {c : ℕ} {w : List α} {u : Fin c → α} :
    u ∈ shingles c w ↔ ∃ i : ℕ, ∀ k : Fin c, w[i+(k:ℕ)]?=some (u k) := by
  classical
  simp [shingles]

lemma at_eq {c : ℕ} {w : List α} {u : Fin c → α} {i : ℕ}
    (h : ∀ k : Fin c, w[i+(k:ℕ)]?=some (u k)) : shingleAt c w i = u := by
  funext k
  simp [shingleAt,List.getD_eq_getElem?_getD,h k]

lemma before {p s : List α} {a : α} {j : ℕ} (hj : j < p.length) :
    (p++a::s)[j]? = (p++s)[j]? := by
  rw [List.getElem?_append_left hj,List.getElem?_append_left hj]
lemma after {p s : List α} {a : α} {j : ℕ} (hj : p.length ≤ j) :
    (p++a::s)[j+1]? = (p++s)[j]? := by
  rw [List.getElem?_append_right (by omega),List.getElem?_append_right hj]
  rw [show j+1-p.length=(j-p.length)+1 by omega]
  simp

lemma old_lost {c : ℕ} (p s : List α) (a : α) :
    shingles c (p++s) \ shingles c (p++a::s) ⊆
      (Finset.Ico (p.length+1-c) p.length).image (shingleAt c (p++s)) := by
  classical
  intro u hu
  obtain ⟨hu,hn⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨i,hi⟩ := mem_iff.mp hu
  have hleft : ¬ i+c ≤ p.length := by
    intro h
    apply hn
    apply mem_iff.mpr
    refine ⟨i,fun k => ?_⟩
    rw [before (by have := k.isLt; omega)]
    exact hi k
  have hright : i < p.length := by
    by_contra h
    apply hn
    apply mem_iff.mpr
    refine ⟨i+1,fun k => ?_⟩
    rw [show i+1+(k:ℕ)=(i+(k:ℕ))+1 by omega, after (by omega)]
    exact hi k
  exact Finset.mem_image.mpr ⟨i,Finset.mem_Ico.mpr ⟨by omega,hright⟩,at_eq hi⟩

lemma new_gained {c : ℕ} (p s : List α) (a : α) :
    shingles c (p++a::s) \ shingles c (p++s) ⊆
      (Finset.Ico (p.length+1-c) (p.length+1)).image (shingleAt c (p++a::s)) := by
  classical
  intro u hu
  obtain ⟨hu,hn⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨i,hi⟩ := mem_iff.mp hu
  have hleft : ¬ i+c ≤ p.length := by
    intro h
    apply hn
    apply mem_iff.mpr
    refine ⟨i,fun k => ?_⟩
    rw [← before (a:=a) (by have := k.isLt; omega)]
    exact hi k
  have hright : i < p.length+1 := by
    by_contra h
    apply hn
    apply mem_iff.mpr
    refine ⟨i-1,fun k => ?_⟩
    have he := after (p:=p) (s:=s) (a:=a) (j:=i-1+(k:ℕ)) (by omega)
    rw [show i-1+(k:ℕ)+1=i+(k:ℕ) by omega] at he
    exact he.symm.trans (hi k)
  exact Finset.mem_image.mpr ⟨i,Finset.mem_Ico.mpr ⟨by omega,hright⟩,at_eq hi⟩

theorem insertion {c : ℕ} (hc : 1 ≤ c) (p s : List α) (a : α) :
    symmDiffDis (shingles c (p++s)) (shingles c (p++a::s)) ≤ 2*c-1 := by
  classical
  have ho := (Finset.card_le_card (old_lost (c:=c) p s a)).trans Finset.card_image_le
  have hn := (Finset.card_le_card (new_gained (c:=c) p s a)).trans Finset.card_image_le
  simp only [Nat.card_Ico] at ho hn
  unfold symmDiffDis
  rw [Finset.symmDiff_def]
  have h := Finset.card_union_le (shingles c (p++s) \ shingles c (p++a::s))
    (shingles c (p++a::s) \ shingles c (p++s))
  omega
end ShingleWindows
#print axioms ShingleWindows.insertion

open FuzzyExtractors.EditSketch MasekPaterson.Shared
open scoped symmDiff
namespace ShingleDistortion
lemma triangle {α : Type} [DecidableEq α] (A B C : Finset α) :
    symmDiffDis A C ≤ symmDiffDis A B + symmDiffDis B C := by
  have hs : A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C) := by
    intro x
    simp only [Finset.mem_symmDiff,Finset.mem_union]
    tauto
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma step {α : Type} [Fintype α] [Inhabited α] [DecidableEq α]
    {c : ℕ} (hc : 1 ≤ c) {o : EditOp α} {A B : List α} (hy : Yields o A B) :
    symmDiffDis (shingles c A) (shingles c B) ≤ (2*c-1)*EditCost.cost [o] := by
  rcases o with ⟨src,tgt,hn⟩
  obtain ⟨p,s,rfl,rfl⟩ := hy
  cases src with
  | none =>
    cases tgt with
    | none => exact False.elim (hn ⟨rfl,rfl⟩)
    | some b => simpa [EditCost.cost,List.append_assoc] using ShingleWindows.insertion hc p s b
  | some a =>
    cases tgt with
    | none =>
      have hi := ShingleWindows.insertion hc p s a
      simpa [EditCost.cost,List.append_assoc,symmDiffDis,symmDiff_comm] using hi
    | some b =>
      have ha := ShingleWindows.insertion hc p s a
      have hb := ShingleWindows.insertion hc p s b
      have ht := triangle (shingles c (p++a::s)) (shingles c (p++s)) (shingles c (p++b::s))
      have he : symmDiffDis (shingles c (p++a::s)) (shingles c (p++s)) =
          symmDiffDis (shingles c (p++s)) (shingles c (p++a::s)) := by
        simp [symmDiffDis,symmDiff_comm]
      rw [he] at ht
      simp only [Option.toList_some,List.append_assoc,List.singleton_append]
      simp only [EditCost.cost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Option.isSome_some,Bool.true_eq, and_self,if_true,add_zero]
      omega

theorem path {α : Type} [Fintype α] [Inhabited α] [DecidableEq α]
    {c : ℕ} (hc : 1 ≤ c) {S : List (EditOp α)} {A B : List α} (h : Takes S A B) :
    symmDiffDis (shingles c A) (shingles c B) ≤ (2*c-1)*EditCost.cost S := by
  induction h with
  | nil A => simp [symmDiffDis,EditCost.cost]
  | @cons o S A C B hy ht ih =>
    have hs := step hc hy
    have htri := triangle (shingles c A) (shingles c C) (shingles c B)
    have he : EditCost.cost (o::S) = EditCost.cost [o] + EditCost.cost S := by simp [EditCost.cost]
    rw [he,mul_add]
    exact htri.trans (Nat.add_le_add hs ih)

theorem distance {α : Type} [Fintype α] [Inhabited α] [DecidableEq α]
    {c n : ℕ} (hc : 1 ≤ c) (w w' : EditSpace α n) :
    symmDiffDis (shingles c w.1) (shingles c w'.1) ≤ (2*c-1)*editDis w w' := by
  obtain ⟨S,hS,hcS⟩ := EditCost.floor_witness w.1 w'.1
  have hp := path hc hS
  simpa [editDis,hcS] using hp
end ShingleDistortion

theorem solution (𝓕 : Type) [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (n c t₁ : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) :
    IsEmbeddingWithRecovery (editDis (𝓕 := 𝓕) (n := n)) symmDiffDis t₁ ((2*c-1)*t₁)
      ((⌈(n : ℝ)/c⌉₊ : ℝ)*Real.logb 2 ((n : ℝ)-c+1))
      (fun w => shingles c w.1) (gc c) := by
  apply ShingleSupport.recovery_of_distortion 𝓕 n c t₁ hc hcn
  intro w w' h
  exact (ShingleDistortion.distance hc w w').trans (Nat.mul_le_mul_left _ h)
#print axioms solution
