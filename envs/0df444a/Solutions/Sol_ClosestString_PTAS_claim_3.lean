-- Prove2me | solution 1 for ClosestString.PTAS.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:43:29.02472+00:00
-- url     : https://prove2.me/submissions/aae7d241-659f-424e-ad3e-230966f6a91c

import Definitions.Def_ClosestString_PTAS_Basic
import Definitions.Def_ClosestString_PTAS_Algorithm
import Init
import Mathlib


section
namespace Queelius.ClosestString
open MeasureTheory
open scoped BigOperators

theorem finite_estimate_probability {Ω I : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → I → ℝ) (d : I → ℝ) (e b : ℝ)
    (hlo : ∀ i, μ.real {ω | X ω i ≤ d i-e} ≤ b)
    (hhi : ∀ i, μ.real {ω | d i+e ≤ X ω i} ≤ b) :
    1-2*(Fintype.card I:ℝ)*b ≤ μ.real {ω | ∀ i, d i-e < X ω i ∧ X ω i < d i+e} := by
  classical
  let bad : I → Set Ω := fun i => {ω | X ω i ≤ d i-e} ∪ {ω | d i+e ≤ X ω i}
  have hb : μ.real (⋃ i, bad i) ≤ 2*(Fintype.card I:ℝ)*b := calc
    _ ≤ ∑ i, μ.real (bad i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : I, (b+b) := Finset.sum_le_sum fun i _ =>
      (measureReal_union_le _ _).trans (add_le_add (hlo i) (hhi i))
    _ = _ := by simp; ring
  have he : {ω | ∀ i, d i-e < X ω i ∧ X ω i < d i+e} = (⋃ i, bad i)ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq,Set.mem_compl_iff,Set.mem_iUnion,Set.mem_union,bad]
    push_neg
    rfl
  rw [he,measureReal_compl (Set.to_countable _).measurableSet,probReal_univ]
  linarith

theorem approximate_minimizer {I : Type*} (X d : I → ℝ) (e : ℝ)
    (h : ∀ i, d i-e < X i ∧ X i < d i+e)
    (p q : I) (hp : X p ≤ X q) : d p ≤ d q+2*e := by
  linarith [(h p).1,(h q).2]
end Queelius.ClosestString

end


section
namespace Queelius.ClosestString
open ClosestString.PTAS
open scoped BigOperators
variable {A : Type*} [DecidableEq A] {n m r : ℕ}

theorem disagree_has_error (u : Fin n → Fin m → A) (c : Fin m → A) (idx : Fin r → Fin n)
    {j : Fin m} (hj : j ∈ (agreeSet u idx)ᶜ) : ∃ a,u (idx a) j ≠ c j := by
  classical
  simp only [Finset.mem_compl,agreeSet,Finset.mem_filter,Finset.mem_univ,true_and] at hj
  push Not at hj
  obtain ⟨a,b,hab⟩ := hj
  by_cases ha : u (idx a) j=c j
  · exact ⟨b,fun hb => hab (ha.trans hb.symm)⟩
  · exact ⟨a,ha⟩

theorem disagree_card_le_sum (u : Fin n → Fin m → A) (c : Fin m → A) (idx : Fin r → Fin n) :
    (agreeSet u idx)ᶜ.card ≤ ∑ a,distOn (agreeSet u idx)ᶜ (u (idx a)) c := by
  classical
  have hs : (agreeSet u idx)ᶜ ⊆ Finset.univ.biUnion
      (fun a : Fin r => (agreeSet u idx)ᶜ.filter (fun j => u (idx a) j≠c j)) := by
    intro j hj
    obtain ⟨a,ha⟩ := disagree_has_error u c idx hj
    exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hj,ha⟩⟩
  exact (Finset.card_le_card hs).trans Finset.card_biUnion_le

theorem distOn_agree (u : Fin n → Fin m → A) (c : Fin m → A) (idx : Fin r → Fin n)
    (a : Fin r) : distOn (agreeSet u idx) (u (idx a)) c=mismatchOnAgree u c idx := by
  unfold distOn mismatchOnAgree
  congr 1
  ext j
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1,a,h.2⟩
  · rintro ⟨hj,b,hb⟩
    have he := (Finset.mem_filter.mp hj).2 b a
    exact ⟨hj,fun h => hb (he.trans h)⟩

theorem distance_partition (u v : Fin m → A) (Q : Finset (Fin m)) :
    hammingDist u v=distOn Q u v+distOn Qᶜ u v := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s:=Finset.univ.filter (fun j => u j≠v j))
    (fun j : Fin m => j ∈ Q)
  have hq : ((Finset.univ.filter (fun j => u j≠v j)).filter (fun j => j ∈ Q)) =
      Q.filter (fun j => u j≠v j) := by ext j; simp; tauto
  have hp : ((Finset.univ.filter (fun j => u j≠v j)).filter (fun j => j ∉ Q)) =
      Qᶜ.filter (fun j => u j≠v j) := by ext j; simp; tauto
  rw [hq,hp] at h
  exact h.symm

theorem distance_budget (u : Fin n → Fin m → A) (c : Fin m → A) (idx : Fin r → Fin n) :
    (agreeSet u idx)ᶜ.card+r*mismatchOnAgree u c idx ≤ ∑ a,hammingDist (u (idx a)) c := by
  have he : (∑ a,hammingDist (u (idx a)) c) =
      r*mismatchOnAgree u c idx+∑ a,distOn (agreeSet u idx)ᶜ (u (idx a)) c := by
    calc
      _ = ∑ a : Fin r, (mismatchOnAgree u c idx+distOn (agreeSet u idx)ᶜ (u (idx a)) c) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [distance_partition (u (idx a)) c (agreeSet u idx),distOn_agree]
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [he]
  have h := disagree_card_le_sum u c idx
  omega

theorem radius_budget (u : Fin n → Fin m → A) (c : Fin m → A) (d : ℕ)
    (hd : ∀ i,hammingDist (u i) c ≤ d) (idx : Fin r → Fin n) :
    (agreeSet u idx)ᶜ.card+r*mismatchOnAgree u c idx ≤ r*d := by
  apply (distance_budget u c idx).trans
  simpa using Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin r))) => hd (idx a))

end Queelius.ClosestString
open ClosestString.PTAS

theorem disagreement_solution {A : Type*} [DecidableEq A] {n m : ℕ} (u : Fin n → Fin m → A)
    (c : Fin m → A) (d : ℕ) (hd : ∀ i,hammingDist (u i) c ≤ d) (r : ℕ) (idx : Fin r → Fin n) :
    (agreeSet u idx)ᶜ.card ≤ r*d := by
  have h := Queelius.ClosestString.radius_budget u c d hd idx
  omega

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS
open scoped BigOperators
variable {A : Type*} [DecidableEq A] {n m : ℕ}

theorem pair_disagreement (u : Fin n → Fin m → A) (i j : Fin n) :
    (agreeSet u ![i,j])ᶜ.card=hammingDist (u i) (u j) := by
  congr 1
  ext k
  simp [agreeSet,Fin.forall_fin_two,eq_comm]

theorem minMismatch_le_tuple (u : Fin n → Fin m → A) (c : Fin m → A)
    {k : ℕ} (idx : Fin k → Fin n) : minMismatch u c k ≤ mismatchOnAgree u c idx := by
  unfold minMismatch
  rw [dif_pos (show (Finset.univ : Finset (Fin k → Fin n)).Nonempty from ⟨idx,Finset.mem_univ _⟩)]
  exact Finset.inf'_le _ (Finset.mem_univ idx)

theorem pair_mismatch_budget (u : Fin n → Fin m → A) (c : Fin m → A) (d : ℕ)
    (hd : ∀ i,hammingDist (u i) c ≤ d) (i j : Fin n) :
    hammingDist (u i) (u j)+2*minMismatch u c 2 ≤ 2*d := by
  have h := radius_budget u c d hd ![i,j]
  rw [pair_disagreement] at h
  have hm : minMismatch u c 2 ≤ mismatchOnAgree u c ![i,j] := minMismatch_le_tuple u c ![i,j]
  omega

theorem max_pair_mismatch_budget (u : Fin n → Fin m → A) (c : Fin m → A) (d : ℕ)
    (hd : ∀ i,hammingDist (u i) c ≤ d) :
    maxPairDist u+2*minMismatch u c 2 ≤ 2*d := by
  classical
  by_cases hn : n=0
  · subst n
    simp [maxPairDist,minMismatch]
  · letI : NeZero n := ⟨hn⟩
    obtain ⟨⟨i,j⟩,_,he⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n × Fin n))
      Finset.univ_nonempty (fun p => hammingDist (u p.1) (u p.2))
    change Finset.univ.sup (fun p : Fin n × Fin n => hammingDist (u p.1) (u p.2))+_≤_
    rw [he]
    exact pair_mismatch_budget u c d hd i j

theorem telescoping_lower (f : ℕ → ℝ) (v : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    (∀ k,2 ≤ k → k ≤ r → v ≤ f k-f (k+1)) →
      ((r:ℝ)-1)*v+f (r+1) ≤ f 2 := by
  induction r,hr using Nat.le_induction with
  | base => intro h; norm_num
  | succ k hk ih =>
    intro h
    have hh := ih (fun j hj hjk => h j hj (hjk.trans (Nat.le_succ k)))
    have hs := h (k+1) (by omega) (le_refl _)
    push_cast
    linarith

theorem claim3 (u : Fin n → Fin m → A) (c : Fin m → A) (d : ℕ)
    (hd : ∀ i,hammingDist (u i) c ≤ d) (r : ℕ) (hr : 1 ≤ r) :
    (maxPairDist u : ℝ)-d ≤ d/(2*(r:ℝ)-1) ∨
      ∃ k : ℕ,2 ≤ k ∧ k ≤ r ∧
        (minMismatch u c k : ℝ)-minMismatch u c (k+1) ≤ d/(2*(r:ℝ)-1) := by
  by_cases hfirst : (maxPairDist u : ℝ)-d ≤ d/(2*(r:ℝ)-1)
  · exact Or.inl hfirst
  · right
    by_contra hnone
    push Not at hnone
    have ht := telescoping_lower (fun k => (minMismatch u c k : ℝ))
      ((d:ℝ)/(2*(r:ℝ)-1)) r hr (fun k hk hkr => (hnone k hk hkr).le)
    have hb : (maxPairDist u : ℝ)+2*(minMismatch u c 2 : ℝ) ≤ 2*(d:ℝ) := by
      exact_mod_cast max_pair_mismatch_budget u c d hd
    have hn : (0:ℝ) ≤ minMismatch u c (r+1) := by positivity
    have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
    have hd' : 0 < 2*(r:ℝ)-1 := by linarith
    have hc : (2*(r:ℝ)-1)*((d:ℝ)/(2*(r:ℝ)-1))=d := by field_simp
    have hf := lt_of_not_ge hfirst
    nlinarith

end Queelius.ClosestString

end

section
namespace Queelius.ClosestString.Controls
open ClosestString.PTAS

theorem empty_tuple {A : Type*} [DecidableEq A] {n m : ℕ} (u : Fin n → Fin m → A)
    (idx : Fin 0 → Fin n) : agreeSet u idx=Finset.univ ∧ (agreeSet u idx)ᶜ.card=0 := by
  simp [agreeSet]

theorem constant_tuple {A : Type*} [DecidableEq A] {n m r : ℕ} (u : Fin n → Fin m → A)
    (i : Fin n) : agreeSet u (fun _ : Fin r => i)=Finset.univ := by
  simp [agreeSet]

theorem zero_radius {A : Type*} [DecidableEq A] {n m r : ℕ} (u : Fin n → Fin m → A)
    (c : Fin m → A) (hd : ∀ i,hammingDist (u i) c=0) (idx : Fin r → Fin n) :
    (agreeSet u idx)ᶜ.card=0 := by
  have h := radius_budget u c 0 (fun i => (hd i).le) idx
  omega

theorem attained_two_string_bound :
    (∀ i : Fin 2,hammingDist ((![(fun j : Fin 2 => decide (j=0)),(fun j : Fin 2 => decide (j=1))]) i)
      (fun _ => false)=1) ∧
    (agreeSet ![(fun j : Fin 2 => decide (j=0)),(fun j : Fin 2 => decide (j=1))] id)ᶜ.card=2 := by
  decide

end Queelius.ClosestString.Controls

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS
variable {A : Type*} [DecidableEq A] {n m k r : ℕ}

theorem exists_min_tuple [NeZero n] (u : Fin n → Fin m → A) (c : Fin m → A) (k : ℕ) :
    ∃ idx : Fin k → Fin n, mismatchOnAgree u c idx = minMismatch u c k := by
  classical
  have h : (Finset.univ : Finset (Fin k → Fin n)).Nonempty := Finset.univ_nonempty
  unfold minMismatch
  rw [dif_pos h]
  obtain ⟨idx,hi,he⟩ := Finset.exists_mem_eq_inf' h (mismatchOnAgree u c)
  exact ⟨idx,he.symm⟩

theorem agree_reindex (u : Fin n → Fin m → A) (idx : Fin k → Fin n)
    (e : Fin r → Fin k) (he : Function.Surjective e) :
    agreeSet u (idx ∘ e) = agreeSet u idx := by
  ext j
  simp only [agreeSet,Finset.mem_filter,Finset.mem_univ,true_and,Function.comp_apply]
  constructor
  · intro h a b
    obtain ⟨a',rfl⟩ := he a
    obtain ⟨b',rfl⟩ := he b
    exact h a' b'
  · exact fun h a b => h (e a) (e b)

def padIndex (hk : 0 < k) (hkr : k ≤ r) (a : Fin r) : Fin k :=
  if h : a.val < k then ⟨a.val,h⟩ else ⟨0,hk⟩

theorem pad_surjective (hk : 0 < k) (hkr : k ≤ r) :
    Function.Surjective (padIndex hk hkr) := by
  intro a
  refine ⟨Fin.castLE hkr a,?_⟩
  simp [padIndex,a.isLt]

theorem pad_zero (hk : 0 < k) (hkr : k ≤ r) :
    padIndex hk hkr ⟨0,lt_of_lt_of_le hk hkr⟩ = ⟨0,hk⟩ := by
  simp [padIndex,hk]

theorem mismatch_first (u : Fin n → Fin m → A) (c : Fin m → A)
    (idx : Fin k → Fin n) (a : Fin k) :
    mismatchOnAgree u c idx = ((agreeSet u idx).filter (fun j => u (idx a) j ≠ c j)).card :=
  (distOn_agree u c idx a).symm

theorem agree_cons (u : Fin n → Fin m → A) (idx : Fin k → Fin n)
    (a : Fin k) (l : Fin n) :
    agreeSet u (Fin.cons l idx) = (agreeSet u idx).filter (fun j => u (idx a) j = u l j) := by
  ext j
  simp only [agreeSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h
    exact ⟨fun b d => by simpa using h b.succ d.succ,by simpa using h a.succ 0⟩
  · rintro ⟨h,ha⟩ b d
    have hall : ∀ z : Fin (k+1), u ((Fin.cons l idx : Fin (k+1) → Fin n) z) j = u l j := by
      intro z
      refine Fin.cases ?_ (fun z => ?_) z
      · simp
      · simpa using (h z a).trans ha
    exact (hall b).trans (hall d).symm

theorem mismatch_loss (u : Fin n → Fin m → A) (c : Fin m → A)
    (idx : Fin k → Fin n) (a : Fin k) (l : Fin n) :
    ((agreeSet u idx).filter (fun j => u (idx a) j ≠ u l j ∧ u (idx a) j ≠ c j)).card +
      mismatchOnAgree u c (Fin.cons l idx) = mismatchOnAgree u c idx := by
  classical
  rw [mismatch_first u c (Fin.cons l idx) a.succ,agree_cons u idx a l,mismatch_first u c idx a]
  simp only [Fin.cons_succ]
  have he := Finset.card_filter_add_card_filter_not
    (s := (agreeSet u idx).filter (fun j => u (idx a) j ≠ c j))
    (fun j => u (idx a) j ≠ u l j)
  simpa only [Finset.filter_filter,not_not,and_comm] using he

theorem claim2 [NeZero n] (u : Fin n → Fin m → A) (c : Fin m → A)
    (r k : ℕ) (hk : 2 ≤ k) (hkr : k ≤ r) :
    ∃ idx : Fin r → Fin n, ∀ l : Fin n,
      (((agreeSet u idx).filter (fun j =>
          u (idx ⟨0, by omega⟩) j ≠ u l j ∧ u (idx ⟨0, by omega⟩) j ≠ c j)).card : ℤ)
        ≤ (minMismatch u c k : ℤ) - minMismatch u c (k + 1) := by
  obtain ⟨idx,hidx⟩ := exists_min_tuple u c k
  have hk0 : 0 < k := by omega
  refine ⟨idx ∘ padIndex hk0 hkr,?_⟩
  intro l
  rw [agree_reindex u idx _ (pad_surjective hk0 hkr)]
  simp only [Function.comp_apply,pad_zero]
  have hl := mismatch_loss u c idx ⟨0,hk0⟩ l
  have hm := minMismatch_le_tuple u c (Fin.cons l idx)
  rw [hidx] at hl
  omega

end Queelius.ClosestString
open ClosestString.PTAS
theorem claim2_solution {A : Type*} [DecidableEq A] {n m : ℕ} [NeZero n]
    (u : Fin n → Fin m → A) (c : Fin m → A) (r k : ℕ) (hk : 2 ≤ k) (hkr : k ≤ r) :
    ∃ idx : Fin r → Fin n, ∀ l : Fin n,
      (((agreeSet u idx).filter (fun j =>
          u (idx ⟨0, by omega⟩) j ≠ u l j ∧ u (idx ⟨0, by omega⟩) j ≠ c j)).card : ℤ)
        ≤ (minMismatch u c k : ℤ) - minMismatch u c (k + 1) :=
  Queelius.ClosestString.claim2 u c r k hk hkr

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS
variable {A : Type*} [DecidableEq A] {n m : ℕ}

theorem distance_difference_budget (Q : Finset (Fin m)) (x y c : Fin m → A) :
    distOn Q y x ≤ distOn Q y c + (Q.filter (fun j => x j ≠ y j ∧ x j ≠ c j)).card := by
  classical
  have hs : Q.filter (fun j => y j ≠ x j) ⊆
      (Q.filter (fun j => y j ≠ c j)) ∪ (Q.filter (fun j => x j ≠ y j ∧ x j ≠ c j)) := by
    intro j hj
    obtain ⟨hj,hyx⟩ := Finset.mem_filter.mp hj
    by_cases hyc : y j=c j
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hj,Ne.symm hyx,fun hxc => hyx (hyc.trans hxc.symm)⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj,hyc⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem lemma1 (u : Fin n → Fin m → A) (c : Fin m → A)
    (d : ℕ) (hd : ∀ i,hammingDist (u i) c ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (hρ : (1+1/(2*(r:ℝ)-1))*d < maxPairDist u) :
    ∃ idx : Fin r → Fin n, ∀ l : Fin n,
      (distOn (agreeSet u idx) (u l) (u (idx ⟨0,by omega⟩)) : ℝ) -
        distOn (agreeSet u idx) (u l) c ≤ d/(2*(r:ℝ)-1) := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hden : 0 < 2*(r:ℝ)-1 := by linarith
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hp : 0 ≤ (1+1/(2*(r:ℝ)-1))*(d:ℝ) := by positivity
    simp [maxPairDist,one_div] at hρ hp
    linarith
  letI : NeZero n := ⟨hn⟩
  have he : (1+1/(2*(r:ℝ)-1))*(d:ℝ)=d+d/(2*(r:ℝ)-1) := by ring
  rw [he] at hρ
  obtain hfirst | ⟨k,hk,hkr,hgap⟩ := claim3 u c d hd r hr
  · linarith
  · obtain ⟨idx,hidx⟩ := claim2 u c r k hk hkr
    refine ⟨idx,?_⟩
    intro l
    have hbudget : (distOn (agreeSet u idx) (u l) (u (idx ⟨0,by omega⟩)) : ℝ) ≤
        (distOn (agreeSet u idx) (u l) c : ℝ) +
        (((agreeSet u idx).filter (fun j =>
          u (idx ⟨0,by omega⟩) j ≠ u l j ∧ u (idx ⟨0,by omega⟩) j ≠ c j)).card : ℝ) := by
      exact_mod_cast distance_difference_budget (agreeSet u idx) (u (idx ⟨0,by omega⟩)) (u l) c
    have hl : (((agreeSet u idx).filter (fun j =>
          u (idx ⟨0,by omega⟩) j ≠ u l j ∧ u (idx ⟨0,by omega⟩) j ≠ c j)).card : ℝ) ≤
        (minMismatch u c k : ℝ) - minMismatch u c (k+1) := by
      exact_mod_cast hidx l
    linarith

end Queelius.ClosestString

end

section
namespace Queelius.ClosestString.Controls
open ClosestString.PTAS

def threeStrings (i j : Fin 3) : Bool := decide (i=j)

theorem tight_lost_coordinate :
    ((agreeSet threeStrings ![0,1]).filter (fun j =>
      threeStrings 0 j ≠ threeStrings 2 j ∧ threeStrings 0 j ≠ true)).card = 1 := by decide

theorem tight_mismatch_drop :
    mismatchOnAgree threeStrings (fun _ => true) ![0,1] = 1 ∧
      mismatchOnAgree threeStrings (fun _ => true) (Fin.cons 2 ![0,1]) = 0 := by decide

theorem padding_preserves_agreement {A : Type*} [DecidableEq A] {n m k r : ℕ}
    (u : Fin n → Fin m → A) (idx : Fin k → Fin n) (hk : 0 < k) (hkr : k ≤ r) :
    agreeSet u (idx ∘ padIndex hk hkr) = agreeSet u idx :=
  agree_reindex u idx _ (pad_surjective hk hkr)

theorem zero_length_mismatch {A : Type*} [DecidableEq A] {n k : ℕ}
    (u : Fin n → Fin 0 → A) (c : Fin 0 → A) (idx : Fin k → Fin n) :
    mismatchOnAgree u c idx=0 := by simp [mismatchOnAgree,agreeSet]

end Queelius.ClosestString.Controls

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS
variable {A : Type*} [DecidableEq A] {L : ℕ}

theorem distOn_symm (P : Finset (Fin L)) (u v : Fin L → A) : distOn P u v=distOn P v u := by
  simp only [distOn,ne_comm]

theorem distOn_splice_left (P : Finset (Fin L)) (x f t : Fin L → A) :
    distOn P (splice P x f) t=distOn P x t := by
  unfold distOn
  congr 1
  apply Finset.filter_congr
  intro j hj
  simp [splice,hj]

theorem distOn_splice_right (P : Finset (Fin L)) (x f t : Fin L → A) :
    distOn Pᶜ (splice P x f) t=distOn Pᶜ f t := by
  unfold distOn
  congr 1
  apply Finset.filter_congr
  intro j hj
  simp only [Finset.mem_compl] at hj
  simp [splice,hj]

theorem hamming_splice (P : Finset (Fin L)) (x f t : Fin L → A) :
    hammingDist (splice P x f) t=distOn P t x+distOn Pᶜ t f := by
  rw [distance_partition _ _ P,distOn_splice_left,distOn_splice_right,
    distOn_symm P x t,distOn_symm Pᶜ f t]

theorem splice_distance_change (Q : Finset (Fin L)) (s f t : Fin L → A) :
    (hammingDist (splice Qᶜ s f) t : ℝ)=hammingDist s t+
      ((distOn Q t f : ℝ)-distOn Q t s) := by
  rw [hamming_splice,compl_compl,distance_partition s t Qᶜ]
  simp only [compl_compl,Nat.cast_add]
  rw [distOn_symm Qᶜ s t,distOn_symm Q s t]
  ring

theorem opt8_le_witness {n : ℕ} [Fintype A] [Nonempty A]
    (t : Fin n → Fin L → A) (P : Finset (Fin L)) (b : Fin n → ℕ) (x : Fin L → A) :
    opt8 t P b≤Finset.univ.sup (fun i => distOn P (t i) x+b i) := by
  exact Finset.inf'_le _ (Finset.mem_univ x)

theorem opt8_real_bound {n : ℕ} [NeZero n] [Fintype A] [Nonempty A]
    (t : Fin n → Fin L → A) (P : Finset (Fin L)) (b : Fin n → ℕ) (x : Fin L → A)
    (B : ℝ) (hb : ∀ i,(distOn P (t i) x : ℝ)+b i≤B) : (opt8 t P b : ℝ)≤B := by
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i => distOn P (t i) x+b i)
  have ho : (opt8 t P b : ℝ)≤(Finset.univ.sup (fun i => distOn P (t i) x+b i) : ℕ) := by
    exact_mod_cast opt8_le_witness t P b x
  rw [he,Nat.cast_add] at ho
  exact ho.trans (hb j)

theorem final_distance_bound {n : ℕ} [Fintype A] [Nonempty A]
    (s f : Fin L → A) (t t' : Fin n → Fin L → A) (d : ℕ) (hd : ∀ i,hammingDist s (t i)≤d)
    (Q : Finset (Fin L)) (r : ℕ) (hr : 1≤r)
    (hFact1 : ∀ l,(distOn Q (t l) f : ℝ)-distOn Q (t l) s≤d/(2*(r:ℝ)-1))
    (hP : Qᶜ.card≤r*d) (eps : ℝ) (heps : 0≤eps)
    (hFact2 : ∀ i,(hammingDist (splice Qᶜ s f) (t' i) : ℝ)≤
      hammingDist (splice Qᶜ s f) (t i)+2*eps*Qᶜ.card)
    (x : Fin L → A)
    (hx : ∀ i,(distOn Qᶜ (t' i) x : ℝ)+distOn Q (t' i) f≤
      opt8 t' Qᶜ (fun i => distOn Q (t' i) f)+eps*Qᶜ.card) :
    ∀ i,(hammingDist (splice Qᶜ x f) (t' i) : ℝ)≤
      (1+1/(2*(r:ℝ)-1)+3*eps*r)*d := by
  intro i
  have hn : n≠0 := by have := i.isLt; omega
  letI : NeZero n := ⟨hn⟩
  have hdist (j : Fin n) : (hammingDist (splice Qᶜ s f) (t j) : ℝ)≤
      (d:ℝ)+d/(2*(r:ℝ)-1) := by
    rw [splice_distance_change]
    have hd' : (hammingDist s (t j) : ℝ)≤d := by exact_mod_cast hd j
    linarith [hFact1 j]
  have ho := opt8_real_bound t' Qᶜ (fun j => distOn Q (t' j) f) s
    ((d:ℝ)+d/(2*(r:ℝ)-1)+2*eps*Qᶜ.card) (fun j => by
      have hh : (hammingDist (splice Qᶜ s f) (t' j) : ℝ)≤(d:ℝ)+d/(2*(r:ℝ)-1)+2*eps*Qᶜ.card := by linarith [hFact2 j,hdist j]
      simpa only [hamming_splice,compl_compl,Nat.cast_add] using hh)
  rw [hamming_splice,compl_compl,Nat.cast_add]
  have hp' : (Qᶜ.card : ℝ)≤(r:ℝ)*d := by exact_mod_cast hP
  have hm := mul_le_mul_of_nonneg_left hp' (show 0≤3*eps by positivity)
  have ht := hx i
  calc
    _ ≤ (d:ℝ)+d/(2*(r:ℝ)-1)+3*eps*Qᶜ.card := by linarith
    _ ≤ (d:ℝ)+d/(2*(r:ℝ)-1)+3*eps*((r:ℝ)*d) := by linarith
    _ = _ := by ring

end Queelius.ClosestString

end

section
open ClosestString.PTAS

theorem eq15_solution {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {n L : ℕ}
    (s f : Fin L → A) (t t' : Fin n → Fin L → A) (d : ℕ) (hd : ∀ i, hammingDist s (t i) ≤ d)
    (Q : Finset (Fin L)) (r : ℕ) (hr : 1 ≤ r)
    (hFact1 : ∀ l, (distOn Q (t l) f : ℝ) - distOn Q (t l) s ≤ d / (2 * (r : ℝ) - 1))
    (hP : Qᶜ.card ≤ r * d) (ε : ℝ) (hε : 0 ≤ ε)
    (hFact2 : ∀ i, (hammingDist (splice Qᶜ s f) (t' i) : ℝ)
      ≤ hammingDist (splice Qᶜ s f) (t i) + 2 * ε * Qᶜ.card)
    (x : Fin L → A)
    (hx : ∀ i, (distOn Qᶜ (t' i) x : ℝ) + distOn Q (t' i) f
      ≤ opt8 t' Qᶜ (fun i => distOn Q (t' i) f) + ε * Qᶜ.card) :
    ∀ i, (hammingDist (splice Qᶜ x f) (t' i) : ℝ)
      ≤ (1 + 1 / (2 * (r : ℝ) - 1) + 3 * ε * r) * d :=
  Queelius.ClosestString.final_distance_bound s f t t' d hd Q r hr hFact1 hP ε hε hFact2 x hx

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem minDistSub_le_witness {m L : ℕ} [NeZero L] (hL : L ≤ m)
    (s : Fin m → A) (c : Fin L → A) (p : Start m L) :
    minDistSub c s ≤ hammingDist c (substr s p) := by
  rw [minDistSub,dif_pos (start_nonempty hL)]
  exact Finset.inf'_le _ (Finset.mem_univ p)

theorem cost_le_witnesses {n m L : ℕ} [NeZero L] (hL : L ≤ m)
    (S : Fin n → Fin m → A) (c : Fin L → A) (p : Fin n → Start m L) (B : ℕ)
    (hB : ∀ i,hammingDist c (substr (S i) (p i)) ≤ B) : cost S c ≤ B := by
  apply Finset.sup_le
  intro i hi
  exact (minDistSub_le_witness hL (S i) c (p i)).trans (hB i)

theorem cost_real_le_witnesses {n m L : ℕ} [NeZero n] [NeZero L] (hL : L ≤ m)
    (S : Fin n → Fin m → A) (c : Fin L → A) (p : Fin n → Start m L) (B : ℝ)
    (hB : ∀ i,(hammingDist c (substr (S i) (p i)) : ℝ) ≤ B) : (cost S c : ℝ) ≤ B := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i => minDistSub c (S i))
  change ((Finset.univ.sup (fun i => minDistSub c (S i)) : ℕ) : ℝ) ≤ B
  rw [he]
  have hh : (minDistSub c (S i) : ℝ) ≤ hammingDist c (substr (S i) (p i)) := by
    exact_mod_cast minDistSub_le_witness hL (S i) c (p i)
  exact hh.trans (hB i)

theorem closest_cost_le_candidate {n m L r : ℕ} [NeZero n] [NeZero L] [NeZero r]
    (S : Fin n → Fin m → A) (hL : L ≤ m) (eps : ℝ) (solver : Solver A n L)
    (omega : Sample n m L r (sampleSize n m eps))
    (c : Cand A n m L r (sampleSize n m eps)) :
    cost S (closestSubstring S hL r eps solver omega) ≤ cost S (candStr S hL eps solver omega c) := by
  exact (Finset.univ.exists_min_image (fun c => cost S (candStr S hL eps solver omega c))
    (cand_nonempty hL)).choose_spec.2 c (Finset.mem_univ c)

theorem bestStart_minimizes {n m L r k : ℕ} [NeZero L] [NeZero r]
    (S : Fin n → Fin m → A) (hL : L ≤ m) (tau : AdmTuple n m L r)
    (y : Fin k → A) (R : Fin k → Fin L) (i : Fin n) (p : Start m L) :
    score S tau y R i (bestStart S hL tau y R i) ≤ score S tau y R i p := by
  have hm := Finset.min'_mem
    (Finset.univ.filter (fun p => score S tau y R i p =
      Finset.univ.inf' (start_nonempty hL) (score S tau y R i)))
    (show (Finset.univ.filter (fun p => score S tau y R i p =
      Finset.univ.inf' (start_nonempty hL) (score S tau y R i))).Nonempty from by
      obtain ⟨p,hp,he⟩ := Finset.exists_mem_eq_inf' (start_nonempty hL) (score S tau y R i)
      exact ⟨p,by simp [he]⟩)
  have he : score S tau y R i (bestStart S hL tau y R i)=
      Finset.univ.inf' (start_nonempty hL) (score S tau y R i) := (Finset.mem_filter.mp hm).2
  rw [he]
  exact Finset.inf'_le _ (Finset.mem_univ p)

theorem algorithm_bound_from_good_tuple {n m L r : ℕ} [NeZero n] [NeZero L] [NeZero r]
    (S : Fin n → Fin m → A) (hL : L ≤ m) (eps : ℝ) (heps : 0 ≤ eps)
    (solver : Solver A n L) (hsolver : IsApproxSolver eps solver)
    (s : Fin L → A) (t : Fin n → Start m L) (d : ℕ)
    (hd : ∀ i,hammingDist s (substr (S i) (t i)) ≤ d)
    (tau : AdmTuple n m L r) (hr : 1 ≤ r)
    (hFact1 : ∀ l,(distOn (agreeQ S tau) (substr (S l) (t l)) (firstStr S tau) : ℝ)-
      distOn (agreeQ S tau) (substr (S l) (t l)) s ≤ d/(2*(r:ℝ)-1))
    (hP : (diffP S tau).card ≤ r*d)
    (omega : Sample n m L r (sampleSize n m eps))
    (hFact2 : ∀ i,(hammingDist (splice (diffP S tau) s (firstStr S tau))
        (substr (S i) (bestStart S hL tau (fun a => s (omega tau a)) (omega tau) i)) : ℝ) ≤ 
      hammingDist (splice (diffP S tau) s (firstStr S tau)) (substr (S i) (t i))+
        2*eps*(diffP S tau).card) :
    (cost S (closestSubstring S hL r eps solver omega) : ℝ) ≤ 
      (1+1/(2*(r:ℝ)-1)+3*eps*r)*d := by
  let y := fun a => s (omega tau a)
  let starts := bestStart S hL tau y (omega tau)
  let selected := fun i => substr (S i) (starts i)
  have hd' := final_distance_bound s (firstStr S tau) (fun i => substr (S i) (t i)) selected d hd
    (agreeQ S tau) r hr hFact1 hP eps heps hFact2
    (solver selected (diffP S tau) (fun i => distOn (agreeQ S tau) (selected i) (firstStr S tau)))
    (hsolver selected (diffP S tau) (fun i => distOn (agreeQ S tau) (selected i) (firstStr S tau)))
  have hc := cost_real_le_witnesses hL S (candidate1 S hL solver tau y (omega tau)) starts
    ((1+1/(2*(r:ℝ)-1)+3*eps*r)*d) hd'
  have hmin : (cost S (closestSubstring S hL r eps solver omega) : ℝ) ≤ 
      cost S (candidate1 S hL solver tau y (omega tau)) := by
    exact_mod_cast closest_cost_le_candidate S hL eps solver omega (Sum.inl (tau,y))
  exact hmin.trans hc

end Queelius.ClosestString

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem optimal_center_exists {n m L : ℕ} (S : Fin n → Fin m → A) :
    ∃ s : Fin L → A,cost S s=dOpt L S := by
  obtain ⟨s,hs,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun s : Fin L → A => cost S s)
  exact ⟨s,he.symm⟩

theorem optimal_substrings {n m L : ℕ} [NeZero L] (S : Fin n → Fin m → A)
    (hL : L ≤ m) (s : Fin L → A) :
    ∃ t : Fin n → Start m L,∀ i,hammingDist s (substr (S i) (t i)) ≤ cost S s := by
  classical
  have he (i : Fin n) : ∃ p : Start m L,hammingDist s (substr (S i) p)=minDistSub s (S i) := by
    obtain ⟨p,hp,hv⟩ := Finset.exists_mem_eq_inf' (start_nonempty hL)
      (fun p => hammingDist s (substr (S i) p))
    refine ⟨p,?_⟩
    rw [minDistSub,dif_pos (start_nonempty hL)]
    exact hv.symm
  choose t ht using he
  refine ⟨t,fun i => ?_⟩
  rw [ht i]
  exact Finset.le_sup (f:=fun i => minDistSub s (S i)) (Finset.mem_univ i)

def liftTuple {n m L r : ℕ} (t : Fin n → Start m L) (idx : Fin r → Fin n) : AdmTuple n m L r :=
  ⟨fun a => (idx a,t (idx a)),fun a b h => congrArg t h⟩

theorem tupleStr_lift {n m L r : ℕ} (S : Fin n → Fin m → A)
    (t : Fin n → Start m L) (idx : Fin r → Fin n) (a : Fin r) :
    tupleStr S (liftTuple t idx) a=substr (S (idx a)) (t (idx a)) := rfl

theorem agreeQ_lift {n m L r : ℕ} (S : Fin n → Fin m → A)
    (t : Fin n → Start m L) (idx : Fin r → Fin n) :
    agreeQ S (liftTuple t idx)=agreeSet (fun i => substr (S i) (t i)) idx := rfl

theorem firstStr_lift {n m L r : ℕ} [NeZero r] (S : Fin n → Fin m → A)
    (t : Fin n → Start m L) (idx : Fin r → Fin n) :
    firstStr S (liftTuple t idx)=substr (S (idx 0)) (t (idx 0)) := rfl

theorem large_pair_good_tuple {n m L r : ℕ} [NeZero r]
    (S : Fin n → Fin m → A) (t : Fin n → Start m L) (s : Fin L → A) (d : ℕ)
    (hd : ∀ i,hammingDist s (substr (S i) (t i)) ≤ d) (hr : 1 ≤ r)
    (hlarge : (1+1/(2*(r:ℝ)-1))*d < maxPairDist (fun i => substr (S i) (t i))) :
    ∃ tau : AdmTuple n m L r,
      (∀ i,(distOn (agreeQ S tau) (substr (S i) (t i)) (firstStr S tau) : ℝ)-
        distOn (agreeQ S tau) (substr (S i) (t i)) s ≤ d/(2*(r:ℝ)-1)) ∧
      (diffP S tau).card ≤ r*d := by
  have hd' : ∀ i,hammingDist (substr (S i) (t i)) s ≤ d := fun i => by
    simpa only [hammingDist_comm] using hd i
  obtain ⟨idx,hidx⟩ := lemma1 (fun i => substr (S i) (t i)) s d hd' r hr hlarge
  refine ⟨liftTuple t idx,?_,?_⟩
  · have hz : (⟨0,by omega⟩ : Fin r)=0 := Fin.ext (by simp)
    simpa only [agreeQ_lift,firstStr_lift,hz] using hidx
  · exact disagreement_solution (fun i => substr (S i) (t i)) s d hd' r idx

theorem small_pair_algorithm_bound {n m L r : ℕ} [NeZero n] [NeZero L] [NeZero r]
    (S : Fin n → Fin m → A) (hL : L ≤ m) (t : Fin n → Start m L)
    (eps : ℝ) (solver : Solver A n L) (omega : Sample n m L r (sampleSize n m eps)) :
    cost S (closestSubstring S hL r eps solver omega) ≤ maxPairDist (fun i => substr (S i) (t i)) := by
  apply (closest_cost_le_candidate S hL eps solver omega (Sum.inr (t 0))).trans
  apply cost_le_witnesses hL S _ t
  intro i
  exact Finset.le_sup (f:=fun p : Fin n×Fin n =>
    hammingDist (substr (S p.1) (t p.1)) (substr (S p.2) (t p.2))) (Finset.mem_univ (0,i))

end Queelius.ClosestString

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem deterministic_reduction {n m L r : ℕ} [NeZero n] [NeZero L] [NeZero r]
    (S : Fin n → Fin m → A) (hL : L ≤ m) (eps : ℝ) (heps : 0 ≤ eps)
    (solver : Solver A n L) (hsolver : IsApproxSolver eps solver) (hr : 1 ≤ r) :
    ∃ (s : Fin L → A) (t : Fin n → Start m L) (tau : AdmTuple n m L r),
      cost S s=dOpt L S ∧
      (∀ i,hammingDist s (substr (S i) (t i)) ≤ dOpt L S) ∧
      ∀ omega : Sample n m L r (sampleSize n m eps),
        (∀ i,(hammingDist (splice (diffP S tau) s (firstStr S tau))
          (substr (S i) (bestStart S hL tau (fun a => s (omega tau a)) (omega tau) i)) : ℝ) ≤
          hammingDist (splice (diffP S tau) s (firstStr S tau)) (substr (S i) (t i))+
            2*eps*(diffP S tau).card) →
        (cost S (closestSubstring S hL r eps solver omega) : ℝ) ≤
          (1+1/(2*(r:ℝ)-1)+3*eps*r)*dOpt L S := by
  obtain ⟨s,hs⟩ := optimal_center_exists (L:=L) S
  obtain ⟨t,ht⟩ := optimal_substrings S hL s
  rw [hs] at ht
  by_cases hsmall : (maxPairDist (fun i => substr (S i) (t i)) : ℝ) ≤
      (1+1/(2*(r:ℝ)-1))*dOpt L S
  · refine ⟨s,t,liftTuple t (fun _ => 0),hs,ht,?_⟩
    intro omega hevent
    have hcost : (cost S (closestSubstring S hL r eps solver omega) : ℝ) ≤
        maxPairDist (fun i => substr (S i) (t i)) := by
      exact_mod_cast small_pair_algorithm_bound S hL t eps solver omega
    have hextra : 0 ≤ 3*eps*(r:ℝ)*(dOpt L S : ℝ) := by positivity
    nlinarith
  · have hlarge := lt_of_not_ge hsmall
    obtain ⟨tau,hf1,hP⟩ := large_pair_good_tuple S t s (dOpt L S) ht hr hlarge
    exact ⟨s,t,tau,hs,ht,fun omega hevent =>
      algorithm_bound_from_good_tuple S hL eps heps solver hsolver s t (dOpt L S) ht tau hr hf1 hP omega hevent⟩

theorem candidate_card_bound (n m L r k : ℕ) :
    Fintype.card (Cand A n m L r k) ≤ (n*m)^r*(Fintype.card A)^k+m := by
  have hs : Fintype.card (Start m L) ≤ m := by
    simpa using Fintype.card_subtype_le (fun p : Fin m => p.val+L ≤ m)
  have ht : Fintype.card (AdmTuple n m L r) ≤ (n*Fintype.card (Start m L))^r := by
    simpa only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin] using
      Fintype.card_subtype_le (@Admissible n m L r)
  change Fintype.card ((AdmTuple n m L r × (Fin k → A)) ⊕ Start m L) ≤ _
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  calc
    _ ≤ (n*Fintype.card (Start m L))^r*(Fintype.card A)^k+Fintype.card (Start m L) := by gcongr
    _ ≤ (n*m)^r*(Fintype.card A)^k+m := by gcongr

end Queelius.ClosestString

end

section
namespace Queelius.ClosestString.Controls
open ClosestString.PTAS

theorem zero_optimum_exact_success {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {n m L r : ℕ} [NeZero n] [NeZero L] [NeZero r]
    (S : Fin n → Fin m → A) (hL : L ≤ m) (eps : ℝ) (solver : Solver A n L)
    (omega : Sample n m L r (sampleSize n m eps)) (hzero : dOpt L S=0) :
    cost S (closestSubstring S hL r eps solver omega)=0 := by
  obtain ⟨s,hs⟩ := optimal_center_exists (L:=L) S
  obtain ⟨t,ht⟩ := optimal_substrings S hL s
  rw [hs,hzero] at ht
  have hpair : maxPairDist (fun i => substr (S i) (t i)) ≤ 0 := by
    apply Finset.sup_le
    intro ij hij
    exact (hammingDist_triangle_left (substr (S ij.1) (t ij.1))
      (substr (S ij.2) (t ij.2)) s).trans (by simpa using Nat.add_le_add (ht ij.1) (ht ij.2))
  exact Nat.eq_zero_of_le_zero ((small_pair_algorithm_bound S hL t eps solver omega).trans hpair)

theorem fixed_positions_can_force_error :
    hammingDist (splice ({0} : Finset (Fin 2)) ![false,false] ![true,true]) ![false,false]=1 := by
  decide

end Queelius.ClosestString.Controls

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS

/-- A constant alphabet raised to a rounded logarithmic sample size grows polynomially. -/
theorem rounded_log_power_bound (a x : ℕ) (ha : 1 ≤ a) (hx : 1 ≤ x) (q : ℝ) (hq : 0 ≤ q) :
    a ^ ⌈q * Real.log (x:ℝ)⌉₊ ≤ a * x ^ ⌈q * Real.log (a:ℝ)⌉₊ := by
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hap : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have hxp : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hc : (⌈q * Real.log (x:ℝ)⌉₊ : ℝ) ≤ q * Real.log (x:ℝ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hq (Real.log_nonneg hx1))).le
  have he : (a:ℝ) ^ (q * Real.log (x:ℝ)) = (x:ℝ) ^ (q * Real.log (a:ℝ)) := by
    rw [Real.rpow_def_of_pos hap,Real.rpow_def_of_pos hxp]
    congr 1
    ring
  have hreal : (a:ℝ) ^ ⌈q * Real.log (x:ℝ)⌉₊ ≤ (a:ℝ) * (x:ℝ) ^ ⌈q * Real.log (a:ℝ)⌉₊ := by
    calc
      _ = (a:ℝ) ^ (⌈q * Real.log (x:ℝ)⌉₊ : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (a:ℝ) ^ (q * Real.log (x:ℝ) + 1) := Real.rpow_le_rpow_of_exponent_le ha1 hc
      _ = (x:ℝ) ^ (q * Real.log (a:ℝ)) * a := by rw [Real.rpow_add hap,Real.rpow_one,he]
      _ ≤ (x:ℝ) ^ (⌈q * Real.log (a:ℝ)⌉₊ : ℝ) * a :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1 (Nat.le_ceil _)) hap.le
      _ = _ := by rw [Real.rpow_natCast]; ring
  exact_mod_cast hreal

noncomputable def candidateExponent (a r : ℕ) (eps : ℝ) : ℕ :=
  a + r + ⌈4 / eps^2 * Real.log (a:ℝ)⌉₊ + 2

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem sampled_candidate_card_polynomial (r : ℕ) (eps : ℝ)
    (n m L : ℕ) (hn : 1 ≤ n) (hL0 : 1 ≤ L) (hLm : L ≤ m) :
    Fintype.card (Cand A n m L r (sampleSize n m eps)) ≤
      candidateExponent (Fintype.card A) r eps *
        (n*m+1) ^ candidateExponent (Fintype.card A) r eps := by
  let a := Fintype.card A
  let d := ⌈4 / eps^2 * Real.log (a:ℝ)⌉₊
  let c := candidateExponent a r eps
  have ha : 1 ≤ a := Fintype.card_pos_iff.mpr inferInstance
  have hm : 1 ≤ m := hL0.trans hLm
  have hx : 1 ≤ n*m := by nlinarith
  have hs : a ^ sampleSize n m eps ≤ a * (n*m)^d := by
    simpa [sampleSize,Nat.cast_mul,d] using rounded_log_power_bound a (n*m) ha hx
      (4/eps^2) (by positivity)
  have hmc : m ≤ n*m := by nlinarith
  have hexp : r+d ≤ c := by dsimp [c,candidateExponent,d]; omega
  have hc1 : 1 ≤ c := by dsimp [c,candidateExponent]; omega
  have hac : a+1 ≤ c := by dsimp [c,candidateExponent]; omega
  have hbase : (n*m)^(r+d) ≤ (n*m+1)^c := by
    apply (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
    exact Nat.pow_le_pow_right (by omega) hexp
  have hmexp : m ≤ (n*m+1)^c := by
    apply hmc.trans
    apply (Nat.le_succ _).trans
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ n*m+1) hc1
  calc
    _ ≤ (n*m)^r*a^sampleSize n m eps+m := candidate_card_bound n m L r _
    _ ≤ (n*m)^r*(a*(n*m)^d)+m := by gcongr
    _ = a*(n*m)^(r+d)+m := by rw [pow_add]; ring
    _ ≤ a*(n*m+1)^c+(n*m+1)^c := by gcongr
    _ = (a+1)*(n*m+1)^c := by ring
    _ ≤ c*(n*m+1)^c := Nat.mul_le_mul_right _ hac

 theorem polynomial_candidate_guarantee (r : ℕ) (eps : ℝ) :
    ∃ c : ℕ, ∀ (n m L : ℕ), 1 ≤ n → 1 ≤ L → L ≤ m →
      Fintype.card (Cand A n m L r (sampleSize n m eps)) ≤ c * (n*m+1)^c :=
  ⟨candidateExponent (Fintype.card A) r eps, sampled_candidate_card_polynomial r eps⟩

end Queelius.ClosestString

open ClosestString.PTAS in
 theorem polynomial_solution {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (r : ℕ) [NeZero r]
    (hr : 2 ≤ r) (eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℕ, ∀ (n m L : ℕ), 1 ≤ n → 1 ≤ L → L ≤ m →
      Fintype.card (Cand A n m L r (sampleSize n m eps)) ≤ c * (n*m+1)^c :=
  Queelius.ClosestString.polynomial_candidate_guarantee r eps

end

section
namespace Queelius.ClosestString
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

 theorem iid_bounded_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hb : ∀ x, f x ∈ Set.Icc (0:ℝ) 1) (k : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    let p := ∫ x, f x ∂μ
    let Pr := Measure.pi (fun _ : Fin k => μ)
    Pr.real {R | (∑ i, f (R i)) ≤ (k:ℝ)*p-eps*k} ≤ Real.exp (-2*eps^2*k) ∧
      Pr.real {R | (k:ℝ)*p+eps*k ≤ ∑ i, f (R i)} ≤ Real.exp (-2*eps^2*k) := by
  dsimp only
  let p := ∫ x, f x ∂μ
  let Pr := Measure.pi (fun _ : Fin k => μ)
  let Y := fun i : Fin k => fun R : Fin k → Ω => f (R i)-p
  have hind : iIndepFun Y Pr :=
    iIndepFun_pi (X := fun _ => fun x => f x-p) (fun _ => (hf.sub_const p).aemeasurable)
  have hsub (i : Fin k) : HasSubgaussianMGF (Y i) (1/4:ℝ≥0) Pr := by
    have h := hasSubgaussianMGF_of_mem_Icc
      (μ := Pr) ((hf.comp (measurable_pi_apply i)).aemeasurable)
      (ae_of_all _ (fun R => hb (R i)))
    have hi : (∫ R, f (R i) ∂Pr) = p := integral_comp_eval hf.aestronglyMeasurable
    norm_num [Y,hi] at h ⊢
    exact h
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (fun i _ => hsub i)
  have hright := hs.measure_ge_le (ε := eps*k) (by positivity)
  have hleft := hs.neg.measure_ge_le (ε := eps*k) (by positivity)
  have heq (R : Fin k → Ω) : (∑ i, Y i R) = (∑ i, f (R i))-(k:ℝ)*p := by
    simp [Y,Finset.sum_sub_distrib]
  have er : {R | eps*(k:ℝ) ≤ ∑ i, Y i R} = {R | (k:ℝ)*p+eps*k ≤ ∑ i, f (R i)} := by
    ext R
    simp only [Set.mem_ofPred_eq]
    rw [heq]
    constructor <;> intro h <;> linarith
  have el : {R | eps*(k:ℝ) ≤ -(∑ i, Y i R)} = {R | (∑ i, f (R i)) ≤ (k:ℝ)*p-eps*k} := by
    ext R
    simp only [Set.mem_ofPred_eq]
    rw [heq]
    constructor <;> intro h <;> linarith
  have hn : (-(eps*(k:ℝ))^2 / (2 * (↑(∑ _i : Fin k, (1/4:ℝ≥0)) : ℝ))) = -2*eps^2*k := by
    by_cases hk : k=0
    · simp [hk]
    · have hk' : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
      field_simp
      <;> ring
  rw [er,hn] at hright
  change Pr.real {R | eps*(k:ℝ) ≤ -(∑ i, Y i R)} ≤ _ at hleft
  rw [el,hn] at hleft
  exact ⟨hleft,hright⟩

end Queelius.ClosestString

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

variable {A : Type*} [DecidableEq A] {L : ℕ}

def mismatchIndicator (u v : Fin L → A) (j : Fin L) : ℝ :=
  if u j ≠ v j then 1 else 0

 theorem mismatch_bounded (u v : Fin L → A) (j : Fin L) :
    mismatchIndicator u v j ∈ Set.Icc (0:ℝ) 1 := by
  unfold mismatchIndicator
  split_ifs <;> norm_num

 theorem mismatch_measurable (u v : Fin L → A) : Measurable (mismatchIndicator u v) :=
  measurable_of_countable _

 theorem mismatch_mean (u v : Fin L → A) (P : Finset (Fin L)) (hP : P.Nonempty) :
    (∫ j, mismatchIndicator u v j ∂(PMF.uniformOfFinset P hP).toMeasure) =
      (distOn P u v : ℝ) / P.card := by
  have hm : MeasurableSet {j : Fin L | u j ≠ v j} := (Set.to_countable _).measurableSet
  have he : mismatchIndicator u v = {j : Fin L | u j ≠ v j}.indicator (fun _ => (1:ℝ)) := by
    funext j
    simp [mismatchIndicator,Set.indicator_apply]
  rw [he,integral_indicator_const _ hm]
  simp only [smul_eq_mul,mul_one,Measure.real]
  rw [PMF.toMeasure_uniformOfFinset_apply hP _ hm]
  simp [distOn,ENNReal.toReal_div]

 theorem sample_as_sum {k : ℕ} (R : Fin k → Fin L) (u v : Fin L → A) :
    (distSample R u v : ℝ) = ∑ i, mismatchIndicator u v (R i) := by
  simp [distSample,mismatchIndicator,Finset.card_filter]

 theorem mismatch_sum_tails (u v : Fin L → A) (P : Finset (Fin L)) (hP : P.Nonempty)
    (k : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    let Pr := Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
    Pr.real {R | (distSample R u v : ℝ) ≤ (k:ℝ)*((distOn P u v : ℝ)/P.card)-eps*k}
      ≤ Real.exp (-2*eps^2*k) ∧
    Pr.real {R | (k:ℝ)*((distOn P u v : ℝ)/P.card)+eps*k ≤ (distSample R u v : ℝ)}
      ≤ Real.exp (-2*eps^2*k) := by
  simpa only [mismatch_mean,← sample_as_sum] using
    iid_bounded_tails (PMF.uniformOfFinset P hP).toMeasure (mismatchIndicator u v)
      (mismatch_measurable u v) (mismatch_bounded u v) k eps heps

end Queelius.ClosestString

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {A : Type*} [DecidableEq A] {L : ℕ}

 theorem scaled_sample_tails (u v : Fin L → A) (P : Finset (Fin L)) (hP : P.Nonempty)
    (k : ℕ) (hk : 0 < k) (eps : ℝ) (heps : 0 ≤ eps) :
    let Pr := Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
    Pr.real {R | (P.card/k:ℝ)*distSample R u v+distOn Pᶜ u v ≤ (hammingDist u v:ℝ)-eps*P.card}
      ≤ Real.exp (-2*eps^2*k) ∧
    Pr.real {R | (hammingDist u v:ℝ)+eps*P.card ≤ (P.card/k:ℝ)*distSample R u v+distOn Pᶜ u v}
      ≤ Real.exp (-2*eps^2*k) := by
  have hp : (0:ℝ) < P.card := Nat.cast_pos.mpr hP.card_pos
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have ha : (0:ℝ) < P.card/k := div_pos hp hk'
  have hd : (hammingDist u v:ℝ) = (distOn P u v:ℝ)+(distOn Pᶜ u v:ℝ) := by
    exact_mod_cast distance_partition u v P
  have hminus : (P.card/k:ℝ)*((k:ℝ)*((distOn P u v:ℝ)/P.card)-eps*k) =
      (distOn P u v:ℝ)-eps*P.card := by field_simp
  have hplus : (P.card/k:ℝ)*((k:ℝ)*((distOn P u v:ℝ)/P.card)+eps*k) =
      (distOn P u v:ℝ)+eps*P.card := by field_simp
  have hl (R : Fin k → Fin L) :
      (P.card/k:ℝ)*distSample R u v+distOn Pᶜ u v ≤ (hammingDist u v:ℝ)-eps*P.card ↔
        (distSample R u v:ℝ) ≤ (k:ℝ)*((distOn P u v:ℝ)/P.card)-eps*k := by
    constructor
    · intro h
      apply (mul_le_mul_iff_of_pos_left ha).mp
      rw [hminus, hd] at *
      linarith
    · intro h
      have hm := mul_le_mul_of_nonneg_left h ha.le
      rw [hminus] at hm
      rw [hd]
      linarith
  have hr (R : Fin k → Fin L) :
      (hammingDist u v:ℝ)+eps*P.card ≤ (P.card/k:ℝ)*distSample R u v+distOn Pᶜ u v ↔
        (k:ℝ)*((distOn P u v:ℝ)/P.card)+eps*k ≤ (distSample R u v:ℝ) := by
    constructor
    · intro h
      apply (mul_le_mul_iff_of_pos_left ha).mp
      rw [hplus, hd] at *
      linarith
    · intro h
      have hm := mul_le_mul_of_nonneg_left h ha.le
      rw [hplus] at hm
      rw [hd]
      linarith
  simpa only [hl,hr] using mismatch_sum_tails u v P hP k eps heps

 theorem sample_size_exponent_bounds (eps N : ℝ) (heps : 0 < eps) (hN : 1 ≤ N)
    (k : ℕ) (hk : 4/eps^2*Real.log N ≤ k) :
    Real.exp (-2*eps^2*k) ≤ Real.exp (-(1/2)*eps^2*k) ∧
      Real.exp (-2*eps^2*k) ≤ N^(-(2:ℝ)) ∧
      Real.exp (-2*eps^2*k) ≤ N^(-(4/3:ℝ)) := by
  have hs : 0 < eps^2 := sq_pos_of_pos heps
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hl : 0 ≤ Real.log N := Real.log_nonneg hN
  have he : 4*Real.log N ≤ eps^2*(k:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hk hs.le
    field_simp at h
    nlinarith
  have hp : 0 ≤ eps^2*(k:ℝ) := by positivity
  refine ⟨Real.exp_le_exp.mpr (by nlinarith),?_,?_⟩
  · rw [Real.rpow_def_of_pos hn]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [Real.rpow_def_of_pos hn]
    apply Real.exp_le_exp.mpr
    nlinarith

 theorem sampling_bounds_complete (u v : Fin L → A) (P : Finset (Fin L)) (hP : P.Nonempty)
    (k : ℕ) (eps : ℝ) (heps : 0 < eps) (N : ℝ) (hN : 1 ≤ N)
    (hk : 4/eps^2*Real.log N ≤ k) :
    Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
      {R | (P.card/k:ℝ)*distSample R u v+distOn Pᶜ u v ≤ (hammingDist u v:ℝ)-eps*P.card}
        ≤ ENNReal.ofReal (Real.exp (-(1/2)*eps^2*k)) ∧
    Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
      {R | (P.card/k:ℝ)*distSample R u v+distOn Pᶜ u v ≤ (hammingDist u v:ℝ)-eps*P.card}
        ≤ ENNReal.ofReal (N^(-(2:ℝ))) ∧
    Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
      {R | (hammingDist u v:ℝ)+eps*P.card ≤ (P.card/k:ℝ)*distSample R u v+distOn Pᶜ u v}
        ≤ ENNReal.ofReal (N^(-(4/3:ℝ))) := by
  by_cases hk0 : k=0
  · have hN1 : N=1 := by
      have hlog : Real.log N ≤ 0 := by
        have hq : 0 < 4/eps^2 := by positivity
        simp only [hk0,Nat.cast_zero] at hk
        nlinarith
      by_contra hn
      have hl := Real.log_pos (lt_of_le_of_ne hN (Ne.symm hn))
      linarith
    subst k
    subst N
    simp only [Nat.cast_zero,mul_zero,Real.exp_zero,Real.one_rpow,ENNReal.ofReal_one]
    exact ⟨prob_le_one,prob_le_one,prob_le_one⟩
  · have h := scaled_sample_tails u v P hP k (Nat.pos_of_ne_zero hk0) eps heps.le
    have hb := sample_size_exponent_bounds eps N heps hN k hk
    refine ⟨?_,?_,?_⟩
    · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_nonneg _)).mpr
        (h.1.trans hb.1)
    · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.rpow_nonneg (zero_le_one.trans hN) _)).mpr
        (h.1.trans hb.2.1)
    · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.rpow_nonneg (zero_le_one.trans hN) _)).mpr
        (h.2.trans hb.2.2)

end Queelius.ClosestString

open ClosestString.PTAS MeasureTheory

open MeasureTheory

/-- **(11)–(12)** (proof of Fact 2, Li, Ma & Wang, arXiv:cs/0002012v1, p. 11): for strings `u, v`
of length `L`, a nonempty position set `P` with complement `Q`, a multiset `R` of `k` independent
uniform positions of `P`, `ρ = |P|/k`, `ε > 0` and `N ≥ 1` with `k ≥ (4/ε²) ln N`:
`Pr(ρ d^R(u,v) + d^Q(u,v) ≤ d(u,v) − ε|P|) ≤ exp(−ε²k/2)` and `≤ N^{−2}`, and
`Pr(ρ d^R(u,v) + d^Q(u,v) ≥ d(u,v) + ε|P|) ≤ N^{−4/3}`. -/
theorem sampling_solution {A : Type*} [DecidableEq A] {L : ℕ} (u v : Fin L → A) (P : Finset (Fin L))
    (hP : P.Nonempty) (k : ℕ) (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N)
    (hk : 4 / ε ^ 2 * Real.log N ≤ k) :
    Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
        {R | (P.card / k : ℝ) * distSample R u v + distOn Pᶜ u v
              ≤ (hammingDist u v : ℝ) - ε * P.card}
        ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * ε ^ 2 * k)) ∧
      Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
        {R | (P.card / k : ℝ) * distSample R u v + distOn Pᶜ u v
              ≤ (hammingDist u v : ℝ) - ε * P.card}
        ≤ ENNReal.ofReal (N ^ (-(2 : ℝ))) ∧
      Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
        {R | (hammingDist u v : ℝ) + ε * P.card
              ≤ (P.card / k : ℝ) * distSample R u v + distOn Pᶜ u v}
        ≤ ENNReal.ofReal (N ^ (-(4 / 3 : ℝ)))  := Queelius.ClosestString.sampling_bounds_complete u v P hP k ε hε N hN hk

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {A : Type*} [DecidableEq A] {L : ℕ}

theorem samples_mem {L k : ℕ} (P : Finset (Fin L)) (hP : P.Nonempty) :
    ∀ᵐ R ∂Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure),
      ∀ a, R a ∈ P := by
  apply MeasureTheory.ae_all_iff.mpr
  intro a
  apply Measure.tendsto_eval_ae_ae.eventually
  apply ae_iff.mpr
  rw [PMF.toMeasure_uniformOfFinset_apply hP _ (Set.to_countable _).measurableSet]
  simp

theorem score_as_estimate {n m r k : ℕ} [NeZero r]
    (S : Fin n → Fin m → A) (τ : AdmTuple n m L r) (s : Fin L → A)
    (R : Fin k → Fin L) (hR : ∀ a, R a ∈ diffP S τ) (i : Fin n) (p : Start m L) :
    score S τ (fun a => s (R a)) R i p =
      ((diffP S τ).card/k:ℝ)*distSample R (splice (diffP S τ) s (firstStr S τ)) (substr (S i) p)
      + distOn (diffP S τ)ᶜ (splice (diffP S τ) s (firstStr S τ)) (substr (S i) p) := by
  have hs : sampleMismatch R (fun a => s (R a)) (substr (S i) p) =
      distSample R (splice (diffP S τ) s (firstStr S τ)) (substr (S i) p) := by
    unfold sampleMismatch distSample
    congr 1
    apply Finset.filter_congr
    intro a ha
    simp [splice,hR a]
  rw [score,hs,distOn_splice_right]
  simp only [diffP,compl_compl]
  ring

theorem score_empty {n m r k : ℕ} [NeZero r]
    (S : Fin n → Fin m → A) (τ : AdmTuple n m L r) (s : Fin L → A)
    (hP : diffP S τ = ∅) (R : Fin k → Fin L) (i : Fin n) (p : Start m L) :
    score S τ (fun a => s (R a)) R i p =
      (hammingDist (splice (diffP S τ) s (firstStr S τ)) (substr (S i) p):ℝ) := by
  have hQ : agreeQ S τ = Finset.univ := by
    have h := congrArg (fun P : Finset (Fin L) => Pᶜ) hP
    simpa [diffP] using h
  simp [score,hP,hQ,splice,distOn,hammingDist]
end Queelius.ClosestString

end

section
namespace Queelius.ClosestString
open ClosestString.PTAS MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem fact_two {A : Type*} [Fintype A] [DecidableEq A] {n m L r : ℕ} [NeZero n] [NeZero L]
    [NeZero r] (S : Fin n → Fin m → A) (hL : L ≤ m) (τ : AdmTuple n m L r) (s : Fin L → A)
    (t : Fin n → Start m L) (ε : ℝ) (hε : 0 < ε)
    (sel : (Fin (sampleSize n m ε) → Fin L) → Fin n → Start m L)
    (hsel : ∀ R i p, score S τ (fun a => s (R a)) R i (sel R i) ≤ score S τ (fun a => s (R a)) R i p) :
    ENNReal.ofReal (1 - 2 * ((n : ℝ) * m) ^ (-(1 / 3 : ℝ))) ≤
      sampleLaw (diffP S τ) (sampleSize n m ε)
        {R | ∀ i : Fin n,
          (hammingDist (splice (diffP S τ) s (firstStr S τ))
              (substr (S i) (sel R i)) : ℝ)
            ≤ hammingDist (splice (diffP S τ) s (firstStr S τ)) (substr (S i) (t i))
              + 2 * ε * (diffP S τ).card} := by
  classical
  let P := diffP S τ
  let k := sampleSize n m ε
  let u := splice P s (firstStr S τ)
  let N : ℝ := (n:ℝ)*m
  have hn : 1 ≤ n := NeZero.pos n
  have hm : 1 ≤ m := (NeZero.pos L).trans_le hL
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ n*m by nlinarith)
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  by_cases hP : P.Nonempty
  · let μ := Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
    let I := Fin n × Start m L
    let d : I → ℝ := fun j => hammingDist u (substr (S j.1) j.2)
    let X : (Fin k → Fin L) → I → ℝ := fun R j =>
      (P.card/k:ℝ)*distSample R u (substr (S j.1) j.2)+distOn Pᶜ u (substr (S j.1) j.2)
    let e : ℝ := ε*P.card
    let b : ℝ := N^(-(4/3:ℝ))
    have hk : 4/ε^2*Real.log N ≤ (k:ℝ) := Nat.le_ceil _
    have hlo (j : I) : μ.real {R | X R j ≤ d j-e} ≤ b := by
      have h := (sampling_bounds_complete u (substr (S j.1) j.2) P hP k ε hε N hN hk).2.1
      have hb : N^(-(2:ℝ)) ≤ b := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
      have hh := ENNReal.toReal_mono (by finiteness) h
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)] at hh
      exact hh.trans hb
    have hhi (j : I) : μ.real {R | d j+e ≤ X R j} ≤ b := by
      have h := (sampling_bounds_complete u (substr (S j.1) j.2) P hP k ε hε N hN hk).2.2
      have hb : 0 ≤ b := Real.rpow_nonneg hNpos.le _
      have hh := ENNReal.toReal_mono (by finiteness) h
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)] at hh
      exact hh
    have hc : (Fintype.card I:ℝ) ≤ N := by
      have hcard : Fintype.card I ≤ n*m := by
        dsimp [I]
        rw [Fintype.card_prod,Fintype.card_fin]
        exact Nat.mul_le_mul_left _ (by simpa using (Fintype.card_subtype_le (fun p : Fin m => p.val + L ≤ m)))
      dsimp [N]
      exact_mod_cast hcard
    have hp : N*b=N^(-(1/3:ℝ)) := by
      dsimp [b]
      calc
        N*N^(-(4/3:ℝ)) = N^(1:ℝ)*N^(-(4/3:ℝ)) := by rw [Real.rpow_one]
        _ = N^((1:ℝ)-(4/3:ℝ)) := (Real.rpow_add hNpos _ _).symm
        _ = _ := by norm_num
    have hprob := finite_estimate_probability μ X d e b hlo hhi
    have hb : 0 ≤ b := Real.rpow_nonneg hNpos.le _
    have hbound : 1-2*N^(-(1/3:ℝ)) ≤ μ.real {R | ∀ j,d j-e<X R j ∧ X R j<d j+e} := by
      have hc' := mul_le_mul_of_nonneg_right hc hb
      rw [←hp]
      linarith
    have he : sampleLaw P k = μ := by simp [sampleLaw,hP,μ]
    change ENNReal.ofReal (1-2*N^(-(1/3:ℝ))) ≤ sampleLaw P k _
    rw [he]
    apply (ENNReal.ofReal_le_of_le_toReal hbound).trans
    apply measure_mono_ae
    filter_upwards [samples_mem P hP] with R hR
    intro hg i
    have hs := hsel R i (t i)
    rw [score_as_estimate S τ s R hR,score_as_estimate S τ s R hR] at hs
    have h := approximate_minimizer (X R) d e hg (i,sel R i) (i,t i) hs
    simpa only [d,e,mul_assoc] using h
  · have hP0 : diffP S τ=∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    have hg : ∀ R : Fin k → Fin L, ∀ i : Fin n,
        (hammingDist u (substr (S i) (sel R i)):ℝ) ≤
          hammingDist u (substr (S i) (t i))+2*ε*(diffP S τ).card := by
      intro R i
      have h := hsel R i (t i)
      rw [score_empty S τ s hP0,score_empty S τ s hP0] at h
      simpa [u,P,hP0] using h
    have he : {R | ∀ i : Fin n,
        (hammingDist u (substr (S i) (sel R i)):ℝ) ≤
          hammingDist u (substr (S i) (t i))+2*ε*(diffP S τ).card} = Set.univ :=
      Set.eq_univ_of_forall hg
    change ENNReal.ofReal (1-2*N^(-(1/3:ℝ))) ≤ sampleLaw P k _
    rw [he,measure_univ]
    apply ENNReal.ofReal_le_one.mpr
    have h := Real.rpow_nonneg hNpos.le (-(1/3:ℝ))
    linarith
end Queelius.ClosestString

end

section
open ClosestString.PTAS MeasureTheory
open Queelius.ClosestString

/-- **Theorem 9** (Li, Ma & Wang, arXiv:cs/0002012v1, p. 9; proof pp. 9–12): Algorithm
closestSubstring (Figure 3) is a PTAS for Closest Substring. Fix the alphabet `A`, an integer
`r ≥ 2` and `ε > 0`.
(a) For every instance (`n ≥ 1` strings of length `m`, `1 ≤ L ≤ m`) and every solver of problem (8)
within error `ε|P|`, with probability at least `1 − 2(nm)^{−1/3}` over the random multisets, the
output's cost is at most `(1 + 1/(2r−1) + 3εr) d_opt`.
(b) The number of candidates the algorithm evaluates (one solver call per step-1 candidate) is
bounded by a polynomial `c (nm + 1)^c` in the input size, `c` depending only on `|A|`, `r`, `ε`. -/
theorem submission_primary_solution {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (r : ℕ) [NeZero r]
    (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    (∀ (n m L : ℕ) [NeZero n] [NeZero L] (hL : L ≤ m) (S : Fin n → Fin m → A)
        (solver : Solver A n L), IsApproxSolver ε solver →
        ENNReal.ofReal (1 - 2 * ((n : ℝ) * m) ^ (-(1 / 3 : ℝ))) ≤
          algLaw S r ε {ω | (cost S (closestSubstring S hL r ε solver ω) : ℝ)
            ≤ (1 + 1 / (2 * (r : ℝ) - 1) + 3 * ε * r) * dOpt L S}) ∧
    (∃ c : ℕ, ∀ (n m L : ℕ), 1 ≤ n → 1 ≤ L → L ≤ m →
        Fintype.card (Cand A n m L r (sampleSize n m ε)) ≤ c * (n * m + 1) ^ c) := by
  constructor
  · intro n m L instn instL hL S solver hsolver
    obtain ⟨s,t,τ,hs,ht,hevent⟩ := deterministic_reduction S hL ε hε.le solver hsolver (by omega : 1 ≤ r)
    let sel := fun R : Fin (sampleSize n m ε) → Fin L =>
      fun i : Fin n => bestStart S hL τ (fun a => s (R a)) R i
    have hprob := fact_two S hL τ s t ε hε sel
      (fun R i p => bestStart_minimizes S hL τ (fun a => s (R a)) R i p)
    let E : Set (Fin (sampleSize n m ε) → Fin L) := {R | ∀ i : Fin n,
      (hammingDist (splice (diffP S τ) s (firstStr S τ)) (substr (S i) (sel R i)):ℝ) ≤
        hammingDist (splice (diffP S τ) s (firstStr S τ)) (substr (S i) (t i))+
          2*ε*(diffP S τ).card}
    have hm : algLaw S r ε ((Function.eval τ) ⁻¹' E) = sampleLaw (diffP S τ) (sampleSize n m ε) E :=
      (measurePreserving_eval (fun τ => sampleLaw (diffP S τ) (sampleSize n m ε)) τ).measure_preimage
        ((Set.to_countable E).measurableSet.nullMeasurableSet)
    apply hprob.trans
    rw [←hm]
    exact measure_mono (fun ω hω => hevent ω hω)
  · exact polynomial_candidate_guarantee r ε




end

section
namespace Queelius.ClosestString.Controls
open ClosestString.PTAS

theorem uniform_error_factor_sharp (e : ℝ) (he : 0 ≤ e) :
    let d : Fin 2 → ℝ := fun i => if i=0 then e else -e
    let X : Fin 2 → ℝ := fun _ => 0
    (∀ i, |X i-d i| ≤ e) ∧ X 0 ≤ X 1 ∧ d 0=d 1+2*e := by
  dsimp only
  constructor
  · intro i
    fin_cases i <;> simp [abs_of_nonneg he]
  · norm_num
    ring

theorem unit_instance_bound (eps : ℝ) :
    sampleSize 1 1 eps=0 ∧ ENNReal.ofReal (1-2*((1:ℝ)*1)^(-(1/3:ℝ)))=0 := by
  norm_num [sampleSize]
end Queelius.ClosestString.Controls

end

universe audit_u0

theorem solution : (
  ∀ {A : Type audit_u0} [inst : DecidableEq A] {n m : Nat} (u : Fin n → Fin m → A) (c : Fin m → A) (d : Nat),
    (∀ (i : Fin n),
        @LE.le Nat instLENat
          (@hammingDist (Fin m) (fun (i : Fin m) => A) (Fin.fintype m) (fun (i : Fin m) => inst) (u i) c) d) →
      ∀ (r : Nat),
        @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r →
          Or
            (@LE.le Real Real.instLE
              (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                (@Nat.cast Real Real.instNatCast (@ClosestString.PTAS.maxPairDist A n m inst u))
                (@Nat.cast Real Real.instNatCast d))
              (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                (@Nat.cast Real Real.instNatCast d)
                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                    (@OfNat.ofNat Real (nat_lit 2)
                      (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@Nat.cast Real Real.instNatCast r))
                  (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))))
            (@Exists Nat fun (k : Nat) =>
              And (@LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
                (And (@LE.le Nat instLENat k r)
                  (@LE.le Real Real.instLE
                    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                      (@Nat.cast Real Real.instNatCast (@ClosestString.PTAS.minMismatch A n m inst u c k))
                      (@Nat.cast Real Real.instNatCast
                        (@ClosestString.PTAS.minMismatch A n m inst u c
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                      (@Nat.cast Real Real.instNatCast d)
                      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                          (@OfNat.ofNat Real (nat_lit 2)
                            (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (@Nat.cast Real Real.instNatCast r))
                        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))))))
) := @Queelius.ClosestString.claim3
