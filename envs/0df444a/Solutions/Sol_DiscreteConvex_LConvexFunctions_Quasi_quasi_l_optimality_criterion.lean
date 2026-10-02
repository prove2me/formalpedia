-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctions.Quasi.quasi_l_optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T07:06:14.836765+00:00
-- url     : https://prove2.me/submissions/63b9af4f-a36f-49f5-b808-d09908ca674d

import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_SSQSBw
import Definitions.Def_DiscreteConvex_LConvexFunctions_IndicatorVec
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Periodic

set_option autoImplicit false

open DiscreteConvex.LConvexFunctions DiscreteConvex.LConvexFunctions.Quasi
namespace LQuasiWeakCore
variable {V : Type*} [Fintype V] [DecidableEq V]

def positive (q : V → ℤ) : Finset V := Finset.univ.filter (fun v => 0 < q v)
def tail (q : V → ℤ) : V → ℤ := fun v => max (q v-1) 0
def measure (q : V → ℤ) : ℕ := ∑ v, (q v).toNat

lemma positive_nonempty (q : V → ℤ) (hp : ∀ v, 0 ≤ q v) (hne : q ≠ 0) :
    (positive q).Nonempty := by
  by_contra h
  apply hne
  funext v
  have hn : ¬0 < q v := by intro hv; exact h ⟨v,by simp [positive,hv]⟩
  have hv := hp v
  change q v=0
  omega

lemma positive_proper (q : V → ℤ) (hz : ∃ v, q v=0) : positive q ≠ Finset.univ := by
  obtain ⟨v,hv⟩ := hz
  intro he
  have hm : v ∈ positive q := he ▸ Finset.mem_univ v
  simpa [positive,hv] using hm

lemma tail_nonneg (q : V → ℤ) (v : V) : 0 ≤ tail q v := le_max_right _ _
lemma tail_zero (q : V → ℤ) (hz : ∃ v, q v=0) : ∃ v, tail q v=0 := by
  obtain ⟨v,hv⟩ := hz
  exact ⟨v,by simp [tail,hv]⟩

lemma measure_tail_lt (q : V → ℤ) (hp : ∀ v, 0 ≤ q v) (hne : q ≠ 0) :
    measure (tail q) < measure q := by
  obtain ⟨u,hu⟩ := positive_nonempty q hp hne
  have hu' : 0 < q u := by simpa [positive] using hu
  apply Finset.sum_lt_sum
  · intro v _
    have hv := hp v
    dsimp [tail]
    omega
  · refine ⟨u,Finset.mem_univ u,?_⟩
    dsimp [tail]
    omega

lemma tail_zero_indicator (q : V → ℤ) (hp : ∀ v, 0 ≤ q v) (hz : tail q=0) :
    q = IndicatorVec (positive q) := by
  funext v
  have he := congrFun hz v
  have hv := hp v
  dsimp [tail] at he
  by_cases h : 0 < q v <;> simp [IndicatorVec,positive,h] <;> omega

lemma descent_excludes (Bad : (V → ℤ) → Prop) (h0 : ¬Bad 0)
    (hstep : ∀ q, (∀ v, 0 ≤ q v) → (∃ v, q v=0) → Bad q → Bad (tail q)) :
    ∀ q, (∀ v, 0 ≤ q v) → (∃ v, q v=0) → ¬Bad q := by
  suffices h : ∀ n : ℕ, ∀ q, measure q=n →
      (∀ v, 0 ≤ q v) → (∃ v, q v=0) → ¬Bad q by
    intro q hp hz
    exact h _ q rfl hp hz
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q hn hp hz hbad
    have hne : q ≠ 0 := by intro he; exact h0 (he ▸ hbad)
    have hm := measure_tail_lt q hp hne
    exact ih _ (by omega) (tail q) rfl (tail_nonneg q) (tail_zero q hz) (hstep q hp hz hbad)

lemma meet_identity (q : V → ℤ) (hp : ∀ v, 0 ≤ q v) :
    (fun v => q v-1) ⊓ 0 = (fun v => IndicatorVec (positive q) v-1) := by
  funext v
  have hv := hp v
  change min (q v-1) 0 = _
  by_cases h : 0 < q v <;> simp [IndicatorVec,positive,h] <;> omega

lemma weak_step (g : (V → ℤ) → WithTop ℝ) (hg : QSBw g)
    (hshift : ∀ q k, g (fun v => q v+k)=g q) (h0 : g 0 ≠ ⊤)
    (q : V → ℤ) (hq : g q ≠ ⊤) (hp : ∀ v, 0 ≤ q v) :
    min (g (IndicatorVec (positive q))) (g (tail q)) ≤ max (g q) (g 0) := by
  have hq' : g (fun v => q v-1) = g q := hshift q (-1)
  have hmeet : g ((fun v => q v-1) ⊓ 0) = g (IndicatorVec (positive q)) := by
    rw [meet_identity q hp]
    exact hshift _ (-1)
  have hsup : ((fun v => q v-1) ⊔ 0 : V → ℤ) = tail q := by funext v; rfl
  have he := hg (fun v => q v-1) (by simpa [DomZ,hq'] using hq) 0 h0
  simpa only [hq',hmeet,hsup] using he

lemma semistrict_step (g : (V → ℤ) → WithTop ℝ) (hg : SSQSBw g)
    (hshift : ∀ q k, g (fun v => q v+k)=g q) (h0 : g 0 ≠ ⊤)
    (q : V → ℤ) (hq : g q < g 0) (hp : ∀ v, 0 ≤ q v) :
    min (g (IndicatorVec (positive q))) (g (tail q)) < g 0 := by
  have hq' : g (fun v => q v-1) = g q := hshift q (-1)
  have hmeet : g ((fun v => q v-1) ⊓ 0) = g (IndicatorVec (positive q)) := by
    rw [meet_identity q hp]
    exact hshift _ (-1)
  have hsup : ((fun v => q v-1) ⊔ 0 : V → ℤ) = tail q := by funext v; rfl
  have he := hg (fun v => q v-1) (by simpa [DomZ,hq'] using ne_top_of_lt hq) 0 h0
  rcases he with he | he
  · simpa only [hq',hmeet,hsup,max_eq_right hq.le] using he
  · have heq : g q=g 0 := by simpa only [hq'] using he.1
    exact False.elim (hq.ne heq)

theorem strict_normalized (g : (V → ℤ) → WithTop ℝ) (hg : QSBw g)
    (hshift : ∀ q k, g (fun v => q v+k)=g q) (h0 : g 0 ≠ ⊤)
    (hloc : ∀ X : Finset V, X ≠ ∅ → X ≠ Finset.univ → g 0 < g (IndicatorVec X))
    (q : V → ℤ) (hp : ∀ v, 0 ≤ q v) (hz : ∃ v, q v=0) (hq : g q ≤ g 0) : q=0 := by
  by_contra hne
  apply descent_excludes (fun q => g q≤g 0 ∧ q≠0) (by simp) ?_ q hp hz ⟨hq,hne⟩
  intro r hr hz ⟨hval,hrne⟩
  have hl := hloc (positive r) (Finset.nonempty_iff_ne_empty.mp (positive_nonempty r hr hrne))
    (positive_proper r hz)
  have hw := weak_step g hg hshift h0 r (ne_top_of_le_ne_top h0 hval) hr
  rw [max_eq_right hval] at hw
  have ht : g (tail r) ≤ g 0 := (min_le_iff.mp hw).resolve_left (not_le_of_gt hl)
  refine ⟨ht,?_⟩
  intro he
  have hi := tail_zero_indicator r hr he
  exact (not_le_of_gt hl) (hi ▸ hval)

theorem weak_normalized (g : (V → ℤ) → WithTop ℝ) (hg : SSQSBw g)
    (hshift : ∀ q k, g (fun v => q v+k)=g q) (h0 : g 0 ≠ ⊤)
    (hloc : ∀ X : Finset V, g 0 ≤ g (IndicatorVec X))
    (q : V → ℤ) (hp : ∀ v, 0 ≤ q v) (hz : ∃ v, q v=0) : g 0 ≤ g q := by
  apply le_of_not_gt
  apply descent_excludes (fun q => g q<g 0) (by simp) ?_ q hp hz
  intro r hr _ hval
  have hw := semistrict_step g hg hshift h0 r hval hr
  exact (min_lt_iff.mp hw).resolve_left (not_lt_of_ge (hloc _))

end LQuasiWeakCore
#print axioms LQuasiWeakCore.strict_normalized
#print axioms LQuasiWeakCore.weak_normalized

open DiscreteConvex.LConvexFunctions DiscreteConvex.LConvexFunctions.Quasi
namespace LQuasiWeakAssembly
open LQuasiWeakCore
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma shift_of_periodic (g : (V → ℤ) → WithTop ℝ) (hper : ∀ p, g (p+1)=g p) :
    ∀ q k, g (fun v => q v+k)=g q := by
  have hperiod : Function.Periodic g (1 : V → ℤ) := hper
  intro q k
  convert hperiod.zsmul k q using 1
  congr 1
  funext v
  simp

lemma translate_sup (p x y : V → ℤ) : (p+x) ⊔ (p+y) = p+(x ⊔ y) := by
  funext v
  change max (p v+x v) (p v+y v) = p v+max (x v) (y v)
  omega
lemma translate_inf (p x y : V → ℤ) : (p+x) ⊓ (p+y) = p+(x ⊓ y) := by
  funext v
  change min (p v+x v) (p v+y v) = p v+min (x v) (y v)
  omega

lemma translate_weak (g : (V → ℤ) → WithTop ℝ) (hg : QSBw g) (p : V → ℤ) :
    QSBw (fun x => g (p+x)) := by
  intro x hx y hy
  have hh := hg (p+x) hx (p+y) hy
  simpa only [translate_sup,translate_inf] using hh

lemma translate_semistrict (g : (V → ℤ) → WithTop ℝ) (hg : SSQSBw g) (p : V → ℤ) :
    SSQSBw (fun x => g (p+x)) := by
  intro x hx y hy
  have hh := hg (p+x) hx (p+y) hy
  simpa only [translate_sup,translate_inf] using hh

lemma strict_at_zero (g : (V → ℤ) → WithTop ℝ) (hg : QSBw g)
    (hshift : ∀ q k, g (fun v => q v+k)=g q) (h0 : g 0 ≠ ⊤)
    (hloc : ∀ X : Finset V, X ≠ ∅ → X ≠ Finset.univ → g 0 < g (IndicatorVec X)) :
    ∀ q : V → ℤ, (¬∃ k : ℤ, q=fun _ => k) → g 0 < g q := by
  classical
  intro q hnot
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    exact False.elim (hnot ⟨0,Subsingleton.elim _ _⟩)
  | inr h =>
    letI := h
    by_contra hle
    have hq : g q ≤ g 0 := le_of_not_gt hle
    obtain ⟨u,_,hu⟩ := Finset.exists_min_image Finset.univ q Finset.univ_nonempty
    let q' : V → ℤ := fun v => q v-q u
    have hpos (v : V) : 0 ≤ q' v := sub_nonneg.mpr (hu v (Finset.mem_univ v))
    have hzero : ∃ v, q' v=0 := ⟨u,sub_self _⟩
    have hcost : g q'=g q := hshift q (-q u)
    have he := strict_normalized g hg hshift h0 hloc q' hpos hzero (hcost ▸ hq)
    apply hnot
    refine ⟨q u,?_⟩
    funext v
    have hv := congrFun he v
    dsimp [q'] at hv
    omega

lemma weak_at_zero (g : (V → ℤ) → WithTop ℝ) (hg : SSQSBw g)
    (hshift : ∀ q k, g (fun v => q v+k)=g q) (h0 : g 0 ≠ ⊤)
    (hloc : ∀ X : Finset V, g 0 ≤ g (IndicatorVec X)) : ∀ q, g 0 ≤ g q := by
  classical
  intro q
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    have he : q=0 := Subsingleton.elim _ _
    rw [he]
  | inr h =>
    letI := h
    obtain ⟨u,_,hu⟩ := Finset.exists_min_image Finset.univ q Finset.univ_nonempty
    let q' : V → ℤ := fun v => q v-q u
    have hpos (v : V) : 0 ≤ q' v := sub_nonneg.mpr (hu v (Finset.mem_univ v))
    have hzero : ∃ v, q' v=0 := ⟨u,sub_self _⟩
    have hcost : g q'=g q := hshift q (-q u)
    simpa only [hcost] using weak_normalized g hg hshift h0 hloc q' hpos hzero

lemma proper_indicator_not_shift (p : V → ℤ) (X : Finset V) (hX : X ≠ ∅)
    (hXV : X ≠ Finset.univ) : ¬∃ k : ℤ, (fun v => p v+IndicatorVec X v) = fun v => p v+k := by
  classical
  obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr hX
  have hvex : ∃ v : V, v ∉ X := by
    by_contra h
    push_neg at h
    apply hXV
    ext v
    simp [h v]
  obtain ⟨v,hv⟩ := hvex
  rintro ⟨k,hk⟩
  have hu' := congrFun hk u
  have hv' := congrFun hk v
  simp only [IndicatorVec,if_pos hu,if_neg hv] at hu' hv'
  omega

theorem criterion :
    (∀ g : (V → ℤ) → WithTop ℝ, (∀ p : V → ℤ, g (p + 1) = g p) → QSBw g → ∀ p ∈ DomZ g,
      (∀ q : V → ℤ, (¬ ∃ k : ℤ, q = fun v => p v + k) → g p < g q) ↔
        (∀ X : Finset V, X ≠ ∅ → X ≠ Finset.univ →
          g p < g (fun v => p v + IndicatorVec X v))) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, (∀ p : V → ℤ, g (p + 1) = g p) → SSQSBw g → ∀ p ∈ DomZ g,
      (∀ q, g p ≤ g q) ↔ (∀ X : Finset V, g p ≤ g (fun v => p v + IndicatorVec X v))) := by
  constructor
  · intro g hper hg p hp
    constructor
    · intro hmin X hX hXV
      exact hmin _ (proper_indicator_not_shift p X hX hXV)
    · intro hloc q hnot
      let F : (V → ℤ) → WithTop ℝ := fun x => g (p+x)
      have hshift := shift_of_periodic g hper
      have hFshift (x : V → ℤ) (k : ℤ) : F (fun v => x v+k)=F x := by
        have he : p+(fun v => x v+k) = (fun v => (p+x) v+k) := by funext v; simp; omega
        simpa only [F,he] using hshift (p+x) k
      have hF0 : F 0 ≠ ⊤ := by simpa [F,DomZ] using hp
      have hFloc (X : Finset V) (hX : X ≠ ∅) (hXV : X ≠ Finset.univ) :
          F 0 < F (IndicatorVec X) := by
        have he : p+IndicatorVec X = (fun v => p v+IndicatorVec X v) := by funext v; rfl
        simpa only [F,add_zero,he] using hloc X hX hXV
      have hn : ¬∃ k : ℤ, (fun v => q v-p v) = fun _ => k := by
        rintro ⟨k,hk⟩
        apply hnot
        refine ⟨k,?_⟩
        funext v
        have hv := congrFun hk v
        omega
      have hh := strict_at_zero F (translate_weak g hg p) hFshift hF0 hFloc
        (fun v => q v-p v) hn
      have he : p+(fun v => q v-p v)=q := by funext v; simp
      simpa only [F,add_zero,he] using hh
  · intro g hper hg p hp
    constructor
    · intro hmin X
      exact hmin _
    · intro hloc q
      let F : (V → ℤ) → WithTop ℝ := fun x => g (p+x)
      have hshift := shift_of_periodic g hper
      have hFshift (x : V → ℤ) (k : ℤ) : F (fun v => x v+k)=F x := by
        have he : p+(fun v => x v+k) = (fun v => (p+x) v+k) := by funext v; simp; omega
        simpa only [F,he] using hshift (p+x) k
      have hF0 : F 0 ≠ ⊤ := by simpa [F,DomZ] using hp
      have hFloc (X : Finset V) : F 0 ≤ F (IndicatorVec X) := by
        have he : p+IndicatorVec X = (fun v => p v+IndicatorVec X v) := by funext v; rfl
        simpa only [F,add_zero,he] using hloc X
      have hh := weak_at_zero F (translate_semistrict g hg p) hFshift hF0 hFloc
        (fun v => q v-p v)
      have he : p+(fun v => q v-p v)=q := by funext v; simp
      simpa only [F,add_zero,he] using hh

end LQuasiWeakAssembly
#print axioms LQuasiWeakAssembly.criterion

theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ g : (V → ℤ) → WithTop ℝ, (∀ p : V → ℤ, g (p + 1) = g p) → QSBw g → ∀ p ∈ DomZ g,
      (∀ q : V → ℤ, (¬ ∃ k : ℤ, q = fun v => p v + k) → g p < g q) ↔
        (∀ X : Finset V, X ≠ ∅ → X ≠ Finset.univ →
          g p < g (fun v => p v + IndicatorVec X v))) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, (∀ p : V → ℤ, g (p + 1) = g p) → SSQSBw g → ∀ p ∈ DomZ g,
      (∀ q, g p ≤ g q) ↔ (∀ X : Finset V, g p ≤ g (fun v => p v + IndicatorVec X v))) := LQuasiWeakAssembly.criterion (V := V)

#print axioms solution
