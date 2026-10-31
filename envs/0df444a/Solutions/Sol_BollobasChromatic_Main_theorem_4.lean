-- Prove2me | solution 1 for BollobasChromatic.Main.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T06:17:34.565844+00:00
-- url     : https://prove2.me/submissions/f5920874-d637-41d9-94b8-a734d81d9179

import Definitions.Def_BollobasChromatic_Main_Setting

-- BEGIN MODULE BCProof.SharedBasics

-- END MODULE BCProof.SharedBasics

-- BEGIN MODULE BCProof.BernoulliMean
noncomputable section
open Finset
namespace BollobasChromatic.Main.BCFresh
variable {I : Type*} [DecidableEq I]

def bweight (p : I → ℝ) (s t : Finset I) : ℝ :=
  (∏ i ∈ t, p i) * ∏ i ∈ s \ t, (1-p i)
def bmean (p : I → ℝ) (s : Finset I) (f : Finset I → ℝ) : ℝ :=
  ∑ t ∈ s.powerset, bweight p s t * f t

theorem bweight_nonneg (p : I → ℝ) (hp : ∀i, 0≤p i ∧ p i≤1) (s t : Finset I) :
    0 ≤ bweight p s t := by
  apply mul_nonneg
  · exact prod_nonneg fun i _ => (hp i).1
  · exact prod_nonneg fun i _ => sub_nonneg.mpr (hp i).2

theorem bweight_insert_absent (p : I → ℝ) {s t : Finset I} {i : I}
    (hi : i∉s) (ht : t⊆s) : bweight p (insert i s) t = (1-p i)*bweight p s t := by
  have hit : i∉t := fun h => hi (ht h)
  have he : insert i s \ t = insert i (s\t) := by ext j; simp; aesop
  have hn : i ∉ s\t := fun h => hi (mem_sdiff.mp h).1
  simp only [bweight, he, prod_insert hn]
  ring

theorem bweight_insert_present (p : I → ℝ) {s t : Finset I} {i : I}
    (hi : i∉s) (ht : t⊆s) : bweight p (insert i s) (insert i t) = p i*bweight p s t := by
  have hit : i∉t := fun h => hi (ht h)
  have he : insert i s \ insert i t = s\t := by ext j; simp; aesop
  simp only [bweight, he, prod_insert hit]
  ring

@[simp] theorem bmean_empty (p : I → ℝ) (f : Finset I → ℝ) : bmean p ∅ f = f ∅ := by
  simp [bmean,bweight]

theorem bmean_insert (p : I → ℝ) {s : Finset I} {i : I} (hi : i∉s)
    (f : Finset I → ℝ) :
    bmean p (insert i s) f = (1-p i)*bmean p s f + p i*bmean p s (fun t => f (insert i t)) := by
  rw [bmean, sum_powerset_insert hi]
  simp only [bmean, mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro t ht
  · rw [bweight_insert_absent p hi (mem_powerset.mp ht)]; ring
  · rw [bweight_insert_present p hi (mem_powerset.mp ht)]; ring

theorem bmean_const (p : I → ℝ) (s : Finset I) (c : ℝ) : bmean p s (fun _ => c) = c := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih => rw [bmean_insert p hi, ih]; ring

theorem bmean_add (p : I → ℝ) (s : Finset I) (f g : Finset I → ℝ) :
    bmean p s (fun t => f t+g t) = bmean p s f+bmean p s g := by
  simp only [bmean,mul_add,sum_add_distrib]
theorem bmean_sub (p : I → ℝ) (s : Finset I) (f g : Finset I → ℝ) :
    bmean p s (fun t => f t-g t) = bmean p s f-bmean p s g := by
  simp only [bmean,mul_sub,sum_sub_distrib]
theorem bmean_mul (p : I → ℝ) (s : Finset I) (c : ℝ) (f : Finset I → ℝ) :
    bmean p s (fun t => c*f t) = c*bmean p s f := by
  simp only [bmean,mul_sum]
  apply sum_congr rfl
  intro t _
  ring

theorem bmean_mono (p : I → ℝ) (hp : ∀i, 0≤p i ∧ p i≤1) (s : Finset I)
    {f g : Finset I → ℝ} (h : ∀t⊆s, f t≤g t) : bmean p s f ≤ bmean p s g := by
  apply sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_left (h t (mem_powerset.mp ht)) (bweight_nonneg p hp s t)
theorem bmean_nonneg (p : I → ℝ) (hp : ∀i, 0≤p i ∧ p i≤1) (s : Finset I)
    {f : Finset I → ℝ} (h : ∀t⊆s, 0≤f t) : 0≤bmean p s f := by
  simpa only [bmean_const] using bmean_mono p hp s h

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.BernoulliMean

-- BEGIN MODULE BCProof.BiasedHarris
noncomputable section
open Finset
namespace BollobasChromatic.Main.BCFresh
variable {I : Type*} [DecidableEq I]

theorem biased_harris (p : I → ℝ) (hp : ∀i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset I) (f g : Finset I → ℝ) (hf : Monotone f) (hg : Monotone g) :
    bmean p s f*bmean p s g ≤ bmean p s (fun t => f t*g t) := by
  induction s using Finset.induction generalizing f g with
  | empty => simp
  | @insert i s hi ih =>
    have hf1 : Monotone (fun t => f (insert i t)) := fun _ _ h => hf (insert_subset_insert i h)
    have hg1 : Monotone (fun t => g (insert i t)) := fun _ _ h => hg (insert_subset_insert i h)
    have h0 := ih f g hf hg
    have h1 := ih (fun t => f (insert i t)) (fun t => g (insert i t)) hf1 hg1
    have hfm : bmean p s f ≤ bmean p s (fun t => f (insert i t)) :=
      bmean_mono p hp s fun t _ => hf (subset_insert i t)
    have hgm : bmean p s g ≤ bmean p s (fun t => g (insert i t)) :=
      bmean_mono p hp s fun t _ => hg (subset_insert i t)
    rw [bmean_insert p hi, bmean_insert p hi, bmean_insert p hi]
    have hc := mul_nonneg (mul_nonneg (hp i).1 (sub_nonneg.mpr (hp i).2))
      (mul_nonneg (sub_nonneg.mpr hfm) (sub_nonneg.mpr hgm))
    have hb := add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr (hp i).2))
      (mul_le_mul_of_nonneg_left h1 (hp i).1)
    nlinarith only [hc,hb]

theorem biased_harris_anti (p : I → ℝ) (hp : ∀i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset I) (f g : Finset I → ℝ) (hf : Monotone f) (hg : Antitone g) :
    bmean p s (fun t => f t*g t) ≤ bmean p s f*bmean p s g := by
  have hn : Monotone (fun t => -g t) := fun _ _ h => neg_le_neg (hg h)
  have hh := biased_harris p hp s f (fun t => -g t) hf hn
  have hm (h : Finset I → ℝ) : bmean p s (fun t => -h t) = -bmean p s h := by
    simpa only [neg_one_mul] using bmean_mul p s (-1) h
  simp only [mul_neg] at hh
  rw [hm, hm] at hh
  nlinarith only [hh]
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.BiasedHarris

-- BEGIN MODULE BCProof.BernoulliProbability
noncomputable section
open Finset
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {I : Type*} [DecidableEq I]

def bindicator (P : Finset I → Prop) (t : Finset I) : ℝ := if P t then 1 else 0
def bprob (p : I → ℝ) (s : Finset I) (P : Finset I → Prop) : ℝ := bmean p s (bindicator P)

theorem bprob_nonneg (p : I → ℝ) (hp : ∀i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset I) (P : Finset I → Prop) : 0 ≤ bprob p s P := by
  apply bmean_nonneg p hp s
  intro t _
  unfold bindicator
  split_ifs <;> norm_num
@[simp] theorem bprob_true (p : I → ℝ) (s : Finset I) : bprob p s (fun _ => True) = 1 := by
  unfold bprob
  convert bmean_const p s 1 using 1
  congr 1
  funext t
  simp [bindicator]
@[simp] theorem bprob_false (p : I → ℝ) (s : Finset I) : bprob p s (fun _ => False) = 0 := by
  unfold bprob
  convert bmean_const p s 0 using 1
  congr 1
  funext t
  simp [bindicator]

theorem bprob_mono (p : I → ℝ) (hp : ∀i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset I) {P Q : Finset I → Prop} (h : ∀t⊆s, P t → Q t) :
    bprob p s P ≤ bprob p s Q := by
  apply bmean_mono p hp s
  intro t ht
  unfold bindicator
  split_ifs with hP hQ <;> norm_num
  exact hQ (h t ht hP)
theorem bprob_le_one (p : I → ℝ) (hp : ∀i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset I) (P : Finset I → Prop) : bprob p s P ≤ 1 := by
  simpa only [bprob_true] using bprob_mono p hp s (P:=P) (Q:=fun _=>True) (fun _ _ _=>True.intro)

theorem bprob_compl (p : I → ℝ) (s : Finset I) (P : Finset I → Prop) :
    bprob p s (fun t => ¬P t) = 1-bprob p s P := by
  have he : bindicator (fun t => ¬P t) = fun t => 1-bindicator P t := by
    funext t
    simp only [bindicator]
    split_ifs <;> norm_num
  rw [bprob,he,bmean_sub,bmean_const]
  rfl

theorem bprob_inter_compl (p : I → ℝ) (s : Finset I) (P Q : Finset I → Prop) :
    bprob p s (fun t => P t ∧ ¬Q t) = bprob p s P-bprob p s (fun t => P t ∧ Q t) := by
  have he : bindicator (fun t => P t ∧ ¬Q t) =
      fun t => bindicator P t-bindicator (fun t => P t ∧ Q t) t := by
    funext t
    simp only [bindicator]
    by_cases hP : P t <;> by_cases hQ : Q t <;> simp [hP,hQ]
  rw [bprob,he,bmean_sub]
  rfl

theorem bprob_union_le (p : I → ℝ) (hp : ∀i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset I) (P Q : Finset I → Prop) :
    bprob p s (fun t => P t ∨ Q t) ≤ bprob p s P+bprob p s Q := by
  rw [bprob,bprob,bprob,←bmean_add]
  apply bmean_mono p hp s
  intro t _
  simp only [bindicator]
  by_cases hP : P t <;> by_cases hQ : Q t <;> simp [hP,hQ]

theorem bprob_anticorrelation (p : I → ℝ) (hp : ∀i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset I) (P Q : Finset I → Prop)
    (hP : ∀u v, u⊆v → P u → P v) (hQ : ∀u v, u⊆v → Q v → Q u) :
    bprob p s (fun t => P t ∧ Q t) ≤ bprob p s P*bprob p s Q := by
  have hpm : Monotone (bindicator P) := by
    intro u v huv
    unfold bindicator
    split_ifs with hu hv <;> norm_num
    exact hv (hP u v huv hu)
  have hqm : Antitone (bindicator Q) := by
    intro u v huv
    unfold bindicator
    split_ifs with hv hu <;> norm_num
    exact hu (hQ u v huv hv)
  have he : bindicator (fun t => P t ∧ Q t) = fun t => bindicator P t*bindicator Q t := by
    funext t
    simp only [bindicator]
    by_cases hP : P t <;> by_cases hQ : Q t <;> simp [hP,hQ]
  unfold bprob
  rw [he]
  exact biased_harris_anti p hp s (bindicator P) (bindicator Q) hpm hqm
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.BernoulliProbability

-- BEGIN MODULE BCProof.CylinderIndependence
noncomputable section
open Finset
namespace BollobasChromatic.Main.BCFresh
variable {I : Type*} [DecidableEq I]

def DependsOn (f : Finset I → ℝ) (A : Finset I) : Prop :=
  ∀u v, u∩A=v∩A → f u=f v

theorem DependsOn.insert_arg {f : Finset I → ℝ} {A : Finset I} (hf : DependsOn f A) (i : I) :
    DependsOn (fun t => f (insert i t)) A := by
  intro u v huv
  apply hf
  ext j
  have hj := Finset.ext_iff.mp huv j
  simp only [mem_inter,mem_insert] at hj ⊢
  tauto

theorem DependsOn.insert_irrel {f : Finset I → ℝ} {A : Finset I}
    (hf : DependsOn f A) {i : I} (hi : i∉A) : (fun t => f (insert i t)) = f := by
  funext t
  apply hf
  ext j
  simp only [mem_inter,mem_insert]
  constructor
  · rintro ⟨h,hA⟩
    rcases h with rfl | h
    · exact False.elim (hi hA)
    · exact ⟨h,hA⟩
  · rintro ⟨h,hA⟩
    exact ⟨Or.inr h,hA⟩

theorem bmean_independent (p : I → ℝ) (s : Finset I) (f g : Finset I → ℝ)
    (A B : Finset I) (hAB : Disjoint A B) (hf : DependsOn f A) (hg : DependsOn g B) :
    bmean p s (fun t => f t*g t) = bmean p s f*bmean p s g := by
  induction s using Finset.induction generalizing f g with
  | empty => simp
  | @insert i s hi ih =>
    have h0 := ih f g hf hg
    have h1 := ih (fun t => f (insert i t)) (fun t => g (insert i t)) (hf.insert_arg i) (hg.insert_arg i)
    rw [bmean_insert p hi,bmean_insert p hi,bmean_insert p hi,h0,h1]
    by_cases hiA : i∈A
    · have hiB : i∉B := fun h => Finset.disjoint_left.mp hAB hiA h
      rw [hg.insert_irrel hiB]
      ring
    · rw [hf.insert_irrel hiA]
      ring

theorem support_indicator_depends (A : Finset I) : DependsOn (bindicator (fun t => A⊆t)) A := by
  intro u v huv
  have hiff : A⊆u ↔ A⊆v := by
    constructor <;> intro h i hi
    · have : i∈u∩A := mem_inter.mpr ⟨h hi,hi⟩
      rw [huv] at this
      exact (mem_inter.mp this).1
    · have : i∈v∩A := mem_inter.mpr ⟨h hi,hi⟩
      rw [←huv] at this
      exact (mem_inter.mp this).1
  simp only [bindicator,hiff]
  split_ifs <;> rfl

theorem bprob_independent (p : I → ℝ) (s : Finset I) (P Q : Finset I → Prop)
    (A B : Finset I) (hAB : Disjoint A B)
    (hP : DependsOn (bindicator P) A) (hQ : DependsOn (bindicator Q) B) :
    bprob p s (fun t => P t ∧ Q t) = bprob p s P*bprob p s Q := by
  have he : bindicator (fun t => P t ∧ Q t) = fun t => bindicator P t*bindicator Q t := by
    funext t
    simp only [bindicator]
    by_cases hP : P t <;> by_cases hQ : Q t <;> simp [hP,hQ]
  unfold bprob
  rw [he]
  exact bmean_independent p s _ _ A B hAB hP hQ
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.CylinderIndependence

-- BEGIN MODULE BCProof.CylinderProbability
noncomputable section
open Finset
namespace BollobasChromatic.Main.BCFresh
variable {I : Type*} [DecidableEq I]

theorem bmean_congr (p : I → ℝ) (s : Finset I) {f g : Finset I → ℝ}
    (h : ∀t⊆s, f t=g t) : bmean p s f=bmean p s g := by
  apply sum_congr rfl
  intro t ht
  rw [h t (mem_powerset.mp ht)]

theorem bprob_support (p : I → ℝ) (s A : Finset I) (hA : A⊆s) :
    bprob p s (fun t => A⊆t) = ∏i∈A,p i := by
  induction s using Finset.induction generalizing A with
  | empty => have he : A=∅ := subset_empty.mp hA; subst A; simp [bprob,bindicator]
  | @insert i s hi ih =>
    unfold bprob
    rw [bmean_insert p hi]
    by_cases hiA : i∈A
    · have hAs : A.erase i⊆s := by
        intro j hj
        have hjs := hA (mem_of_mem_erase hj)
        rcases mem_insert.mp hjs with hji | hj
        · exact False.elim ((mem_erase.mp hj).1 hji)
        · exact hj
      have hzero : bmean p s (bindicator (fun t => A⊆t)) = 0 := by
        calc
          _ = bmean p s (fun _ => 0) := bmean_congr p s fun t ht => by
            have hn : ¬ A⊆t := fun h => hi (ht (h hiA))
            simp [bindicator,hn]
          _ = 0 := bmean_const p s 0
      have hone : bmean p s (fun t => bindicator (fun u => A⊆u) (insert i t)) =
          bprob p s (fun t => A.erase i⊆t) := by
        apply bmean_congr
        intro t _
        have he : A⊆insert i t ↔ A.erase i⊆t := by
          constructor
          · intro h j hj
            exact (mem_insert.mp (h (mem_of_mem_erase hj))).resolve_left (mem_erase.mp hj).1
          · intro h j hj
            by_cases hji : j=i
            · exact mem_insert.mpr (Or.inl hji)
            · exact mem_insert.mpr (Or.inr (h (mem_erase.mpr ⟨hji,hj⟩)))
        simp only [bindicator,he]
        split_ifs <;> rfl
      rw [hzero,hone,ih _ hAs,←Finset.mul_prod_erase _ _ hiA]
      ring
    · have hAs : A⊆s := by
        intro j hj
        exact (mem_insert.mp (hA hj)).resolve_left (fun h => hiA (h ▸ hj))
      have hone : bmean p s (fun t => bindicator (fun u => A⊆u) (insert i t)) =
          bprob p s (fun t => A⊆t) := by
        rw [(support_indicator_depends A).insert_irrel hiA]
        rfl
      rw [hone]
      change (1-p i)*bprob p s (fun t => A⊆t)+p i*bprob p s (fun t => A⊆t)=_
      rw [ih _ hAs]
      ring

theorem no_supports_depends {J : Type*} (F : J → Finset I) (L : Finset J) :
    DependsOn (bindicator (fun t => ∀j∈L, ¬F j⊆t)) (L.biUnion F) := by
  classical
  intro u v huv
  have he (j : J) (hj : j∈L) : F j⊆u ↔ F j⊆v := by
    have hsub : F j⊆L.biUnion F := subset_biUnion_of_mem F hj
    constructor <;> intro h i hi
    · have hh : i∈u∩L.biUnion F := mem_inter.mpr ⟨h hi,hsub hi⟩
      rw [huv] at hh
      exact (mem_inter.mp hh).1
    · have hh : i∈v∩L.biUnion F := mem_inter.mpr ⟨h hi,hsub hi⟩
      rw [←huv] at hh
      exact (mem_inter.mp hh).1
  have hh : (∀j∈L, ¬F j⊆u) ↔ (∀j∈L, ¬F j⊆v) := by
    constructor <;> intro h j hj <;> simpa only [he j hj] using h j hj
  simp only [bindicator,hh]
  split_ifs <;> rfl
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.CylinderProbability

-- BEGIN MODULE BCProof.ProbabilitySums
noncomputable section
open Finset
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {I J : Type*} [DecidableEq I]

theorem bmean_sum (p : I → ℝ) (s : Finset I) (L : Finset J) (f : J → Finset I → ℝ) :
    bmean p s (fun t => ∑j∈L,f j t) = ∑j∈L,bmean p s (f j) := by
  simp only [bmean,mul_sum]
  exact Finset.sum_comm

theorem bprob_congr (p : I → ℝ) (s : Finset I) {P Q : Finset I → Prop}
    (h : ∀t⊆s, P t↔Q t) : bprob p s P=bprob p s Q := by
  apply bmean_congr
  intro t ht
  simp only [bindicator,h t ht]

theorem bprob_cover_le (p : I → ℝ) (hp : ∀i, 0≤p i ∧ p i≤1) (s : Finset I)
    (P : Finset I → Prop) (L : Finset J) (Q : J → Finset I → Prop)
    (h : ∀t⊆s,P t→∃j∈L,Q j t) : bprob p s P ≤ ∑j∈L,bprob p s (Q j) := by
  unfold bprob
  rw [←bmean_sum]
  apply bmean_mono p hp s
  intro t ht
  by_cases hP : P t
  · obtain ⟨j,hj,hQ⟩ := h t ht hP
    have hn (i : J) : 0≤bindicator (Q i) t := by unfold bindicator; split_ifs <;> norm_num
    have hh := Finset.single_le_sum (fun i _ => hn i) hj
    simpa [bindicator,hP,hQ] using hh
  · simp only [bindicator,if_neg hP]
    exact sum_nonneg fun i _ => by split_ifs <;> norm_num

theorem bprob_cover_add_le (p : I → ℝ) (hp : ∀i, 0≤p i ∧ p i≤1) (s : Finset I)
    (P Q : Finset I → Prop) (L : Finset J) (R : J → Finset I → Prop)
    (h : ∀t⊆s,P t→Q t∨∃j∈L,R j t) :
    bprob p s P ≤ bprob p s Q+∑j∈L,bprob p s (R j) := by
  calc
    _ ≤ bprob p s (fun t => Q t∨∃j∈L,R j t) := bprob_mono p hp s h
    _ ≤ bprob p s Q+bprob p s (fun t => ∃j∈L,R j t) := bprob_union_le p hp s _ _
    _ ≤ _ := add_le_add le_rfl (bprob_cover_le p hp s _ L R (fun _ _ h=>h))
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.ProbabilitySums

-- BEGIN MODULE BCProof.GraphLaw
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BollobasChromatic.Main.BCFresh

def edgeGround (n : ℕ) : Finset (Sym2 (Fin n)) := (⊤ : SimpleGraph (Fin n)).edgeFinset
def graphOf {n : ℕ} (t : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (t : Set (Sym2 (Fin n)))

theorem graphOf_edges {n : ℕ} (t : Finset (Sym2 (Fin n))) (ht : t⊆edgeGround n) :
    (graphOf t).edgeFinset=t := by
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset]
  change (SimpleGraph.fromEdgeSet (t : Set (Sym2 (Fin n)))).edgeSet = (t : Set (Sym2 (Fin n)))
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  exact ⟨fun h => h.1, fun h => ⟨h,(⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeFinset (ht h)⟩⟩

@[simp] theorem graphOf_edgeFinset {n : ℕ} (G : SimpleGraph (Fin n)) : graphOf G.edgeFinset=G := by
  simp [graphOf]

theorem edgeGround_card (n : ℕ) : (edgeGround n).card=n.choose 2 := by
  simpa [edgeGround] using (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))

theorem graph_weight (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) :
    gnpWeight n p G=bweight (fun _ => p) (edgeGround n) G.edgeFinset := by
  have hs : G.edgeFinset⊆edgeGround n := SimpleGraph.edgeFinset_mono le_top
  simp only [gnpWeight,bweight,prod_const,card_sdiff_of_subset hs,edgeGround_card]

theorem gnpExp_bmean (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    gnpExp n p f=bmean (fun _ => p) (edgeGround n) (fun t => f (graphOf t)) := by
  unfold gnpExp bmean
  apply Finset.sum_bij (fun G _ => G.edgeFinset)
  · intro G _
    exact mem_powerset.mpr (SimpleGraph.edgeFinset_mono le_top)
  · intro G _ H _ h
    exact SimpleGraph.edgeFinset_inj.mp h
  · intro t ht
    exact ⟨graphOf t,mem_univ _,graphOf_edges t (mem_powerset.mp ht)⟩
  · intro G _
    change gnpWeight n p G*f G=bweight (fun _ => p) (edgeGround n) G.edgeFinset*f (graphOf G.edgeFinset)
    rw [graphOf_edgeFinset,graph_weight]

theorem gnpProb_bprob (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p P=bprob (fun _ => p) (edgeGround n) (fun t => P (graphOf t)) := by
  have he : gnpProb n p P=gnpExp n p (fun G => if P G then 1 else 0) := by
    unfold gnpProb gnpExp
    apply sum_congr rfl
    intro G _
    change (if P G then gnpWeight n p G else 0)=gnpWeight n p G*(if P G then 1 else 0)
    by_cases h : P G <;> simp [h]
  rw [he,gnpExp_bmean]
  rfl

theorem gnpProb_nonneg (n : ℕ) (p : ℝ) (hp : 0≤p ∧ p≤1) (P : SimpleGraph (Fin n) → Prop) :
    0≤gnpProb n p P := by
  rw [gnpProb_bprob]
  exact bprob_nonneg _ (fun _ => hp) _ _

theorem gnpProb_le_one (n : ℕ) (p : ℝ) (hp : 0≤p ∧ p≤1) (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p P≤1 := by
  rw [gnpProb_bprob]
  exact bprob_le_one _ (fun _ => hp) _ _

theorem gnpProb_compl (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => ¬P G)=1-gnpProb n p P := by
  simp only [gnpProb_bprob,bprob_compl]
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.GraphLaw

-- BEGIN MODULE BCProof.CliqueSupports
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {V : Type*} [DecidableEq V]

def cliqueEdges (C : Finset V) : Finset (Sym2 V) := C.sym2.filter (fun e => ¬e.IsDiag)

@[simp] theorem mk_mem_cliqueEdges (C : Finset V) (i j : V) :
    s(i,j) ∈ cliqueEdges C ↔ i∈C ∧ j∈C ∧ i≠j := by
  simp [cliqueEdges,and_assoc]

theorem cliqueEdges_inter (C D : Finset V) : cliqueEdges (C∩D)=cliqueEdges C∩cliqueEdges D := by
  ext e
  induction e using Sym2.ind with
  | _ i j => simp only [mk_mem_cliqueEdges,mem_inter]; tauto

theorem cliqueEdges_mono {C D : Finset V} (h : C⊆D) : cliqueEdges C⊆cliqueEdges D := by
  intro e he
  induction e using Sym2.ind with
  | _ i j =>
    obtain ⟨hi,hj,hij⟩ := (mk_mem_cliqueEdges C i j).mp he
    exact (mk_mem_cliqueEdges D i j).mpr ⟨h hi,h hj,hij⟩

theorem cliqueEdges_card (C : Finset V) : (cliqueEdges C).card=C.card.choose 2 := by
  have hd : C.sym2.filter Sym2.IsDiag = C.image Sym2.diag := by
    ext e
    constructor
    · intro he
      obtain ⟨hc,hd⟩ := mem_filter.mp he
      refine mem_image.mpr ⟨e.diagElem hd, ?_, Sym2.diag_diagElem hd⟩
      have hc' : Sym2.diag (e.diagElem hd) ∈ C.sym2 := (Sym2.diag_diagElem hd).symm ▸ hc
      exact Finset.diag_mem_sym2_iff.mp hc'
    · rintro he
      obtain ⟨i,hi,rfl⟩ := mem_image.mp he
      simp [hi]
  have hc := Finset.card_filter_add_card_filter_not (s := C.sym2) Sym2.IsDiag
  rw [hd,card_image_of_injective _ Sym2.diag_injective,Finset.card_sym2] at hc
  have hn := Nat.choose_succ_succ C.card 1
  norm_num only [Nat.choose_one_right,Nat.succ_eq_add_one] at hn
  change (C.sym2.filter (fun e => ¬e.IsDiag)).card= C.card.choose 2
  omega

theorem clique_iff_edges {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) :
    G.IsClique (C : Set (Fin n)) ↔ cliqueEdges C⊆G.edgeFinset := by
  constructor
  · intro h e he
    induction e using Sym2.ind with
    | _ i j =>
      obtain ⟨hi,hj,hij⟩ := (mk_mem_cliqueEdges C i j).mp he
      simpa using h hi hj hij
  · intro h i hi j hj hij
    have he := h ((mk_mem_cliqueEdges C i j).mpr ⟨hi,hj,hij⟩)
    simpa using he

theorem cliqueEdges_ground {n : ℕ} (C : Finset (Fin n)) : cliqueEdges C⊆edgeGround n := by
  intro e he
  induction e using Sym2.ind with
  | _ i j =>
    have hij := ((mk_mem_cliqueEdges C i j).mp he).2.2
    simpa [edgeGround] using hij

theorem clique_probability (n : ℕ) (q : ℝ) (C : Finset (Fin n)) :
    gnpProb n q (fun G => G.IsClique (C : Set (Fin n)))=q^(C.card.choose 2) := by
  rw [gnpProb_bprob]
  calc
    _ = bprob (fun _ => q) (edgeGround n) (fun t => cliqueEdges C⊆t) := by
      apply bprob_congr
      intro t ht
      rw [clique_iff_edges,graphOf_edges t ht]
    _ = _ := by rw [bprob_support _ _ _ (cliqueEdges_ground C)]; simp [cliqueEdges_card]
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.CliqueSupports

-- BEGIN MODULE BCProof.BernoulliUnion
noncomputable section
open Finset
namespace BollobasChromatic.Main.BCFresh
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

theorem bmean_union (p : I → ℝ) (s t : Finset I) (hst : Disjoint s t)
    (f : Finset I → ℝ) :
    bmean p (s∪t) f = bmean p s (fun u => bmean p t (fun v => f (u∪v))) := by
  induction s using Finset.induction generalizing f with
  | empty => simp only [empty_union,bmean_empty]
  | @insert i s hi ih =>
    have hit : i∉t := fun h => Finset.disjoint_left.mp hst (mem_insert_self _ _) h
    have hst' : Disjoint s t := hst.mono_left (subset_insert _ _)
    have hiu : i∉s∪t := by simp [hi,hit]
    rw [insert_union,bmean_insert p hiu,bmean_insert p hi]
    rw [ih hst',ih hst']
    congr 1
    congr 1
    apply congrArg (bmean p s)
    funext u
    apply congrArg (bmean p t)
    funext v
    rw [insert_union]

theorem bmean_map (p : J → ℝ) (e : I ↪ J) (s : Finset I) (f : Finset J → ℝ) :
    bmean p (s.map e) f = bmean (fun i => p (e i)) s (fun t => f (t.map e)) := by
  induction s using Finset.induction generalizing f with
  | empty => simp
  | @insert i s hi ih =>
    have hn : e i∉s.map e := by simpa using hi
    rw [map_insert,bmean_insert p hn,bmean_insert _ hi,ih,ih]
    congr 1
    congr 1
    apply congrArg (bmean (fun i => p (e i)) s)
    funext t
    rw [map_insert]

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.BernoulliUnion

-- BEGIN MODULE BCProof.BernoulliSum
noncomputable section
open Finset
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

def sumGround (s : Finset I) (t : Finset J) : Finset (I ⊕ J) :=
  s.map Function.Embedding.inl ∪ t.map Function.Embedding.inr

omit [DecidableEq I] [DecidableEq J] in
theorem sumGround_disjoint (s : Finset I) (t : Finset J) :
    Disjoint (s.map (Function.Embedding.inl : I ↪ I ⊕ J))
      (t.map Function.Embedding.inr) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,_,rfl⟩ := mem_map.mp hx
  obtain ⟨j,_,h⟩ := mem_map.mp hy
  cases h

theorem bmean_sumGround (p : I → ℝ) (q : J → ℝ) (s : Finset I) (t : Finset J)
    (f : Finset (I ⊕ J) → ℝ) :
    bmean (Sum.elim p q) (sumGround s t) f =
      bmean p s (fun u => bmean q t (fun v =>
        f (u.map Function.Embedding.inl ∪ v.map Function.Embedding.inr))) := by
  rw [sumGround,bmean_union _ _ _ (sumGround_disjoint s t),bmean_map]
  apply congrArg (bmean p s)
  funext u
  exact bmean_map (Sum.elim p q) Function.Embedding.inr t _

theorem map_inl_subset_sum (A u : Finset I) (v : Finset J) :
    A.map Function.Embedding.inl ⊆
      u.map Function.Embedding.inl ∪ v.map Function.Embedding.inr ↔ A⊆u := by
  constructor
  · intro h i hi
    have hh := h (mem_map.mpr ⟨i,hi,rfl⟩)
    simpa using hh
  · intro h x hx
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
    exact mem_union_left _ (mem_map.mpr ⟨i,h hi,rfl⟩)

theorem bprob_sumGround_left (p : I → ℝ) (q : J → ℝ) (s : Finset I) (t : Finset J)
    (F : Finset I → Prop) :
    bprob (Sum.elim p q) (sumGround s t)
      (fun w => F (w.preimage Function.Embedding.inl Function.Embedding.inl.injective.injOn)) =
      bprob p s F := by
  unfold bprob
  rw [bmean_sumGround]
  apply congrArg (bmean p s)
  funext u
  have he (v : Finset J) :
      (u.map Function.Embedding.inl ∪ v.map Function.Embedding.inr).preimage
        Function.Embedding.inl Function.Embedding.inl.injective.injOn = u := by
    ext i
    rw [Finset.mem_preimage]
    simp
  calc
    _ = bmean q t (fun _ => bindicator F u) := by
      apply congrArg (bmean q t)
      funext v
      change (if F ((u.map Function.Embedding.inl ∪ v.map Function.Embedding.inr).preimage Function.Embedding.inl Function.Embedding.inl.injective.injOn) then (1:ℝ) else 0) = _
      rw [he v]
      rfl
    _ = _ := bmean_const q t _
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.BernoulliSum

-- BEGIN MODULE BCProof.JansonStep
noncomputable section
open Finset
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

omit [DecidableEq J] in
theorem janson_step (p : I → ℝ) (hp : ∀i, 0≤p i ∧ p i≤1) (s : Finset I)
    (F : J → Finset I) (L : Finset J) (A : Finset I) :
    bprob p s (fun t => (∀j∈L, ¬F j⊆t) ∧ ¬A⊆t) ≤
      bprob p s (fun t => ∀j∈L, ¬F j⊆t) *
      Real.exp (-bprob p s (fun t => A⊆t) +
        ∑j∈L.filter (fun j => ¬Disjoint A (F j)),bprob p s (fun t => A⊆t ∧ F j⊆t)) := by
  let K := L.filter (fun j => Disjoint A (F j))
  let N := L.filter (fun j => ¬Disjoint A (F j))
  let D : Finset I → Prop := fun t => ∀j∈L, ¬F j⊆t
  let C : Finset I → Prop := fun t => ∀j∈K, ¬F j⊆t
  let P : Finset I → Prop := fun t => A⊆t
  let b := ∑j∈N,bprob p s (fun t => P t ∧ F j⊆t)
  have hd (t : Finset I) : D t → C t := fun h j hj => h j (mem_filter.mp hj).1
  have hDC : bprob p s D ≤ bprob p s C := bprob_mono p hp s (fun t _ => hd t)
  have hCD : Disjoint A (K.biUnion F) := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiK
    obtain ⟨j,hj,hij⟩ := mem_biUnion.mp hiK
    exact Finset.disjoint_left.mp (mem_filter.mp hj).2 hiA hij
  have hPC : bprob p s (fun t => P t ∧ C t) = bprob p s P*bprob p s C :=
    bprob_independent p s P C A (K.biUnion F) hCD (support_indicator_depends A)
      (no_supports_depends F K)
  have hcover : bprob p s (fun t => P t ∧ C t) ≤
      bprob p s (fun t => P t ∧ D t)+
        ∑j∈N,bprob p s (fun t => (P t ∧ F j⊆t) ∧ C t) := by
    apply bprob_cover_add_le p hp s
    intro t _ ht
    by_cases hD : D t
    · exact Or.inl ⟨ht.1,hD⟩
    · right
      change ¬ (∀j∈L, ¬F j⊆t) at hD
      push Not at hD
      obtain ⟨j,hj,hjt⟩ := hD
      have hnot : ¬Disjoint A (F j) := fun hh => ht.2 j (mem_filter.mpr ⟨hj,hh⟩) hjt
      exact ⟨j,mem_filter.mpr ⟨hj,hnot⟩,⟨ht.1,hjt⟩,ht.2⟩
  have hsumb : (∑j∈N,bprob p s (fun t => (P t ∧ F j⊆t) ∧ C t)) ≤ bprob p s C*b := by
    calc
      _ ≤ ∑j∈N,bprob p s (fun t => P t ∧ F j⊆t)*bprob p s C := by
        apply sum_le_sum
        intro j _
        apply bprob_anticorrelation p hp s
        · intro u v huv h
          exact ⟨h.1.trans huv,h.2.trans huv⟩
        · intro u v huv h k hk hku
          exact h k hk (hku.trans huv)
      _ = _ := by unfold b; rw [←sum_mul,mul_comm]
  have hbase : bprob p s C*(bprob p s P-b) ≤ bprob p s (fun t => P t ∧ D t) := by
    rw [hPC] at hcover
    nlinarith only [hcover,hsumb]
  have hlow : bprob p s D*(bprob p s P-b) ≤ bprob p s (fun t => P t ∧ D t) := by
    by_cases hn : 0≤bprob p s P-b
    · exact (mul_le_mul_of_nonneg_right hDC hn).trans hbase
    · exact (mul_nonpos_of_nonneg_of_nonpos (bprob_nonneg p hp s D) (le_of_not_ge hn)).trans
        (bprob_nonneg p hp s _)
  have hcomp : bprob p s (fun t => D t ∧ ¬P t) = bprob p s D-bprob p s (fun t => P t ∧ D t) := by
    rw [bprob_inter_compl]
    congr 1
    exact bprob_congr p s fun _ _ => and_comm
  change bprob p s (fun t => D t ∧ ¬P t) ≤ bprob p s D*Real.exp (-bprob p s P+b)
  rw [hcomp]
  have hex := Real.add_one_le_exp (-bprob p s P+b)
  have hm := mul_le_mul_of_nonneg_left hex (bprob_nonneg p hp s D)
  nlinarith only [hlow,hm]
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.JansonStep

-- BEGIN MODULE BCProof.JansonPlain
noncomputable section
open Finset
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

def eventMean (p : I → ℝ) (s : Finset I) (F : J → Finset I) (L : Finset J) : ℝ :=
  ∑j∈L,bprob p s (fun t => F j⊆t)
def overlapPair (p : I → ℝ) (s : Finset I) (F : J → Finset I) (i j : J) : ℝ :=
  if i≠j ∧ ¬Disjoint (F i) (F j) then bprob p s (fun t => F i⊆t ∧ F j⊆t) else 0
def orderedOverlap (p : I → ℝ) (s : Finset I) (F : J → Finset I) (L : Finset J) : ℝ :=
  ∑i∈L,∑j∈L,overlapPair p s F i j

@[simp] theorem overlapPair_self (p : I → ℝ) (s : Finset I) (F : J → Finset I) (i : J) :
    overlapPair p s F i i=0 := by simp [overlapPair]
theorem overlapPair_symm (p : I → ℝ) (s : Finset I) (F : J → Finset I) (i j : J) :
    overlapPair p s F i j=overlapPair p s F j i := by
  have he : bprob p s (fun t => F i⊆t ∧ F j⊆t)=bprob p s (fun t => F j⊆t ∧ F i⊆t) :=
    bprob_congr p s fun _ _ => and_comm
  simp only [overlapPair,he,ne_comm,disjoint_comm]

theorem orderedOverlap_insert (p : I → ℝ) (s : Finset I) (F : J → Finset I)
    {L : Finset J} {i : J} (hi : i∉L) :
    orderedOverlap p s F (insert i L) = orderedOverlap p s F L+
      2*(∑j∈L.filter (fun j => ¬Disjoint (F i) (F j)),bprob p s (fun t => F i⊆t ∧ F j⊆t)) := by
  have he : (∑j∈L,overlapPair p s F i j) =
      ∑j∈L.filter (fun j => ¬Disjoint (F i) (F j)),bprob p s (fun t => F i⊆t ∧ F j⊆t) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro j hj
    have hij : i≠j := fun h => hi (h ▸ hj)
    simp [overlapPair,hij]
  have he' : (∑j∈L,overlapPair p s F j i) = ∑j∈L,overlapPair p s F i j :=
    sum_congr rfl fun j _ => overlapPair_symm p s F j i
  simp only [orderedOverlap,sum_insert hi,overlapPair_self,zero_add,sum_add_distrib]
  rw [he',he]
  ring

theorem orderedOverlap_nonneg (p : I → ℝ) (hp : ∀i, 0≤p i ∧ p i≤1)
    (s : Finset I) (F : J → Finset I) (L : Finset J) : 0≤orderedOverlap p s F L := by
  apply sum_nonneg
  intro i _
  apply sum_nonneg
  intro j _
  unfold overlapPair
  split_ifs
  · exact bprob_nonneg p hp s _
  · exact le_rfl

theorem janson_plain (p : I → ℝ) (hp : ∀i, 0≤p i ∧ p i≤1)
    (s : Finset I) (F : J → Finset I) (L : Finset J) :
    bprob p s (fun t => ∀j∈L, ¬F j⊆t) ≤
      Real.exp (-eventMean p s F L+orderedOverlap p s F L/2) := by
  induction L using Finset.induction with
  | empty => simp [eventMean,orderedOverlap]
  | @insert i L hi ih =>
    have he : bprob p s (fun t => ∀j∈insert i L, ¬F j⊆t) =
        bprob p s (fun t => (∀j∈L, ¬F j⊆t) ∧ ¬F i⊆t) := by
      apply bprob_congr
      intro t _
      simp only [forall_mem_insert,and_comm]
    rw [he]
    refine (janson_step p hp s F L (F i)).trans ?_
    refine (mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add,orderedOverlap_insert p s F hi]
    simp only [eventMean,sum_insert hi]
    congr 1
    ring
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.JansonPlain

-- BEGIN MODULE BCProof.SelectedSupports
noncomputable section
open Finset
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

def selectedSupport (F : J → Finset I) (j : J) : Finset (I ⊕ J) :=
  insert (Sum.inr j) ((F j).map Function.Embedding.inl)

theorem selectedSupport_subset (s : Finset I) (L : Finset J) (F : J → Finset I)
    (hF : ∀j∈L,F j⊆s) {j : J} (hj : j∈L) : selectedSupport F j⊆sumGround s L := by
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact mem_union_right _ (mem_map.mpr ⟨j,hj,rfl⟩)
  · obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
    exact mem_union_left _ (mem_map.mpr ⟨i,hF j hj hi,rfl⟩)

theorem selectedSupport_disjoint (F : J → Finset I) {i j : J} (hij : i≠j) :
    Disjoint (selectedSupport F i) (selectedSupport F j) ↔ Disjoint (F i) (F j) := by
  simp only [selectedSupport,disjoint_insert_left,disjoint_insert_right]
  simp [Ne.symm hij,Finset.disjoint_map]

theorem bprob_support_inter (p : I → ℝ) (s A B : Finset I) (hA : A⊆s) (hB : B⊆s) :
    bprob p s (fun t => A⊆t ∧ B⊆t) = ∏i∈A∪B,p i := by
  have he := bprob_support p s (A∪B) (union_subset hA hB)
  exact (bprob_congr p s fun _ _ => union_subset_iff.symm).trans he

theorem selectedSupport_probability (p : I → ℝ) (θ : ℝ) (s : Finset I)
    (L : Finset J) (F : J → Finset I) (hF : ∀j∈L,F j⊆s) {j : J} (hj : j∈L) :
    bprob (Sum.elim p (fun _ => θ)) (sumGround s L) (fun t => selectedSupport F j⊆t) =
      θ*bprob p s (fun t => F j⊆t) := by
  rw [bprob_support _ _ _ (selectedSupport_subset s L F hF hj),
    bprob_support p s _ (hF j hj)]
  simp [selectedSupport,prod_map]

theorem selectedSupport_joint (p : I → ℝ) (θ : ℝ) (s : Finset I)
    (L : Finset J) (F : J → Finset I) (hF : ∀j∈L,F j⊆s)
    {i j : J} (hi : i∈L) (hj : j∈L) (hij : i≠j) :
    bprob (Sum.elim p (fun _ => θ)) (sumGround s L)
      (fun t => selectedSupport F i⊆t ∧ selectedSupport F j⊆t) =
      θ^2*bprob p s (fun t => F i⊆t ∧ F j⊆t) := by
  rw [bprob_support_inter _ _ _ _ (selectedSupport_subset s L F hF hi)
    (selectedSupport_subset s L F hF hj), bprob_support_inter p s _ _ (hF i hi) (hF j hj)]
  have he : selectedSupport F i ∪ selectedSupport F j =
      insert (Sum.inr i) (insert (Sum.inr j) ((F i∪F j).map Function.Embedding.inl)) := by
    ext x
    simp only [selectedSupport,mem_union,mem_insert,Finset.map_union]
    tauto
  rw [he]
  simp [hij,prod_map,pow_two,mul_assoc]

theorem selected_eventMean (p : I → ℝ) (θ : ℝ) (s : Finset I)
    (L : Finset J) (F : J → Finset I) (hF : ∀j∈L,F j⊆s) :
    eventMean (Sum.elim p (fun _ => θ)) (sumGround s L) (selectedSupport F) L =
      θ*eventMean p s F L := by
  unfold eventMean
  rw [mul_sum]
  exact sum_congr rfl fun j hj => selectedSupport_probability p θ s L F hF hj

theorem selected_orderedOverlap (p : I → ℝ) (θ : ℝ) (s : Finset I)
    (L : Finset J) (F : J → Finset I) (hF : ∀j∈L,F j⊆s) :
    orderedOverlap (Sum.elim p (fun _ => θ)) (sumGround s L) (selectedSupport F) L =
      θ^2*orderedOverlap p s F L := by
  unfold orderedOverlap
  simp only [mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  by_cases hij : i=j
  · subst j
    simp
  · simp only [overlapPair,selectedSupport_disjoint F hij]
    split_ifs with h
    · exact selectedSupport_joint p θ s L F hF hi hj hij
    · ring
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.SelectedSupports

-- BEGIN MODULE BCProof.CliqueJoint
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

theorem cliqueEdges_overlap (C D : Finset V) :
    ¬Disjoint (cliqueEdges C) (cliqueEdges D) ↔ 2≤(C∩D).card := by
  rw [Finset.disjoint_iff_inter_eq_empty,←cliqueEdges_inter,←card_eq_zero,
    cliqueEdges_card,Nat.choose_eq_zero_iff]
  omega

theorem cliqueEdges_union_card (C D : Finset V) :
    (cliqueEdges C∪cliqueEdges D).card = C.card.choose 2+D.card.choose 2-(C∩D).card.choose 2 := by
  rw [card_union,←cliqueEdges_inter,cliqueEdges_card,cliqueEdges_card,cliqueEdges_card]

theorem cliqueEdges_image_inter (e : V ↪ W) (C D : Finset V) :
    (C.map e∩D.map e).card=(C∩D).card := by
  rw [←map_inter,card_map]

theorem clique_joint_probability (n : ℕ) (q : ℝ) (C D : Finset (Fin n)) :
    gnpProb n q (fun G => G.IsClique (C : Set (Fin n)) ∧ G.IsClique (D : Set (Fin n))) =
      q^(C.card.choose 2+D.card.choose 2-(C∩D).card.choose 2) := by
  rw [gnpProb_bprob]
  calc
    _ = bprob (fun _ => q) (edgeGround n) (fun t => cliqueEdges C⊆t ∧ cliqueEdges D⊆t) := by
      apply bprob_congr
      intro t ht
      rw [clique_iff_edges,clique_iff_edges,graphOf_edges t ht]
    _ = _ := by
      rw [bprob_support_inter _ _ _ _ (cliqueEdges_ground C) (cliqueEdges_ground D)]
      simp only [prod_const,cliqueEdges_union_card]

theorem clique_support_probability {n : ℕ} (q : ℝ) (C : Finset (Fin n)) :
    bprob (fun _ => q) (edgeGround n) (fun t => cliqueEdges C⊆t)=q^(C.card.choose 2) := by
  rw [bprob_support _ _ _ (cliqueEdges_ground C)]
  simp only [prod_const,cliqueEdges_card]

theorem clique_support_joint {n : ℕ} (q : ℝ) (C D : Finset (Fin n)) :
    bprob (fun _ => q) (edgeGround n) (fun t => cliqueEdges C⊆t ∧ cliqueEdges D⊆t)=
      q^(C.card.choose 2+D.card.choose 2-(C∩D).card.choose 2) := by
  rw [bprob_support_inter _ _ _ _ (cliqueEdges_ground C) (cliqueEdges_ground D)]
  simp only [prod_const,cliqueEdges_union_card]
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.CliqueJoint

-- BEGIN MODULE BCProof.ThinnedJanson
noncomputable section
open Finset
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

theorem no_events_le_selected (p : I → ℝ) (hp : ∀i,0≤p i ∧ p i≤1)
    (θ : ℝ) (hθ : 0≤θ ∧ θ≤1) (s : Finset I) (L : Finset J) (F : J → Finset I) :
    bprob p s (fun t => ∀j∈L,¬F j⊆t) ≤
      bprob (Sum.elim p (fun _ => θ)) (sumGround s L)
        (fun t => ∀j∈L,¬selectedSupport F j⊆t) := by
  rw [←bprob_sumGround_left p (fun _ : J => θ) s L (fun t => ∀j∈L,¬F j⊆t)]
  apply bprob_mono _ (fun x => by cases x with | inl i => exact hp i | inr _ => exact hθ)
  intro t _ h j hj hs
  apply h j hj
  intro i hi
  apply mem_preimage.mpr
  exact hs (mem_insert.mpr (Or.inr (mem_map.mpr ⟨i,hi,rfl⟩)))

theorem janson_thinned (p : I → ℝ) (hp : ∀i,0≤p i ∧ p i≤1)
    (θ : ℝ) (hθ : 0≤θ ∧ θ≤1) (s : Finset I) (L : Finset J)
    (F : J → Finset I) (hF : ∀j∈L,F j⊆s) :
    bprob p s (fun t => ∀j∈L,¬F j⊆t) ≤
      Real.exp (-θ*eventMean p s F L+θ^2*orderedOverlap p s F L/2) := by
  refine (no_events_le_selected p hp θ hθ s L F).trans ?_
  have h := janson_plain (Sum.elim p (fun _ => θ))
    (fun x => by cases x with | inl i => exact hp i | inr _ => exact hθ)
    (sumGround s L) (selectedSupport F) L
  rw [selected_eventMean p θ s L F hF,selected_orderedOverlap p θ s L F hF] at h
  simpa only [neg_mul] using h

theorem janson_optimized (p : I → ℝ) (hp : ∀i,0≤p i ∧ p i≤1)
    (s : Finset I) (L : Finset J) (F : J → Finset I) (hF : ∀j∈L,F j⊆s)
    (hμ : 0<eventMean p s F L) :
    bprob p s (fun t => ∀j∈L,¬F j⊆t) ≤
      Real.exp (-(eventMean p s F L)^2/(2*(eventMean p s F L+orderedOverlap p s F L))) := by
  let μ := eventMean p s F L
  let d := orderedOverlap p s F L
  have hd : 0≤d := orderedOverlap_nonneg p hp s F L
  have hμ' : 0<μ := hμ
  have hden : 0<μ+d := by positivity
  have hθ : 0≤μ/(μ+d) ∧ μ/(μ+d)≤1 :=
    ⟨(div_pos hμ' hden).le,(div_le_one hden).mpr (by linarith)⟩
  refine (janson_thinned p hp (μ/(μ+d)) hθ s L F hF).trans (Real.exp_le_exp.mpr ?_)
  change -(μ/(μ+d))*μ+(μ/(μ+d))^2*d/2 ≤ -μ^2/(2*(μ+d))
  apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hden))
  field_simp
  nlinarith [sq_nonneg μ]
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.ThinnedJanson

-- BEGIN MODULE BCProof.InclusiveOverlap
noncomputable section
open Finset
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

def inclusivePair (p : I → ℝ) (s : Finset I) (F : J → Finset I) (i j : J) : ℝ :=
  if ¬Disjoint (F i) (F j) then bprob p s (fun t => F i⊆t ∧ F j⊆t) else 0

theorem inclusive_eq_mean_overlap (p : I → ℝ) (s : Finset I) (F : J → Finset I)
    (L : Finset J) (hF : ∀j∈L,(F j).Nonempty) :
    (∑i∈L,∑j∈L,inclusivePair p s F i j) = eventMean p s F L+orderedOverlap p s F L := by
  have hi (i : J) (hi : i∈L) :
      (∑j∈L,inclusivePair p s F i j) = bprob p s (fun t => F i⊆t)+∑j∈L,overlapPair p s F i j := by
    have he (j : J) : inclusivePair p s F i j =
        (if j=i then bprob p s (fun t => F i⊆t) else 0)+overlapPair p s F i j := by
      by_cases hij : j=i
      · subst j
        have hn : ¬Disjoint (F i) (F i) := by simpa using (hF i hi).ne_empty
        have hp : bprob p s (fun t => F i⊆t ∧ F i⊆t)=bprob p s (fun t => F i⊆t) :=
          bprob_congr p s fun _ _ => and_self_iff
        simp only [inclusivePair,if_pos hn,ite_true,overlapPair_self,add_zero,hp]
      · simp [inclusivePair,overlapPair,hij,Ne.symm hij]
    simp_rw [he]
    rw [sum_add_distrib]
    simp [hi]
  calc
    _ = ∑i∈L,(bprob p s (fun t => F i⊆t)+∑j∈L,overlapPair p s F i j) := sum_congr rfl fun i h => hi i h
    _ = _ := sum_add_distrib

theorem janson_inclusive (p : I → ℝ) (hp : ∀i,0≤p i ∧ p i≤1)
    (s : Finset I) (L : Finset J) (F : J → Finset I) (hF : ∀j∈L,F j⊆s)
    (hne : ∀j∈L,(F j).Nonempty) (hμ : 0<eventMean p s F L)
    (R : ℝ) (hR : 0<R)
    (hbound : (∑i∈L,∑j∈L,inclusivePair p s F i j) ≤ (eventMean p s F L)^2*R) :
    bprob p s (fun t => ∀j∈L,¬F j⊆t) ≤ Real.exp (-1/(2*R)) := by
  rw [inclusive_eq_mean_overlap p s F L hne] at hbound
  have hd := orderedOverlap_nonneg p hp s F L
  have he : 0<eventMean p s F L+orderedOverlap p s F L := by positivity
  refine (janson_optimized p hp s L F hF hμ).trans (Real.exp_le_exp.mpr ?_)
  apply (div_le_div_iff₀ (by positivity : 0<2*(eventMean p s F L+orderedOverlap p s F L))
    (by positivity : 0<2*R)).mpr
  nlinarith only [hbound]
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.InclusiveOverlap

-- BEGIN MODULE BCProof.SubsetCount

namespace BollobasChromatic.Main.BCFresh
open Finset

 theorem intersection_count_le {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset V) (r l : ℕ) (hC : C.card = r) (hl : l ≤ r) :
    ((univ.powersetCard r).filter (fun D => (C ∩ D).card = l)).card ≤
      r.choose l * (Fintype.card V - l).choose (r - l) := by
  let F : Finset V → Finset (Finset V) := fun T =>
    (univ.powersetCard r).filter (T ⊆ ·)
  have hsub : (univ.powersetCard r).filter (fun D => (C ∩ D).card = l) ⊆
      (C.powersetCard l).biUnion F := by
    intro D hD
    obtain ⟨hDr, hDl⟩ := mem_filter.mp hD
    apply mem_biUnion.mpr
    refine ⟨C ∩ D, mem_powersetCard.mpr ⟨inter_subset_left, hDl⟩, ?_⟩
    exact mem_filter.mpr ⟨hDr, inter_subset_right⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have hcount (T : Finset V) (hT : T ∈ C.powersetCard l) :
      (F T).card = (Fintype.card V - l).choose (r - l) := by
    have hTl := (mem_powersetCard.mp hT).2
    simpa only [F, card_univ, hTl] using
      card_filter_powersetCard_subset T univ r (subset_univ _) (by omega)
  calc
    _ = ∑ _T ∈ C.powersetCard l, (Fintype.card V - l).choose (r - l) :=
      sum_congr rfl hcount
    _ ≤ _ := by simp only [sum_const, smul_eq_mul, card_powersetCard, hC, le_refl]

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.SubsetCount

-- BEGIN MODULE BCProof.QuadraticEndpoints

namespace BollobasChromatic.Main.BCFresh

 theorem quadratic_le_max {a b c u v x : ℝ} (ha : 0 ≤ a)
    (hu : u ≤ x) (hv : x ≤ v) :
    a*x^2+b*x+c ≤ max (a*u^2+b*u+c) (a*v^2+b*v+c) := by
  by_cases he : u = v
  · have hx : x = u := by linarith
    subst x
    exact le_max_left _ _
  have huv : 0 < v-u := by have := hu.trans hv; exact sub_pos.mpr (lt_of_le_of_ne this he)
  have hp : 0 ≤ a*(x-u)*(v-x) :=
    mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hu)) (sub_nonneg.mpr hv)
  let M := max (a*u^2+b*u+c) (a*v^2+b*v+c)
  have h1 := mul_le_mul_of_nonneg_left (le_max_left (a*u^2+b*u+c) (a*v^2+b*v+c))
    (sub_nonneg.mpr hv)
  have h2 := mul_le_mul_of_nonneg_left (le_max_right (a*u^2+b*u+c) (a*v^2+b*v+c))
    (sub_nonneg.mpr hu)
  change (v-x)*(a*u^2+b*u+c) ≤ (v-x)*M at h1
  change (x-u)*(a*v^2+b*v+c) ≤ (x-u)*M at h2
  have hh : (v-u)*(a*x^2+b*x+c) ≤ (v-u)*M := by nlinarith
  exact le_of_mul_le_mul_left hh huv

noncomputable def smallLog (a R D x : ℝ) : ℝ :=
  x*(2*Real.log R-Real.log D)+a*x*(x-1)/2

noncomputable def largeLog (a R D x : ℝ) : ℝ :=
  R*Real.log 2+x*(Real.log R-Real.log D)+a*x*(x-1)/2

 theorem smallLog_le_max {a R D u v x : ℝ} (ha : 0 ≤ a) (hu : u ≤ x) (hv : x ≤ v) :
    smallLog a R D x ≤ max (smallLog a R D u) (smallLog a R D v) := by
  have he (z : ℝ) : (a/2)*z^2+(2*Real.log R-Real.log D-a/2)*z+0 = smallLog a R D z := by
    unfold smallLog
    ring
  simpa only [he] using quadratic_le_max (a := a/2) (b := 2*Real.log R-Real.log D-a/2)
    (c := 0) (by positivity) hu hv

 theorem largeLog_le_max {a R D u v x : ℝ} (ha : 0 ≤ a) (hu : u ≤ x) (hv : x ≤ v) :
    largeLog a R D x ≤ max (largeLog a R D u) (largeLog a R D v) := by
  have he (z : ℝ) : (a/2)*z^2+(Real.log R-Real.log D-a/2)*z+R*Real.log 2 =
      largeLog a R D z := by
    unfold largeLog
    ring
  simpa only [he] using quadratic_le_max (a := a/2) (b := Real.log R-Real.log D-a/2)
    (c := R*Real.log 2) (by positivity) hu hv

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.QuadraticEndpoints

-- BEGIN MODULE BCProof.ChooseRatio

namespace BollobasChromatic.Main.BCFresh

 theorem choose_ratio_le (m r l : ℕ) (hr : r < m) (hl : l ≤ r) :
    (r.choose l : ℝ) / (m.choose l : ℝ) ≤ ((r : ℝ) / (m - r : ℕ)) ^ l := by
  have hd : (0 : ℝ) < (m - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hr
  have hb : (0 : ℝ) < (m.choose l : ℕ) := by
    exact_mod_cast Nat.choose_pos (hl.trans hr.le)
  have hf : (0 : ℝ) < (l.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos l
  have hu : (r.choose l : ℝ) ≤ (r : ℝ)^l / l.factorial := Nat.choose_le_pow_div l r
  have hlo : ((m - r : ℕ) : ℝ)^l / l.factorial ≤ (m.choose l : ℝ) := by
    refine le_trans ?_ (Nat.pow_le_choose l m)
    apply div_le_div_of_nonneg_right _ hf.le
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show m-r ≤ m+1-l by omega)) l
  rw [div_pow]
  apply (div_le_div_iff₀ hb (pow_pos hd l)).mpr
  calc
    (r.choose l : ℝ) * ((m-r : ℕ) : ℝ)^l ≤
        ((r : ℝ)^l / l.factorial) * ((m-r : ℕ) : ℝ)^l :=
      mul_le_mul_of_nonneg_right hu (by positivity)
    _ = (r : ℝ)^l * (((m-r : ℕ) : ℝ)^l / l.factorial) := by ring
    _ ≤ (r : ℝ)^l * (m.choose l : ℝ) :=
      mul_le_mul_of_nonneg_left hlo (by positivity)

 theorem contained_ratio (m r l : ℕ) (hr : r ≤ m) (hl : l ≤ r) :
    ((m-l).choose (r-l) : ℝ) / (m.choose r : ℝ) =
      (r.choose l : ℝ) / (m.choose l : ℝ) := by
  have hmr : (m.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hr))
  have hml : (m.choose l : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (hl.trans hr)))
  apply (div_eq_div_iff hmr hml).mpr
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_mul (n := m) hl)
  push_cast at h
  nlinarith only [h]

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.ChooseRatio

-- BEGIN MODULE BCProof.OverlapTerms

namespace BollobasChromatic.Main.BCFresh
open Finset

noncomputable def overlapTerm (r : ℕ) (a D : ℝ) (l : ℕ) : ℝ :=
  (r.choose l : ℝ) * ((r : ℝ)/D)^l * Real.exp (a*(l:ℝ)*((l:ℝ)-1)/2)

 theorem ratio_exp_identity {R D : ℝ} (hR : 0 < R) (hD : 0 < D) (l : ℕ) :
    (R/D)^l = Real.exp ((l:ℝ)*(Real.log R-Real.log D)) := by
  rw [Real.exp_nat_mul, Real.exp_sub, Real.exp_log hR, Real.exp_log hD]

 theorem overlapTerm_le_small (r l : ℕ) (a D : ℝ) (hr : 0 < r) (hD : 0 < D) :
    overlapTerm r a D l ≤ Real.exp (smallLog a r D l) := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hchoose : (r.choose l : ℝ) ≤ (r:ℝ)^l := by exact_mod_cast Nat.choose_le_pow r l
  calc
    overlapTerm r a D l ≤ (r:ℝ)^l*((r:ℝ)/D)^l*Real.exp (a*(l:ℝ)*((l:ℝ)-1)/2) := by
      unfold overlapTerm
      gcongr
    _ = Real.exp (smallLog a r D l) := by
      have hp : (r:ℝ)^l = Real.exp ((l:ℝ)*Real.log r) := by
        rw [Real.exp_nat_mul, Real.exp_log hr0]
      rw [ratio_exp_identity hr0 hD, hp]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold smallLog
      ring

 theorem overlapTerm_le_large (r l : ℕ) (a D : ℝ) (hr : 0 < r) (hD : 0 < D) :
    overlapTerm r a D l ≤ Real.exp (largeLog a r D l) := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hchoose : (r.choose l : ℝ) ≤ (2:ℝ)^r := by exact_mod_cast Nat.choose_le_two_pow r l
  calc
    overlapTerm r a D l ≤ (2:ℝ)^r*((r:ℝ)/D)^l*Real.exp (a*(l:ℝ)*((l:ℝ)-1)/2) := by
      unfold overlapTerm
      gcongr
    _ = Real.exp (largeLog a r D l) := by
      have hp : (2:ℝ)^r = Real.exp ((r:ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
      rw [ratio_exp_identity hr0 hD, hp]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1

 theorem overlapTerm_endpoint_bound (r l : ℕ) (a D B : ℝ) (hr : 4 ≤ r)
    (ha : 0 ≤ a) (hD : 0 < D) (hl : 2 ≤ l) (hlr : l ≤ r)
    (hs2 : Real.exp (smallLog a r D 2) ≤ B)
    (hsm : Real.exp (smallLog a r D ((r:ℝ)/2)) ≤ B)
    (hlm : Real.exp (largeLog a r D ((r:ℝ)/2)) ≤ B)
    (hlr' : Real.exp (largeLog a r D r) ≤ B) : overlapTerm r a D l ≤ B := by
  have hrpos : 0 < r := by omega
  by_cases hh : (l:ℝ) ≤ (r:ℝ)/2
  · refine (overlapTerm_le_small r l a D hrpos hD).trans ?_
    have he := smallLog_le_max (R := (r:ℝ)) (D := D) (u := 2) ha (by exact_mod_cast hl) hh
    refine (Real.exp_le_exp.mpr he).trans ?_
    rcases le_total (smallLog a r D 2) (smallLog a r D ((r:ℝ)/2)) with h | h
    · simpa only [max_eq_right h] using hsm
    · simpa only [max_eq_left h] using hs2
  · refine (overlapTerm_le_large r l a D hrpos hD).trans ?_
    have he := largeLog_le_max (R := (r:ℝ)) (D := D) ha (le_of_not_ge hh)
      (show (l:ℝ) ≤ r by exact_mod_cast hlr)
    refine (Real.exp_le_exp.mpr he).trans ?_
    rcases le_total (largeLog a r D ((r:ℝ)/2)) (largeLog a r D r) with h | h
    · simpa only [max_eq_right h] using hlr'
    · simpa only [max_eq_left h] using hlm

 theorem sum_overlapTerm_le (r : ℕ) (a D B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ l ∈ Icc 2 r, overlapTerm r a D l ≤ B) :
    ∑ l ∈ Icc 2 r, overlapTerm r a D l ≤ (r:ℝ)*B := by
  calc
    _ ≤ ∑ _l ∈ Icc 2 r, B := sum_le_sum hb
    _ = ((Icc 2 r).card : ℝ)*B := by simp
    _ ≤ (r:ℝ)*B := mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show (Icc 2 r).card ≤ r by simp)) hB

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.OverlapTerms

-- BEGIN MODULE BCProof.WeightedOverlap

namespace BollobasChromatic.Main.BCFresh
open Finset

noncomputable def overlapWeight {V : Type*} [DecidableEq V] (a : ℝ) (C D : Finset V) : ℝ :=
  if 2 ≤ (C ∩ D).card then
    Real.exp (a*((C ∩ D).card:ℝ)*(((C ∩ D).card:ℝ)-1)/2) else 0

 theorem sum_overlap_by_card {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset V) (r : ℕ) (hC : C.card = r) (a : ℝ) :
    ∑ D ∈ univ.powersetCard r, overlapWeight a C D =
      ∑ l ∈ Icc 2 r,
        (((univ.powersetCard r).filter (fun D => (C ∩ D).card = l)).card:ℝ)*
          Real.exp (a*(l:ℝ)*((l:ℝ)-1)/2) := by
  have he (l : ℕ) :
      (((univ.powersetCard r).filter (fun D => (C ∩ D).card = l)).card:ℝ)*
        Real.exp (a*(l:ℝ)*((l:ℝ)-1)/2) =
      ∑ D ∈ univ.powersetCard r, if (C ∩ D).card = l then
        Real.exp (a*(l:ℝ)*((l:ℝ)-1)/2) else 0 := by
    rw [← sum_filter]
    simp
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro D hD
  have hcard : (C ∩ D).card ≤ r := hC ▸ card_le_card inter_subset_left
  by_cases htwo : 2 ≤ (C ∩ D).card
  · unfold overlapWeight
    rw [if_pos htwo]
    symm
    rw [sum_eq_single (C ∩ D).card]
    · simp
    · intro l hl hne
      simp only [if_neg (Ne.symm hne)]
    · intro hn
      exact (hn (mem_Icc.mpr ⟨htwo,hcard⟩)).elim
  · unfold overlapWeight
    rw [if_neg htwo]
    symm
    apply sum_eq_zero
    intro l hl
    apply if_neg
    intro heq
    exact htwo (heq ▸ (mem_Icc.mp hl).1)

 theorem intersection_count_normalized {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset V) (r l : ℕ) (hC : C.card = r) (hr : r < Fintype.card V) (hl : l ≤ r) :
    (((univ.powersetCard r).filter (fun D => (C ∩ D).card = l)).card:ℝ) /
        ((Fintype.card V).choose r:ℝ) ≤
      (r.choose l:ℝ)*((r:ℝ)/(Fintype.card V-r:ℕ))^l := by
  have hb : (0:ℝ) < ((Fintype.card V).choose r:ℝ) := by
    exact_mod_cast Nat.choose_pos hr.le
  calc
    _ ≤ ((r.choose l:ℝ)*((Fintype.card V-l).choose (r-l):ℝ)) /
        ((Fintype.card V).choose r:ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast intersection_count_le C r l hC hl) hb.le
    _ = (r.choose l:ℝ)*((r.choose l:ℝ)/((Fintype.card V).choose l:ℝ)) := by
      rw [mul_div_assoc, contained_ratio (Fintype.card V) r l hr.le hl]
    _ ≤ _ := mul_le_mul_of_nonneg_left (choose_ratio_le (Fintype.card V) r l hr hl) (by positivity)

 theorem fixed_overlap_bound {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset V) (r : ℕ) (hC : C.card = r) (hr : r < Fintype.card V) (a : ℝ) :
    (∑ D ∈ univ.powersetCard r, overlapWeight a C D) /
        ((Fintype.card V).choose r:ℝ) ≤
      ∑ l ∈ Icc 2 r, overlapTerm r a (Fintype.card V-r:ℕ) l := by
  rw [sum_overlap_by_card C r hC a, sum_div]
  apply sum_le_sum
  intro l hl
  have h := mul_le_mul_of_nonneg_right
    (intersection_count_normalized C r l hC hr (mem_Icc.mp hl).2)
    (Real.exp_pos (a*(l:ℝ)*((l:ℝ)-1)/2)).le
  simpa only [overlapTerm, div_mul_eq_mul_div] using h

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.WeightedOverlap

-- BEGIN MODULE BCProof.CliqueMoments
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exp_choose_difference (a : ℝ) (r l : ℕ) (hl : l≤r) :
    Real.exp (-a)^(r.choose 2+r.choose 2-l.choose 2) =
      (Real.exp (-a)^r.choose 2)^2*Real.exp (a*(l:ℝ)*((l:ℝ)-1)/2) := by
  have hc : l.choose 2≤r.choose 2+r.choose 2 := (Nat.choose_le_choose 2 hl).trans (Nat.le_add_right _ _)
  simp only [←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  rw [Nat.cast_sub hc,Nat.cast_add]
  simp only [Nat.cast_choose_two]
  norm_num
  ring

omit [DecidableEq V] in
theorem clique_eventMean {n : ℕ} (e : V ↪ Fin n) (a : ℝ) (r : ℕ) :
    eventMean (fun _ => Real.exp (-a)) (edgeGround n)
      (fun C => cliqueEdges (C.map e)) (univ.powersetCard r) =
      ((Fintype.card V).choose r:ℝ)*Real.exp (-a)^r.choose 2 := by
  unfold eventMean
  calc
    _ = ∑_C∈(univ : Finset V).powersetCard r,Real.exp (-a)^r.choose 2 := by
      apply sum_congr rfl
      intro C hC
      rw [clique_support_probability,card_map,(mem_powersetCard.mp hC).2]
    _ = _ := by simp

omit [Fintype V] in
theorem clique_inclusivePair {n : ℕ} (e : V ↪ Fin n) (a : ℝ) (r : ℕ)
    (C D : Finset V) (hC : C.card=r) (hD : D.card=r) :
    inclusivePair (fun _ => Real.exp (-a)) (edgeGround n) (fun C => cliqueEdges (C.map e)) C D =
      (Real.exp (-a)^r.choose 2)^2*overlapWeight a C D := by
  unfold inclusivePair
  dsimp only
  simp only [cliqueEdges_overlap,cliqueEdges_image_inter]
  unfold overlapWeight
  split_ifs
  · rw [clique_support_joint,card_map,card_map,cliqueEdges_image_inter,hC,hD]
    exact exp_choose_difference a r (C∩D).card (hC ▸ card_le_card inter_subset_left)
  · ring

theorem clique_failure_bound {n : ℕ} (e : V ↪ Fin n) (a : ℝ) (ha : 0≤a) (r : ℕ)
    (hr : 2≤r) (hrm : r<Fintype.card V) (B : ℝ) (hB : 0<B)
    (hb : (∑l∈Icc 2 r,overlapTerm r a (Fintype.card V-r:ℕ) l)≤B) :
    gnpProb n (Real.exp (-a))
      (fun G => ∀C∈(univ : Finset V).powersetCard r,¬G.IsClique (C.map e : Set (Fin n))) ≤
        Real.exp (-1/(2*B)) := by
  let L := (univ : Finset V).powersetCard r
  let F : Finset V → Finset (Sym2 (Fin n)) := fun C => cliqueEdges (C.map e)
  let b := Real.exp (-a)^r.choose 2
  let N : ℝ := (Fintype.card V).choose r
  have hN : 0<N := by
    change (0:ℝ)<((Fintype.card V).choose r:ℝ)
    exact_mod_cast Nat.choose_pos hrm.le
  have hbpos : 0<b := by positivity
  have hμ : eventMean (fun _ => Real.exp (-a)) (edgeGround n) F L=N*b := clique_eventMean e a r
  have heprob : gnpProb n (Real.exp (-a))
      (fun G => ∀C∈L,¬G.IsClique (C.map e : Set (Fin n))) =
      bprob (fun _ => Real.exp (-a)) (edgeGround n) (fun t => ∀C∈L,¬F C⊆t) := by
    rw [gnpProb_bprob]
    apply bprob_congr
    intro t ht
    simp only [clique_iff_edges,graphOf_edges t ht]
    rfl
  rw [heprob]
  apply janson_inclusive _ (fun _ => ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)⟩)
    _ L F (fun C _ => cliqueEdges_ground (C.map e))
  · intro C hC
    apply card_pos.mp
    rw [cliqueEdges_card,card_map,(mem_powersetCard.mp hC).2]
    exact Nat.choose_pos hr
  · rw [hμ]
    exact mul_pos hN hbpos
  · exact hB
  · rw [hμ]
    have hrow (C : Finset V) (hC : C∈L) :
        (∑D∈L,overlapWeight a C D)≤N*B := by
      have hh := (fixed_overlap_bound C r (mem_powersetCard.mp hC).2 hrm a).trans hb
      exact (div_le_iff₀ hN).mp hh |>.trans_eq (mul_comm B N)
    calc
      _ = ∑C∈L,b^2*(∑D∈L,overlapWeight a C D) := by
        apply sum_congr rfl
        intro C hC
        rw [mul_sum]
        apply sum_congr rfl
        intro D hD
        exact clique_inclusivePair e a r C D (mem_powersetCard.mp hC).2 (mem_powersetCard.mp hD).2
      _ ≤ ∑_C∈L,b^2*(N*B) := sum_le_sum fun C hC => mul_le_mul_of_nonneg_left (hrow C hC) (sq_nonneg b)
      _ = _ := by
        simp only [sum_const,nsmul_eq_mul]
        have hcard : (L.card:ℝ)=N := by simp [L,N]
        rw [hcard]
        ring
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.CliqueMoments

-- BEGIN MODULE BCProof.BernoulliComplement
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BollobasChromatic.Main.BCFresh
variable {I : Type*} [DecidableEq I]

theorem bweight_compl (p : I → ℝ) (s t : Finset I) (ht : t⊆s) :
    bweight p s (s\t)=bweight (fun i => 1-p i) s t := by
  have he : s\(s\t)=t := Finset.sdiff_sdiff_eq_self ht
  simp only [bweight,he,sub_sub_cancel]
  ring

theorem bmean_compl (p : I → ℝ) (s : Finset I) (f : Finset I → ℝ) :
    bmean p s (fun t => f (s\t))=bmean (fun i => 1-p i) s f := by
  unfold bmean
  apply sum_bij (fun t _ => s\t)
  · intro t _
    exact mem_powerset.mpr sdiff_subset
  · intro t ht u hu he
    have h := congrArg (fun v => s\v) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht),Finset.sdiff_sdiff_eq_self (mem_powerset.mp hu)] using h
  · intro t ht
    exact ⟨s\t,mem_powerset.mpr sdiff_subset,Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht)⟩
  · intro t ht
    have hh := bweight_compl (fun i => 1-p i) s t (mem_powerset.mp ht)
    simp only [sub_sub_cancel] at hh
    rw [hh]

theorem graphOf_compl {n : ℕ} (t : Finset (Sym2 (Fin n))) (ht : t⊆edgeGround n) :
    graphOf (edgeGround n\t)=(graphOf t)ᶜ := by
  apply SimpleGraph.edgeSet_injective
  have h1 := graphOf_edges (edgeGround n\t) sdiff_subset
  have h2 := graphOf_edges t ht
  have hc : ((graphOf t)ᶜ).edgeFinset=edgeGround n\(graphOf t).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ i j => simp [edgeGround,SimpleGraph.compl_adj]
  have he : (graphOf (edgeGround n\t)).edgeFinset=((graphOf t)ᶜ).edgeFinset := by rw [h1,hc,h2]
  simpa only [SimpleGraph.coe_edgeFinset] using congrArg (fun v : Finset (Sym2 (Fin n)) => (v : Set (Sym2 (Fin n)))) he

theorem gnpProb_complement (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => P Gᶜ)=gnpProb n (1-p) P := by
  simp only [gnpProb_bprob]
  unfold bprob
  calc
    _ = bmean (fun _ => p) (edgeGround n) (fun t => bindicator (fun u => P (graphOf u)) (edgeGround n\t)) := by
      apply bmean_congr
      intro t ht
      simp only [bindicator,graphOf_compl t ht]
    _ = _ := bmean_compl _ _ _
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.BernoulliComplement

-- BEGIN MODULE BCProof.GraphProbability
noncomputable section
open Finset SimpleGraph Filter
open scoped Classical Topology
namespace BollobasChromatic.Main.BCFresh

theorem gnpProb_mono (n : ℕ) (p : ℝ) (hp : 0≤p ∧ p≤1)
    {P Q : SimpleGraph (Fin n) → Prop} (h : ∀G,P G→Q G) : gnpProb n p P≤gnpProb n p Q := by
  simp only [gnpProb_bprob]
  exact bprob_mono _ (fun _ => hp) _ (fun t _ => h (graphOf t))

theorem gnpProb_congr (n : ℕ) (p : ℝ) {P Q : SimpleGraph (Fin n) → Prop}
    (h : ∀G,P G↔Q G) : gnpProb n p P=gnpProb n p Q := by
  unfold gnpProb
  exact sum_congr rfl fun G _ => by rw [h G]

theorem gnpProb_cover {J : Type*} (n : ℕ) (p : ℝ) (hp : 0≤p ∧ p≤1)
    (L : Finset J) (P : J → SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => ∃j∈L,P j G)≤∑j∈L,gnpProb n p (P j) := by
  simp only [gnpProb_bprob]
  exact bprob_cover_le _ (fun _ => hp) _ _ L _ (fun _ _ h => h)

theorem gnpProb_union (n : ℕ) (p : ℝ) (hp : 0≤p ∧ p≤1)
    (P Q : SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => P G∨Q G)≤gnpProb n p P+gnpProb n p Q := by
  simp only [gnpProb_bprob]
  exact bprob_union_le _ (fun _ => hp) _ _ _

theorem almostEvery_of_failure (p : ℝ) (hp : 0≤p ∧ p≤1)
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ᶠn in atTop,gnpProb n p (fun G => ¬P n G)≤b n) : AlmostEvery p P := by
  have hz : Tendsto (fun n => gnpProb n p (fun G => ¬P n G)) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n => gnpProb_nonneg n p hp _) h hb
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub hz
  simp only [sub_zero] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall fun n => by
    dsimp only
    rw [gnpProb_compl]
    ring

theorem almostEvery_and (p : ℝ) (hp : 0≤p ∧ p≤1)
    (P Q : (n : ℕ) → SimpleGraph (Fin n) → Prop)
    (hP : AlmostEvery p P) (hQ : AlmostEvery p Q) : AlmostEvery p (fun n G => P n G∧Q n G) := by
  have hp' : Tendsto (fun n => gnpProb n p (fun G => ¬P n G)) atTop (𝓝 0) := by
    simpa only [gnpProb_compl,sub_self] using (tendsto_const_nhds (x := (1:ℝ))).sub hP
  have hq' : Tendsto (fun n => gnpProb n p (fun G => ¬Q n G)) atTop (𝓝 0) := by
    simpa only [gnpProb_compl,sub_self] using (tendsto_const_nhds (x := (1:ℝ))).sub hQ
  apply almostEvery_of_failure p hp _ _ (by simpa only [add_zero] using hp'.add hq')
  apply Filter.Eventually.of_forall
  intro n
  calc
    _ = gnpProb n p (fun G => ¬P n G∨¬Q n G) := gnpProb_congr n p fun _ => not_and_or
    _ ≤ _ := gnpProb_union n p hp _ _
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.GraphProbability

-- BEGIN MODULE BCProof.SubsetFailure
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BollobasChromatic.Main.BCFresh

theorem no_clique_subtype {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) (r : ℕ) :
    (∀C⊆T,C.card=r → ¬G.IsClique (C:Set (Fin n))) ↔
      (∀D∈(univ : Finset ({x : Fin n // x ∈ T})).powersetCard r,
        ¬G.IsClique (D.map (Function.Embedding.subtype (fun x => x∈T)) : Set (Fin n))) := by
  constructor
  · intro h D hD
    apply h (D.map (Function.Embedding.subtype _))
    · intro x hx
      exact D.property_of_mem_map_subtype hx
    · simpa only [card_map] using (mem_powersetCard.mp hD).2
  · intro h C hCT hC
    let D := C.subtype (fun x => x∈T)
    have he : D.map (Function.Embedding.subtype (fun x => x∈T))=C :=
      Finset.subtype_map_of_mem (fun x hx => hCT hx)
    have hD : D.card=r := by rw [←card_map (Function.Embedding.subtype (fun x => x∈T)),he,hC]
    have hh := h D (mem_powersetCard.mpr ⟨subset_univ _,hD⟩)
    simpa only [he] using hh

theorem fixed_subset_failure (n : ℕ) (p a : ℝ) (ha : 0≤a) (hq : 1-p=Real.exp (-a))
    (T : Finset (Fin n)) (r : ℕ) (hr : 2≤r) (hrT : r<T.card) (B : ℝ) (hB : 0<B)
    (hb : (∑l∈Icc 2 r,overlapTerm r a (T.card-r:ℕ) l)≤B) :
    gnpProb n p (fun G => ∀C⊆T,C.card=r → ¬G.IsIndepSet (C:Set (Fin n)))≤Real.exp (-1/(2*B)) := by
  have he : gnpProb n p (fun G => ∀C⊆T,C.card=r → ¬G.IsIndepSet (C:Set (Fin n))) =
      gnpProb n (1-p) (fun G => ∀C⊆T,C.card=r → ¬G.IsClique (C:Set (Fin n))) := by
    rw [←gnpProb_complement]
    apply gnpProb_congr
    intro G
    simp only [SimpleGraph.isClique_compl]
  rw [he,hq]
  have he' : gnpProb n (Real.exp (-a)) (fun G => ∀C⊆T,C.card=r → ¬G.IsClique (C:Set (Fin n))) =
      gnpProb n (Real.exp (-a)) (fun G => ∀D∈(univ : Finset ({x : Fin n // x ∈ T})).powersetCard r,
        ¬G.IsClique (D.map (Function.Embedding.subtype (fun x => x∈T)):Set (Fin n))) :=
    gnpProb_congr n _ fun G => no_clique_subtype G T r
  rw [he']
  apply clique_failure_bound (Function.Embedding.subtype (fun x => x∈T)) a ha r hr
  · simpa using hrT
  · exact hB
  · simpa using hb

theorem all_subset_failure (n : ℕ) (p a : ℝ) (hp : 0≤p ∧ p≤1) (ha : 0≤a)
    (hq : 1-p=Real.exp (-a)) (m r : ℕ) (hr : 2≤r) (hrm : r < m)
    (B : ℝ) (hB : 0<B) (hb : (∑l∈Icc 2 r,overlapTerm r a (m-r:ℕ) l)≤B) :
    gnpProb n p (fun G => ¬ ∀ T : Finset (Fin n),T.card=m →
      ∃C⊆T,C.card=r ∧ G.IsIndepSet (C:Set (Fin n))) ≤ (2:ℝ)^n*Real.exp (-1/(2*B)) := by
  have he : gnpProb n p (fun G => ¬ ∀ T : Finset (Fin n),T.card=m →
      ∃C⊆T,C.card=r ∧ G.IsIndepSet (C:Set (Fin n))) =
      gnpProb n p (fun G => ∃T∈(univ:Finset (Fin n)).powersetCard m,
        ∀C⊆T,C.card=r → ¬G.IsIndepSet (C:Set (Fin n))) := by
    apply gnpProb_congr
    intro G
    simp only [not_forall,not_exists,not_and,mem_powersetCard,subset_univ,true_and,exists_prop]
  rw [he]
  refine (gnpProb_cover n p hp _ _).trans ?_
  calc
    _ ≤ ∑_T∈(univ:Finset (Fin n)).powersetCard m,Real.exp (-1/(2*B)) := by
      apply sum_le_sum
      intro T hT
      have hcard := (mem_powersetCard.mp hT).2
      exact fixed_subset_failure n p a ha hq T r hr (hcard ▸ hrm) B hB (by simpa only [hcard] using hb)
    _ = (n.choose m:ℝ)*Real.exp (-1/(2*B)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_two_pow n m) (Real.exp_pos _).le
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.SubsetFailure

-- BEGIN MODULE BCProof.FirstMoment
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BollobasChromatic.Main.BCFresh

theorem clique_first_moment (n : ℕ) (q : ℝ) (hq : 0≤q ∧ q≤1) (r : ℕ) :
    gnpProb n q (fun G => ∃C : Finset (Fin n),C.card=r ∧ G.IsClique (C:Set (Fin n))) ≤
      expCliques n q r := by
  calc
    _ = gnpProb n q (fun G => ∃C∈(univ : Finset (Fin n)).powersetCard r,G.IsClique (C:Set (Fin n))) := by
      apply gnpProb_congr
      intro G
      simp
    _ ≤ ∑C∈(univ : Finset (Fin n)).powersetCard r,gnpProb n q (fun G => G.IsClique (C:Set (Fin n))) :=
      gnpProb_cover n q hq _ _
    _ = _ := by
      calc
        _ = ∑_C∈(univ : Finset (Fin n)).powersetCard r,q^r.choose 2 := by
          apply sum_congr rfl
          intro C hC
          rw [clique_probability,(mem_powersetCard.mp hC).2]
        _ = _ := by simp [expCliques]

theorem independent_first_moment (n : ℕ) (p : ℝ) (hp : 0≤p ∧ p≤1) (r : ℕ) :
    gnpProb n p (fun G => ∃C : Finset (Fin n),C.card=r ∧ G.IsIndepSet (C:Set (Fin n))) ≤
      expCliques n (1-p) r := by
  have he : gnpProb n p (fun G => ∃C : Finset (Fin n),C.card=r ∧ G.IsIndepSet (C:Set (Fin n))) =
      gnpProb n (1-p) (fun G => ∃C : Finset (Fin n),C.card=r ∧ G.IsClique (C:Set (Fin n))) := by
    rw [←gnpProb_complement]
    apply gnpProb_congr
    intro G
    simp only [SimpleGraph.isClique_compl]
  rw [he]
  exact clique_first_moment n (1-p) ⟨sub_nonneg.mpr hp.2,sub_le_self 1 hp.1⟩ r
end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.FirstMoment

-- BEGIN MODULE BCProof.FirstMomentBound

namespace BollobasChromatic.Main.BCFresh

 theorem factorial_exp_lower (t : ℕ) (ht : 1 ≤ t) :
    Real.exp ((t:ℝ)*Real.log t-t) ≤ (t.factorial:ℝ) := by
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hlog := Real.log_nonneg htR
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hlogpi := Real.log_nonneg hpi
  have h := Stirling.le_log_factorial_stirling (by omega : t ≠ 0)
  have hbound : (t:ℝ)*Real.log t-t ≤ Real.log (t.factorial:ℝ) := by linarith
  exact (Real.exp_le_exp.mpr hbound).trans_eq (Real.exp_log (by positivity))

 theorem first_moment_bound (n t : ℕ) (hn : 1 ≤ n) (ht : 1 ≤ t) (a : ℝ) :
    (n.choose t:ℝ)*(Real.exp (-a))^(t.choose 2) ≤
      Real.exp ((t:ℝ)*(Real.log n+1-Real.log t-a*((t:ℝ)-1)/2)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hf := factorial_exp_lower t ht
  have hc := (Nat.choose_le_pow_div t n : (n.choose t:ℝ) ≤ (n:ℝ)^t/(t.factorial:ℝ))
  have hden := div_le_div_of_nonneg_left (show (0:ℝ) ≤ (n:ℝ)^t by positivity)
    (Real.exp_pos _) hf
  have h := mul_le_mul_of_nonneg_right (hc.trans hden)
    (show (0:ℝ) ≤ (Real.exp (-a))^(t.choose 2) by positivity)
  refine h.trans_eq ?_
  have hnexp : (n:ℝ)^t = Real.exp ((t:ℝ)*Real.log n) := by
    rw [Real.exp_nat_mul, Real.exp_log hnR]
  rw [hnexp, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add,
    Nat.cast_choose_two]
  congr 1
  ring

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.FirstMomentBound

-- BEGIN MODULE BCProof.ScalarLimits

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

 theorem log_over_self {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => Real.log (u n) / u n) atTop (𝓝 0) := by
  simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hu

 theorem pow_log_over_self {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) (k : ℕ) :
    Tendsto (fun n => Real.log (u n)^k / u n) atTop (𝓝 0) := by
  simpa only [one_mul, add_zero, Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp hu

 theorem nat_floor_error_scaled {f g : ℕ → ℝ} (hf : ∀ᶠ n in atTop, 0 ≤ f n)
    (hg : Tendsto g atTop atTop) :
    Tendsto (fun n => ((⌊f n⌋₊ : ℝ)-f n)/g n) atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero (b := -1) (B := 0) _ _ hg
  · exact Filter.Eventually.of_forall fun n => by linarith [Nat.lt_floor_add_one (f n)]
  · filter_upwards [hf] with n hn
    exact sub_nonpos.mpr (Nat.floor_le hn)

 theorem int_floor_error_scaled (f : ℕ → ℝ) {g : ℕ → ℝ}
    (hg : Tendsto g atTop atTop) :
    Tendsto (fun n => ((⌊f n⌋ : ℝ)-f n)/g n) atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero (b := -1) (B := 0) _ _ hg
  · exact Filter.Eventually.of_forall fun n => by linarith [Int.lt_floor_add_one (f n)]
  · exact Filter.Eventually.of_forall fun n => sub_nonpos.mpr (Int.floor_le (f n))

 theorem nat_floor_scaled {f g : ℕ → ℝ} {c : ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : Tendsto g atTop atTop)
    (hfg : Tendsto (fun n => f n/g n) atTop (𝓝 c)) :
    Tendsto (fun n => (⌊f n⌋₊ : ℝ)/g n) atTop (𝓝 c) := by
  have h := (nat_floor_error_scaled hf hg).add hfg
  simp only [zero_add] at h
  convert h using 1
  ext n
  ring

 theorem int_floor_scaled (f : ℕ → ℝ) {g : ℕ → ℝ} {c : ℝ}
    (hg : Tendsto g atTop atTop)
    (hfg : Tendsto (fun n => f n/g n) atTop (𝓝 c)) :
    Tendsto (fun n => (⌊f n⌋ : ℝ)/g n) atTop (𝓝 c) := by
  have h := (int_floor_error_scaled f hg).add hfg
  simp only [zero_add] at h
  convert h using 1
  ext n
  ring

 theorem log_difference_limit {f g : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hfg : Tendsto (fun n => f n/g n) atTop (𝓝 c)) :
    Tendsto (fun n => Real.log (f n)-Real.log (g n)) atTop (𝓝 (Real.log c)) := by
  have h := (Real.continuousAt_log hc.ne').tendsto.comp hfg
  apply h.congr'
  filter_upwards [hf, hg] with n hn hm
  exact Real.log_div hn.ne' hm.ne'

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.ScalarLimits

-- BEGIN MODULE BCProof.RatioLimits

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

 theorem diverges_of_ratio {f g : ℕ → ℝ} {c : ℝ} (hg : Tendsto g atTop atTop)
    (hc : 0 < c) (hfg : Tendsto (fun n => f n/g n) atTop (𝓝 c)) :
    Tendsto f atTop atTop := by
  apply (hg.atTop_mul_pos hc hfg).congr'
  filter_upwards [hg.eventually (eventually_gt_atTop 0)] with n hn
  field_simp

 theorem nat_floor_relative {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun n => (⌊f n⌋₊ : ℝ)/f n) atTop (𝓝 1) := by
  apply nat_floor_scaled (hf.eventually (eventually_ge_atTop 0)) hf
  apply tendsto_const_nhds.congr'
  filter_upwards [hf.eventually (eventually_gt_atTop 0)] with n hn
  exact (div_self hn.ne').symm

 theorem log_ratio_limit {f g : ℕ → ℝ} {c : ℝ}
    (hg : Tendsto g atTop atTop) (hc : 0 < c)
    (hfg : Tendsto (fun n => f n/g n) atTop (𝓝 c)) :
    Tendsto (fun n => Real.log (f n)/Real.log (g n)) atTop (𝓝 1) := by
  have hf := diverges_of_ratio hg hc hfg
  have hd := log_difference_limit hc (hf.eventually (eventually_gt_atTop 0))
    (hg.eventually (eventually_gt_atTop 0)) hfg
  have hlg := Real.tendsto_log_atTop.comp hg
  have hz := hd.div_atTop hlg
  have h := hz.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hlg.eventually (eventually_gt_atTop 0)] with n hn
  dsimp only [Function.comp_def] at hn ⊢
  field_simp
  ring

 theorem reciprocal_diverges {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hp : ∀ᶠ n in atTop, 0 < f n) :
    Tendsto (fun n => (f n)⁻¹) atTop atTop := by
  exact (show Tendsto f atTop (𝓝[>] (0:ℝ)) from
    tendsto_nhdsWithin_iff.mpr ⟨hf, hp⟩).inv_tendsto_nhdsGT_zero

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.RatioLimits

-- BEGIN MODULE BCProof.ParameterBasics

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

noncomputable def logN (n : ℕ) : ℝ := Real.log n
noncomputable def loglogN (n : ℕ) : ℝ := Real.log (logN n)
noncomputable def subsetRaw (n : ℕ) : ℝ := (n:ℝ)/(logN n)^2
noncomputable def subsetSize (n : ℕ) : ℕ := ⌊subsetRaw n⌋₊
noncomputable def cliqueRaw (a : ℝ) (n : ℕ) : ℝ :=
  (2*logN n-(27/4:ℝ)*loglogN n)/a
noncomputable def cliqueSize (a : ℝ) (n : ℕ) : ℕ := ⌊cliqueRaw a n⌋₊

 theorem logN_atTop : Tendsto logN atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
 theorem loglogN_atTop : Tendsto loglogN atTop atTop :=
  Real.tendsto_log_atTop.comp logN_atTop
 theorem loglogN_div_logN : Tendsto (fun n => loglogN n/logN n) atTop (𝓝 0) :=
  log_over_self logN_atTop

 theorem subsetRaw_atTop : Tendsto subsetRaw atTop atTop := by
  have h := pow_log_over_self (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop) 2
  have hp : ∀ᶠ n : ℕ in atTop, 0 < (Real.log (n:ℝ))^2/(n:ℝ) := by
    filter_upwards [eventually_gt_atTop (1:ℕ)] with n hn
    have hn1 : (1:ℝ) < n := by exact_mod_cast hn
    have hl := Real.log_pos hn1
    positivity
  change Tendsto (fun n : ℕ => (n:ℝ)/(Real.log (n:ℝ))^2) atTop atTop
  simpa only [inv_div] using reciprocal_diverges h hp

 theorem subsetSize_atTop : Tendsto (fun n => (subsetSize n:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp subsetRaw_atTop)

 theorem subsetSize_relative :
    Tendsto (fun n => (subsetSize n:ℝ)/subsetRaw n) atTop (𝓝 1) :=
  nat_floor_relative subsetRaw_atTop

 theorem cliqueRaw_div_logN (a : ℝ) :
    Tendsto (fun n => cliqueRaw a n/logN n) atTop (𝓝 (2/a)) := by
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2)).sub
    (loglogN_div_logN.const_mul (27/4:ℝ))).div_const a
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [logN_atTop.eventually (eventually_gt_atTop 0)] with n hn
  unfold cliqueRaw
  field_simp

 theorem cliqueRaw_atTop {a : ℝ} (ha : 0 < a) : Tendsto (cliqueRaw a) atTop atTop :=
  diverges_of_ratio logN_atTop (div_pos (by norm_num) ha) (cliqueRaw_div_logN a)

 theorem cliqueSize_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (cliqueSize a n:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp (cliqueRaw_atTop ha))

 theorem cliqueSize_div_logN {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (cliqueSize a n:ℝ)/logN n) atTop (𝓝 (2/a)) :=
  nat_floor_scaled ((cliqueRaw_atTop ha).eventually (eventually_ge_atTop 0))
    logN_atTop (cliqueRaw_div_logN a)

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.ParameterBasics

-- BEGIN MODULE BCProof.ParameterLogs

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

 theorem subsetRaw_log : ∀ᶠ n : ℕ in atTop,
    Real.log (subsetRaw n) = logN n-2*loglogN n := by
  filter_upwards [eventually_gt_atTop (1:ℕ)] with n hn
  have hn1 : (1:ℝ) < n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hl : 0 < logN n := Real.log_pos hn1
  unfold subsetRaw loglogN
  rw [Real.log_div hn0.ne' (pow_ne_zero 2 hl.ne'), Real.log_pow]
  rfl

 theorem subset_log_error :
    Tendsto (fun n => Real.log (subsetSize n:ℝ)-(logN n-2*loglogN n)) atTop (𝓝 0) := by
  have h := log_difference_limit (by norm_num : (0:ℝ)<1)
    (subsetSize_atTop.eventually (eventually_gt_atTop 0))
    (subsetRaw_atTop.eventually (eventually_gt_atTop 0)) subsetSize_relative
  simp only [Real.log_one] at h
  apply h.congr'
  filter_upwards [subsetRaw_log] with n hn
  rw [hn]

 theorem subset_log_div_logN :
    Tendsto (fun n => Real.log (subsetSize n:ℝ)/logN n) atTop (𝓝 1) := by
  have he := subset_log_error.div_atTop logN_atTop
  have h := he.add ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub
    (loglogN_div_logN.const_mul 2))
  simp only [mul_zero, sub_zero, zero_add] at h
  apply h.congr'
  filter_upwards [logN_atTop.eventually (eventually_gt_atTop 0)] with n hn
  field_simp
  ring

 theorem subset_loglog_error :
    Tendsto (fun n => Real.log (Real.log (subsetSize n:ℝ))-loglogN n) atTop (𝓝 0) := by
  have h := log_difference_limit (by norm_num : (0:ℝ)<1)
    ((Real.tendsto_log_atTop.comp subsetSize_atTop).eventually (eventually_gt_atTop 0))
    (logN_atTop.eventually (eventually_gt_atTop 0)) subset_log_div_logN
  simpa only [Real.log_one, Function.comp_def, loglogN] using h

 theorem subset_log_refined :
    Tendsto (fun n => (Real.log (subsetSize n:ℝ)-logN n)/loglogN n)
      atTop (𝓝 (-2)) := by
  have h := (subset_log_error.div_atTop loglogN_atTop).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2))
  simp only [zero_sub] at h
  apply h.congr'
  filter_upwards [loglogN_atTop.eventually (eventually_gt_atTop 0)] with n hn
  field_simp
  ring

 theorem subset_loglog_relative :
    Tendsto (fun n => Real.log (Real.log (subsetSize n:ℝ))/loglogN n) atTop (𝓝 1) := by
  have h := (subset_loglog_error.div_atTop loglogN_atTop).add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [loglogN_atTop.eventually (eventually_gt_atTop 0)] with n hn
  field_simp
  ring

 theorem cliqueSize_refined {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => ((cliqueSize a n:ℝ)-(2/a)*logN n)/loglogN n)
      atTop (𝓝 (-(27/4:ℝ)/a)) := by
  have he := nat_floor_error_scaled ((cliqueRaw_atTop ha).eventually (eventually_ge_atTop 0))
    loglogN_atTop
  have h := he.sub (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (27/4:ℝ)/a) atTop (𝓝 ((27/4:ℝ)/a)))
  simp only [zero_sub] at h
  rw [neg_div]
  apply h.congr'
  filter_upwards [loglogN_atTop.eventually (eventually_gt_atTop 0)] with n hn
  unfold cliqueSize cliqueRaw
  field_simp
  ring

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.ParameterLogs

-- BEGIN MODULE BCProof.ParameterMargins

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

 theorem cliqueSize_div_subset_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (cliqueSize a n:ℝ)/Real.log (subsetSize n:ℝ)) atTop (𝓝 (2/a)) := by
  have h := (cliqueSize_div_logN ha).div subset_log_div_logN one_ne_zero
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [logN_atTop.eventually (eventually_gt_atTop 0)] with n hn
  dsimp only [Pi.div_apply]
  field_simp

 theorem cliqueSize_div_subset {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (cliqueSize a n:ℝ)/(subsetSize n:ℝ)) atTop (𝓝 0) := by
  have hs := pow_log_over_self (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop) 3
  have h := ((cliqueSize_div_logN ha).mul hs).div subsetSize_relative one_ne_zero
  simp only [mul_zero, zero_div] at h
  apply h.congr'
  filter_upwards [logN_atTop.eventually (eventually_gt_atTop 0),
    subsetSize_atTop.eventually (eventually_gt_atTop 0), eventually_gt_atTop (0:ℕ)] with n hn hm hn0
  have hnreal : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn0
  dsimp only [Pi.div_apply]
  unfold logN at hn
  unfold subsetRaw logN
  field_simp

 theorem clique_threshold_slack {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => ((2/a)*(Real.log (subsetSize n:ℝ)-
      (4/3:ℝ)*Real.log (Real.log (subsetSize n:ℝ)))-(cliqueSize a n:ℝ))/loglogN n)
      atTop (𝓝 (1/(12*a))) := by
  have h := ((subset_log_refined.const_mul (2/a)).sub
    (subset_loglog_relative.const_mul (8/(3*a)))).sub (cliqueSize_refined ha)
  have he : (2/a)*(-2)-(8/(3*a))*1-(-(27/4:ℝ)/a) = 1/(12*a) := by ring
  rw [he] at h
  convert h using 1
  ext n
  ring

 theorem clique_below_threshold {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, (cliqueSize a n:ℝ) ≤ (2/a)*(Real.log (subsetSize n:ℝ)-
      (4/3:ℝ)*Real.log (Real.log (subsetSize n:ℝ))) := by
  have hp : (0:ℝ) < 1/(12*a) := by positivity
  filter_upwards [(clique_threshold_slack ha).eventually (lt_mem_nhds hp),
    loglogN_atTop.eventually (eventually_gt_atTop 0)] with n hn hl
  have hdiff := (div_pos_iff_of_pos_right hl).mp hn
  linarith

 theorem remainder_div_subset {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => ((subsetSize n:ℝ)-(cliqueSize a n:ℝ))/(subsetSize n:ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub
    (cliqueSize_div_subset ha)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [subsetSize_atTop.eventually (eventually_gt_atTop 0)] with n hn
  field_simp

 theorem remainder_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (subsetSize n:ℝ)-(cliqueSize a n:ℝ)) atTop atTop :=
  diverges_of_ratio subsetSize_atTop (by norm_num) (remainder_div_subset ha)

 theorem remainder_log_error {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => Real.log ((subsetSize n:ℝ)-(cliqueSize a n:ℝ))-
      Real.log (subsetSize n:ℝ)) atTop (𝓝 0) := by
  simpa only [Real.log_one] using log_difference_limit (by norm_num : (0:ℝ)<1)
    ((remainder_atTop ha).eventually (eventually_gt_atTop 0))
    (subsetSize_atTop.eventually (eventually_gt_atTop 0)) (remainder_div_subset ha)

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.ParameterMargins

-- BEGIN MODULE BCProof.S0Parameters

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

noncomputable def baseRate (p : ℝ) : ℝ := Real.log (1/(1-p))
noncomputable def s0Constant (p : ℝ) : ℝ :=
  (Real.log (baseRate p)+2*Real.log (Real.exp 1/2))/baseRate p+1
noncomputable def s0Approx (p : ℝ) (n : ℕ) : ℝ :=
  (2*logN n-loglogN n)/baseRate p+s0Constant p

 theorem baseRate_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < baseRate p := by
  apply Real.log_pos
  exact (one_lt_div (by linarith : (0:ℝ)<1-p)).mpr (by linarith)

 theorem s0_floor_formula {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ n in atTop, s0 p n = ⌊s0Approx p n⌋ := by
  have ha := baseRate_pos hp0 hp1
  filter_upwards [logN_atTop.eventually (eventually_gt_atTop 0)] with n hn
  unfold s0 s0Approx s0Constant
  congr 1
  change 2*(logN n/baseRate p)-Real.log (logN n/baseRate p)/baseRate p+
    2*(Real.log (Real.exp 1/2)/baseRate p)+1 = _
  rw [Real.log_div hn.ne' ha.ne']
  unfold loglogN
  ring

 theorem s0Approx_div_logN (p : ℝ) :
    Tendsto (fun n => s0Approx p n/logN n) atTop (𝓝 (2/baseRate p)) := by
  have h := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2)).sub
    loglogN_div_logN).div_const (baseRate p)).add (logN_atTop.const_div_atTop (s0Constant p))
  simp only [sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [logN_atTop.eventually (eventually_gt_atTop 0)] with n hn
  unfold s0Approx
  field_simp

 theorem s0_div_logN {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => (s0 p n:ℝ)/logN n) atTop (𝓝 (2/baseRate p)) := by
  have h := int_floor_scaled (s0Approx p) logN_atTop (s0Approx_div_logN p)
  apply h.congr'
  filter_upwards [s0_floor_formula hp0 hp1] with n hn
  rw [hn]

 theorem s0_atTop {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => (s0 p n:ℝ)) atTop atTop :=
  diverges_of_ratio logN_atTop (div_pos (by norm_num) (baseRate_pos hp0 hp1))
    (s0_div_logN hp0 hp1)

 theorem s0_refined {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => ((s0 p n:ℝ)-(2/baseRate p)*logN n)/loglogN n)
      atTop (𝓝 (-1/baseRate p)) := by
  have he := int_floor_error_scaled (s0Approx p) loglogN_atTop
  have h := (he.add (loglogN_atTop.const_div_atTop (s0Constant p))).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1/baseRate p) atTop (𝓝 (1/baseRate p)))
  simp only [add_zero, zero_sub] at h
  rw [neg_div]
  apply h.congr'
  filter_upwards [s0_floor_formula hp0 hp1,
    loglogN_atTop.eventually (eventually_gt_atTop 0)] with n hn hl
  rw [hn]
  unfold s0Approx
  field_simp
  ring

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.S0Parameters

-- BEGIN MODULE BCProof.LowerParameters

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

noncomputable def lowerSize (p : ℝ) (n : ℕ) : ℕ := (s0 p n).toNat + 1

 theorem lowerSize_cast {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ n in atTop, (lowerSize p n : ℝ) = (s0 p n : ℝ)+1 := by
  filter_upwards [(s0_atTop hp0 hp1).eventually (eventually_ge_atTop 0)] with n hn
  have hz : 0 ≤ s0 p n := by exact_mod_cast hn
  have he := Int.toNat_of_nonneg hz
  unfold lowerSize
  push_cast
  exact_mod_cast congrArg (fun z : ℤ => z+1) he

 theorem lowerSize_div_logN {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => (lowerSize p n:ℝ)/logN n) atTop (𝓝 (2/baseRate p)) := by
  have h := (s0_div_logN hp0 hp1).add (logN_atTop.const_div_atTop 1)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [lowerSize_cast hp0 hp1] with n hn
  rw [hn, add_div]

 theorem lowerSize_refined {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => ((lowerSize p n:ℝ)-(2/baseRate p)*logN n)/loglogN n)
      atTop (𝓝 (-1/baseRate p)) := by
  have h := (s0_refined hp0 hp1).add (loglogN_atTop.const_div_atTop 1)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [lowerSize_cast hp0 hp1] with n hn
  rw [hn]
  ring

 theorem lowerSize_log_relative {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => Real.log (lowerSize p n:ℝ)/loglogN n) atTop (𝓝 1) :=
  log_ratio_limit logN_atTop (div_pos (by norm_num) (baseRate_pos hp0 hp1))
    (lowerSize_div_logN hp0 hp1)

noncomputable def firstMomentBracket (p : ℝ) (n : ℕ) : ℝ :=
  logN n+1-Real.log (lowerSize p n:ℝ)-baseRate p*((lowerSize p n:ℝ)-1)/2

 theorem firstMomentBracket_limit {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => firstMomentBracket p n/loglogN n) atTop (𝓝 (-1/2:ℝ)) := by
  have ha := baseRate_pos hp0 hp1
  have h := ((lowerSize_log_relative hp0 hp1).neg.sub
    ((lowerSize_refined hp0 hp1).const_mul (baseRate p/2))).add
      (loglogN_atTop.const_div_atTop (1+baseRate p/2))
  have he : -1-baseRate p/2*(-1/baseRate p)+0 = (-1/2:ℝ) := by
    field_simp
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [loglogN_atTop.eventually (eventually_gt_atTop 0)] with n hn
  unfold firstMomentBracket
  field_simp
  ring

 theorem firstMoment_exp_tendsto {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => Real.exp ((lowerSize p n:ℝ)*firstMomentBracket p n)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => Real.exp (-(loglogN n)/4)) atTop (𝓝 0) :=
    by
      simpa only [neg_div, Function.comp_def] using Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp
          (Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ)<4) loglogN_atTop))
  refine squeeze_zero' (Eventually.of_forall (fun n => (Real.exp_pos _).le)) ?_ hlim
  filter_upwards [(firstMomentBracket_limit hp0 hp1).eventually
    (gt_mem_nhds (by norm_num : (-1/2:ℝ)< -1/4)),
    loglogN_atTop.eventually (eventually_gt_atTop 0)] with n hn hl
  apply Real.exp_le_exp.mpr
  have hb : firstMomentBracket p n ≤ -loglogN n/4 := by
    have hh := (div_lt_iff₀ hl).mp hn
    linarith
  have ht : (1:ℝ) ≤ lowerSize p n := by unfold lowerSize; norm_cast; omega
  nlinarith

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.LowerParameters

-- BEGIN MODULE BCProof.LowerColoring

namespace BollobasChromatic.Main.BCFresh
open Finset SimpleGraph

 theorem indep_card_le_of_no_set {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (s : ℕ)
    (hno : ∀ C : Finset V, C.card = s+1 → ¬G.IsIndepSet (C:Set V))
    (C : Finset V) (hC : G.IsIndepSet (C:Set V)) : C.card ≤ s := by
  by_contra hh
  obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq (show s+1 ≤ C.card by omega)
  apply hno D hD
  exact hC.mono hDC

 theorem chromatic_lower_of_indep_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : ℕ) (hs : 0 < s)
    (hb : ∀ C : Finset V, G.IsIndepSet (C:Set V) → C.card ≤ s) :
    (Fintype.card V:ℝ)/(s:ℝ) ≤ (G.chromaticNumber.toNat:ℝ) := by
  classical
  let c : G.Coloring (Fin G.chromaticNumber.toNat) := G.colorable_chromaticNumber_of_fintype.some
  have hcard : Fintype.card V =
      ∑ i : Fin G.chromaticNumber.toNat, ((univ:Finset V).filter (fun v => c v = i)).card := by
    simpa only [card_univ] using (card_eq_sum_card_fiberwise
      (f := c) (s := (univ:Finset V)) (t := univ) (fun _ _ => mem_univ _))
  have hfib (i : Fin G.chromaticNumber.toNat) :
      ((univ:Finset V).filter (fun v => c v = i)).card ≤ s := by
    apply hb
    intro v hv w hw _ hadj
    exact c.valid hadj ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm)
  have hbound : Fintype.card V ≤ G.chromaticNumber.toNat*s := by
    rw [hcard]
    calc
      _ ≤ ∑ _i : Fin G.chromaticNumber.toNat, s := sum_le_sum (fun i _ => hfib i)
      _ = _ := by simp
  apply (div_le_iff₀ (show (0:ℝ)<s by exact_mod_cast hs)).mpr
  exact_mod_cast hbound

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.LowerColoring

-- BEGIN MODULE BCProof.IndependentColoring

namespace BollobasChromatic.Main.BCFresh
open Finset SimpleGraph

 theorem coloring_from_independent_family {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V))
    (hF : ∀ C ∈ F, G.IsIndepSet (C : Set V)) :
    G.Colorable (F.card+(univ \ F.biUnion id).card) := by
  classical
  let R := univ \ F.biUnion id
  let f : V → (↑F ⊕ ↑R) := fun v =>
    if hv : ∃ C ∈ F, v ∈ C then Sum.inl ⟨hv.choose, hv.choose_spec.1⟩
    else Sum.inr ⟨v, mem_sdiff.mpr ⟨mem_univ _, by
      intro hh
      obtain ⟨C,hC,hvC⟩ := mem_biUnion.mp hh
      exact hv ⟨C,hC,hvC⟩⟩⟩
  have hc : G.Coloring (↑F ⊕ ↑R) := Coloring.mk f (by
    intro v w hvw he
    by_cases hv : ∃ C ∈ F, v ∈ C
    · by_cases hw : ∃ C ∈ F, w ∈ C
      · simp only [f, dif_pos hv, dif_pos hw, Sum.inl.injEq, Subtype.mk.injEq] at he
        have hwC : w ∈ hv.choose := by rw [he]; exact hw.choose_spec.2
        exact hF hv.choose hv.choose_spec.1 hv.choose_spec.2 hwC hvw.ne hvw
      · simp only [f, dif_pos hv, dif_neg hw, Sum.inl_ne_inr] at he
    · by_cases hw : ∃ C ∈ F, w ∈ C
      · simp only [f, dif_neg hv, dif_pos hw, Sum.inr_ne_inl] at he
      · simp only [f, dif_neg hv, dif_neg hw, Sum.inr.injEq, Subtype.mk.injEq] at he
        exact hvw.ne he)
  simpa only [Fintype.card_sum, Fintype.card_coe] using hc.colorable

 theorem chromatic_of_independent_family {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V))
    (hF : ∀ C ∈ F, G.IsIndepSet (C : Set V)) :
    G.chromaticNumber.toNat ≤ F.card+(univ \ F.biUnion id).card :=
  ENat.toNat_le_of_le_natCast (coloring_from_independent_family G F hF).chromaticNumber_le

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.IndependentColoring

-- BEGIN MODULE BCProof.GreedyColoring

namespace BollobasChromatic.Main.BCFresh
open Finset SimpleGraph

 theorem independent_packing_remainder {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r m : ℕ) (hr : 0 < r)
    (hsets : ∀ T : Finset V, T.card = m →
      ∃ C ⊆ T, C.card = r ∧ G.IsIndepSet (C : Set V)) :
    ∃ F : Finset (Finset V),
      (∀ C ∈ F, C.card = r ∧ G.IsIndepSet (C : Set V)) ∧
      (↑F : Set (Finset V)).Pairwise Disjoint ∧
      (univ \ F.biUnion id).card < m := by
  classical
  let good : Finset (Finset V) → Prop := fun F =>
    (∀ C ∈ F, C.card = r ∧ G.IsIndepSet (C : Set V)) ∧
    (↑F : Set (Finset V)).Pairwise Disjoint
  let B := (univ : Finset (Finset (Finset V))).filter good
  have hB : B.Nonempty := ⟨∅, by simp [B,good]⟩
  obtain ⟨F,hFB,hmax⟩ := Finset.exists_max_image B Finset.card hB
  have hF : good F := (mem_filter.mp hFB).2
  refine ⟨F,hF.1,hF.2,?_⟩
  by_contra hbad
  obtain ⟨T,hTR,hTm⟩ := exists_subset_card_eq (le_of_not_gt hbad)
  obtain ⟨C,hCT,hCr,hCG⟩ := hsets T hTm
  have hCR : C ⊆ univ \ F.biUnion id := hCT.trans hTR
  have hdis (D : Finset V) (hD : D ∈ F) : Disjoint C D := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvD
    exact (mem_sdiff.mp (hCR hvC)).2 (mem_biUnion.mpr ⟨D,hD,hvD⟩)
  have hCF : C ∉ F := by
    intro hh
    have he := disjoint_self.mp (hdis C hh)
    have hc0 : C.card = 0 := by rw [he]; rfl
    omega
  have hnew : insert C F ∈ B := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,?_⟩
    · intro D hD
      rcases mem_insert.mp hD with rfl | hD
      · exact ⟨hCr,hCG⟩
      · exact hF.1 D hD
    · intro D hD E hE hne
      by_cases hDC : D = C
      · subst D
        exact hdis E (mem_of_mem_insert_of_ne hE (Ne.symm hne))
      · have hDF : D ∈ F := mem_of_mem_insert_of_ne hD hDC
        by_cases hEC : E = C
        · subst E
          exact (hdis D hDF).symm
        · exact hF.2 hDF (mem_of_mem_insert_of_ne hE hEC) hne
  have hh := hmax (insert C F) hnew
  rw [card_insert_of_notMem hCF] at hh
  omega

 theorem greedy_chromatic_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r m : ℕ) (hr : 0 < r)
    (hsets : ∀ T : Finset V, T.card = m →
      ∃ C ⊆ T, C.card = r ∧ G.IsIndepSet (C : Set V)) :
    (G.chromaticNumber.toNat:ℝ) ≤ (Fintype.card V:ℝ)/(r:ℝ)+(m:ℝ) := by
  classical
  obtain ⟨F,hF,hdis,hrem⟩ := independent_packing_remainder G r m hr hsets
  have hcards : (F.biUnion id).card = F.card*r := by
    change (F.biUnion (fun C => C)).card = F.card*r
    rw [card_biUnion hdis]
    calc
      ∑ C ∈ F, C.card = ∑ _C ∈ F, r := sum_congr rfl (fun C hC => (hF C hC).1)
      _ = _ := by simp
  have hsize : F.card*r ≤ Fintype.card V := by
    rw [← hcards, ← card_univ (α := V)]
    exact card_le_card (subset_univ _)
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hreal : (F.card:ℝ) ≤ (Fintype.card V:ℝ)/(r:ℝ) :=
    (le_div_iff₀ hr0).mpr (by exact_mod_cast hsize)
  have hchi := chromatic_of_independent_family G F (fun C hC => (hF C hC).2)
  have hchi' : (G.chromaticNumber.toNat:ℝ) ≤ (F.card:ℝ)+((univ \ F.biUnion id).card:ℝ) := by
    exact_mod_cast hchi
  have hrem' : ((univ \ F.biUnion id).card:ℝ) ≤ (m:ℝ) := by exact_mod_cast hrem.le
  linarith

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.GreedyColoring

-- BEGIN MODULE BCProof.UpperParameters

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

 theorem upper_scaled_gap {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => (logN n/loglogN n)*
      ((s0 p n:ℝ)/(cliqueSize (baseRate p) n:ℝ)+
        (subsetSize n:ℝ)*(s0 p n:ℝ)/(n:ℝ)-1)) atTop (𝓝 (23/8:ℝ)) := by
  have ha := baseRate_pos hp0 hp1
  have hr := ((s0_refined hp0 hp1).sub (cliqueSize_refined ha)).div
    (cliqueSize_div_logN ha) (ne_of_gt (div_pos (by norm_num : (0:ℝ)<2) ha))
  have he : (-1/baseRate p-(-(27/4:ℝ)/baseRate p))/(2/baseRate p) = (23/8:ℝ) := by
    field_simp
    ring
  rw [he] at hr
  have hm := (subsetSize_relative.mul (s0_div_logN hp0 hp1)).mul
    (loglogN_atTop.const_div_atTop (1:ℝ))
  simp only [mul_zero] at hm
  have h := hr.add hm
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [logN_atTop.eventually (eventually_gt_atTop 0),
    loglogN_atTop.eventually (eventually_gt_atTop 0),
    (cliqueSize_atTop ha).eventually (eventually_gt_atTop 0),
    eventually_gt_atTop (0:ℕ)] with n hL hell hR hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  dsimp only [Pi.div_apply]
  unfold subsetRaw
  field_simp
  ring

 theorem upper_parameter_bound {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ n : ℕ in atTop,
      (n:ℝ)/(cliqueSize (baseRate p) n:ℝ)+(subsetSize n:ℝ) ≤
      ((n:ℝ)/(s0 p n:ℝ))*(1+3*loglogN n/logN n) := by
  have ha := baseRate_pos hp0 hp1
  filter_upwards [(upper_scaled_gap hp0 hp1).eventually (gt_mem_nhds (by norm_num : (23/8:ℝ)<3)),
    logN_atTop.eventually (eventually_gt_atTop 0),
    loglogN_atTop.eventually (eventually_gt_atTop 0),
    (cliqueSize_atTop ha).eventually (eventually_gt_atTop 0),
    (s0_atTop hp0 hp1).eventually (eventually_gt_atTop 0),
    eventually_gt_atTop (0:ℕ)] with n h hL hell hR hs hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hm := mul_lt_mul_of_pos_left h (div_pos hell hL)
  have he (d : ℝ) : (loglogN n/logN n)*((logN n/loglogN n)*d) = d := by field_simp
  rw [he] at hm
  rw [show loglogN n/logN n*3 = 3*loglogN n/logN n by ring] at hm
  have hb : (s0 p n:ℝ)/(cliqueSize (baseRate p) n:ℝ)+
      (subsetSize n:ℝ)*(s0 p n:ℝ)/(n:ℝ) ≤ 1+3*loglogN n/logN n := by
    linarith
  have hf := mul_le_mul_of_nonneg_left hb (div_pos hnpos hs).le
  have he2 : ((n:ℝ)/(s0 p n:ℝ))*((s0 p n:ℝ)/(cliqueSize (baseRate p) n:ℝ)+
      (subsetSize n:ℝ)*(s0 p n:ℝ)/(n:ℝ)) =
      (n:ℝ)/(cliqueSize (baseRate p) n:ℝ)+(subsetSize n:ℝ) := by
    field_simp
  rw [he2] at hf
  exact hf

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.UpperParameters

-- BEGIN MODULE BCProof.EndpointAlgebra

namespace BollobasChromatic.Main.BCFresh

 theorem small_endpoint_identity {R D : ℝ} (hR : 0 < R) (hD : 0 < D) (a : ℝ) :
    Real.exp (smallLog a R D 2) = Real.exp a * R^4 / D^2 := by
  have h4 : Real.exp (4*Real.log R) = R^4 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hR] using (Real.exp_nat_mul (Real.log R) 4)
  have h2 : Real.exp (2*Real.log D) = D^2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hD] using (Real.exp_nat_mul (Real.log D) 2)
  have he : smallLog a R D 2 = a+4*Real.log R-2*Real.log D := by
    unfold smallLog
    ring
  rw [he, Real.exp_sub, Real.exp_add, h4, h2]

 theorem small_endpoint_bound {R D M : ℝ} (hR : 0 < R) (hD : 0 < D)
    (hM : 0 < M) (hDM : M ≤ 2*D) (a : ℝ) :
    Real.exp (smallLog a R D 2) ≤ 4*Real.exp a*R^4/M^2 := by
  rw [small_endpoint_identity hR hD]
  apply (div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos hM)).mpr
  have hs : M^2 ≤ 4*D^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ Real.exp a*R^4 by positivity)
  nlinarith only [hh]

 theorem large_endpoint_bound {a R D L K : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (hrlog : Real.log R ≤ Real.log L+K)
    (hdlog : L-1 ≤ Real.log D)
    (hupper : a*R ≤ 2*L-(8/3:ℝ)*Real.log L)
    (hlower : L ≤ a*R)
    (hlarge : 6*(Real.log 2+K+1) ≤ Real.log L)
    (hlarge' : 18*a ≤ Real.log L) :
    largeLog a R D R ≤ -3*L := by
  have hb : Real.log 2+Real.log R-Real.log D+a*(R-1)/2 ≤ -Real.log L/6 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hb hR
  have hmul' := mul_le_mul_of_nonneg_left hlarge' hR
  have he : largeLog a R D R = R*(Real.log 2+Real.log R-Real.log D+a*(R-1)/2) := by
    unfold largeLog
    ring
  rw [he]
  nlinarith only [hmul, hmul', hlower]

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.EndpointAlgebra

-- BEGIN MODULE BCProof.MiddleLimits

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

 theorem remainder_log_ratio {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => Real.log ((subsetSize n:ℝ)-(cliqueSize a n:ℝ))/
      Real.log (subsetSize n:ℝ)) atTop (𝓝 1) :=
  log_ratio_limit subsetSize_atTop (by norm_num) (remainder_div_subset ha)

 theorem clique_log_ratio_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => Real.log (cliqueSize a n:ℝ)/Real.log (subsetSize n:ℝ)) atTop (𝓝 0) := by
  have h := (log_over_self (cliqueSize_atTop ha)).mul (cliqueSize_div_subset_log ha)
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [(cliqueSize_atTop ha).eventually (eventually_gt_atTop 0)] with n hn
  field_simp

 theorem midpoint_small_limit {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => smallLog a (cliqueSize a n) ((subsetSize n:ℝ)-(cliqueSize a n:ℝ))
      ((cliqueSize a n:ℝ)/2)/(Real.log (subsetSize n:ℝ))^2) atTop (𝓝 (-1/(2*a))) := by
  have hR := (cliqueSize_div_subset_log ha).div_const 2
  have hB := ((clique_log_ratio_zero ha).const_mul 2).sub (remainder_log_ratio ha)
  have hI := (Real.tendsto_log_atTop.comp subsetSize_atTop).const_div_atTop (1:ℝ)
  have h := (hR.mul hB).add ((hR.mul (hR.sub hI)).const_mul (a/2))
  have he : (2/a)/2*(2*0-1)+(a/2)*((2/a)/2*((2/a)/2-0)) = -1/(2*a) := by
    field_simp
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp subsetSize_atTop).eventually
    (eventually_gt_atTop 0)] with n hn
  dsimp only [Function.comp_def] at hn ⊢
  unfold smallLog
  field_simp

 theorem midpoint_large_limit {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => largeLog a (cliqueSize a n) ((subsetSize n:ℝ)-(cliqueSize a n:ℝ))
      ((cliqueSize a n:ℝ)/2)/(Real.log (subsetSize n:ℝ))^2) atTop (𝓝 (-1/(2*a))) := by
  have hR := (cliqueSize_div_subset_log ha).div_const 2
  have hB := (clique_log_ratio_zero ha).sub (remainder_log_ratio ha)
  have hI := (Real.tendsto_log_atTop.comp subsetSize_atTop).const_div_atTop (1:ℝ)
  have hZ := (cliqueSize_div_subset_log ha).mul
    ((Real.tendsto_log_atTop.comp subsetSize_atTop).const_div_atTop (Real.log 2))
  have h := (hZ.add (hR.mul hB)).add ((hR.mul (hR.sub hI)).const_mul (a/2))
  have he : ((2/a)*0+(2/a)/2*(0-1))+(a/2)*((2/a)/2*((2/a)/2-0)) = -1/(2*a) := by
    field_simp
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp subsetSize_atTop).eventually
    (eventually_gt_atTop 0)] with n hn
  dsimp only [Function.comp_def] at hn ⊢
  unfold largeLog
  field_simp

 theorem negative_quadratic_bound {f L : ℕ → ℝ} {c : ℝ}
    (hL : Tendsto L atTop atTop) (hc : c < 0)
    (hf : Tendsto (fun n => f n/(L n)^2) atTop (𝓝 c)) (b : ℝ) :
    ∀ᶠ n in atTop, f n ≤ -b*L n := by
  have hh : c < c/2 := by linarith
  filter_upwards [hf.eventually (gt_mem_nhds hh),
    hL.eventually (eventually_gt_atTop 0),
    hL.eventually (eventually_ge_atTop (-2*b/c))] with n hn hpos hlarge
  have hmul := (div_lt_iff₀ (sq_pos_of_pos hpos)).mp hn
  have hscale := mul_le_mul_of_nonpos_left hlarge (show c/2 ≤ 0 by linarith)
  have he : (c/2)*(-2*b/c) = -b := by field_simp [hc.ne]
  rw [he] at hscale
  have hlast := mul_le_mul_of_nonneg_right hscale hpos.le
  nlinarith only [hmul, hlast]

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.MiddleLimits

-- BEGIN MODULE BCProof.LargeEndpoint

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

 theorem large_endpoint_eventually {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, largeLog a (cliqueSize a n)
      ((subsetSize n:ℝ)-(cliqueSize a n:ℝ)) (cliqueSize a n) ≤
        -3*Real.log (subsetSize n:ℝ) := by
  have hL := Real.tendsto_log_atTop.comp subsetSize_atTop
  have hell := Real.tendsto_log_atTop.comp hL
  have hupper : 2/a < 3/a := by apply (div_lt_div_iff_of_pos_right ha).mpr; norm_num
  have hlower : 1/a < 2/a := by apply (div_lt_div_iff_of_pos_right ha).mpr; norm_num
  filter_upwards [(cliqueSize_div_subset_log ha).eventually (gt_mem_nhds hupper),
    (cliqueSize_div_subset_log ha).eventually (lt_mem_nhds hlower),
    (remainder_log_error ha).eventually (lt_mem_nhds (by norm_num : (-1:ℝ)<0)),
    clique_below_threshold ha,
    hL.eventually (eventually_gt_atTop 0),
    hell.eventually (eventually_ge_atTop (6*(Real.log 2+Real.log (3/a)+1))),
    hell.eventually (eventually_ge_atTop (18*a)),
    (cliqueSize_atTop ha).eventually (eventually_gt_atTop 0)] with n hu hl hd ht hL0 hlarge hlarge' hR
  dsimp only [Function.comp_def] at hL0 hlarge hlarge'
  have hu' := (div_lt_iff₀ hL0).mp hu
  have hl' := (lt_div_iff₀ hL0).mp hl
  have hlog : Real.log (cliqueSize a n:ℝ) ≤
      Real.log (Real.log (subsetSize n:ℝ))+Real.log (3/a) := by
    have hh := Real.log_le_log hR hu'.le
    rw [Real.log_mul (by positivity : (3/a:ℝ) ≠ 0) hL0.ne'] at hh
    linarith
  apply large_endpoint_bound ha hR.le hlog (by linarith)
  · have hh := mul_le_mul_of_nonneg_left ht ha.le
    field_simp at hh
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hl'.le ha.le
    field_simp at hh
    nlinarith
  · exact hlarge
  · exact hlarge'

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.LargeEndpoint

-- BEGIN MODULE BCProof.UniformOverlap

namespace BollobasChromatic.Main.BCFresh
open Filter Topology Finset

noncomputable def overlapConstant (a : ℝ) : ℝ := 4*Real.exp a+1

 theorem exp_decay_overlap {a R M : ℝ} (hR : 1 ≤ R) (hM : 1 ≤ M) :
    Real.exp (-3*Real.log M) ≤ overlapConstant a*R^4/M^2 := by
  have hM0 : 0 < M := by linarith
  have hlog := Real.log_nonneg hM
  have hp : Real.exp (-2*Real.log M) = 1/M^2 := by
    have he : Real.exp (2*Real.log M) = M^2 := by
      simpa only [Nat.cast_ofNat, Real.exp_log hM0] using (Real.exp_nat_mul (Real.log M) 2)
    rw [show -2*Real.log M = -(2*Real.log M) by ring, Real.exp_neg, he]
    simp
  have hR4 : 1 ≤ R^4 := one_le_pow₀ hR
  calc
    _ ≤ Real.exp (-2*Real.log M) := Real.exp_le_exp.mpr (by linarith)
    _ = 1/M^2 := hp
    _ ≤ overlapConstant a*R^4/M^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg M)
      unfold overlapConstant
      nlinarith [Real.exp_pos a]

 theorem uniform_overlap_eventually {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, 4 ≤ cliqueSize a n ∧ cliqueSize a n < subsetSize n ∧
      (∑ l ∈ Icc 2 (cliqueSize a n), overlapTerm (cliqueSize a n) a
        ((subsetSize n:ℝ)-(cliqueSize a n:ℝ)) l) ≤
          overlapConstant a*(cliqueSize a n:ℝ)^5/(subsetSize n:ℝ)^2 := by
  have hL := Real.tendsto_log_atTop.comp subsetSize_atTop
  have hc : -1/(2*a) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  filter_upwards [negative_quadratic_bound hL hc (midpoint_small_limit ha) 3,
    negative_quadratic_bound hL hc (midpoint_large_limit ha) 3,
    large_endpoint_eventually ha,
    (cliqueSize_div_subset ha).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    (cliqueSize_atTop ha).eventually (eventually_ge_atTop 4),
    subsetSize_atTop.eventually (eventually_ge_atTop 1)] with n hsm hlm hlr hratio hr hm
  have hM : (0:ℝ)<subsetSize n := by linarith
  have hR : (0:ℝ)<cliqueSize a n := by linarith
  have hhalf := (div_lt_iff₀ hM).mp hratio
  have hD : 0 < (subsetSize n:ℝ)-(cliqueSize a n:ℝ) := by linarith
  have hrnat : 4 ≤ cliqueSize a n := by exact_mod_cast hr
  refine ⟨hrnat, by exact_mod_cast (show (cliqueSize a n:ℝ)<subsetSize n by linarith), ?_⟩
  have hsmall := small_endpoint_bound hR hD hM (by linarith) a
  have hdecay := exp_decay_overlap (a := a) (by linarith : (1:ℝ)≤cliqueSize a n) hm
  have hb := sum_overlapTerm_le (cliqueSize a n) a
    ((subsetSize n:ℝ)-(cliqueSize a n:ℝ))
    (overlapConstant a*(cliqueSize a n:ℝ)^4/(subsetSize n:ℝ)^2)
    (by unfold overlapConstant; positivity) (fun l hl =>
      overlapTerm_endpoint_bound _ _ _ _ _ hrnat ha.le hD (mem_Icc.mp hl).1 (mem_Icc.mp hl).2
        (hsmall.trans (by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          unfold overlapConstant
          nlinarith [pow_nonneg hR.le 4]))
        ((Real.exp_le_exp.mpr hsm).trans hdecay)
        ((Real.exp_le_exp.mpr hlm).trans hdecay)
        ((Real.exp_le_exp.mpr hlr).trans hdecay))
  convert hb using 1
  ring

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.UniformOverlap

-- BEGIN MODULE BCProof.UnionRate

namespace BollobasChromatic.Main.BCFresh
open Filter Topology

 theorem variance_ratio_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (subsetSize n:ℝ)^2/((n:ℝ)*(cliqueSize a n:ℝ)^5)) atTop atTop := by
  have hsmall := pow_log_over_self (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop) 9
  have hlarge : Tendsto (fun n : ℕ => (n:ℝ)/(logN n)^9) atTop atTop := by
    have h := reciprocal_diverges hsmall (by
      filter_upwards [logN_atTop.eventually (eventually_gt_atTop 0),
        eventually_gt_atTop (0:ℕ)] with n hl hn
      change 0 < (logN n)^9/(n:ℝ)
      positivity)
    simpa only [inv_div, logN] using h
  have hc : 0 < 1/(2/a)^5 := by positivity
  have hcoef := (subsetSize_relative.pow 2).div ((cliqueSize_div_logN ha).pow 5)
    (by positivity : (2/a)^5 ≠ 0)
  simp only [one_pow] at hcoef
  have h := hlarge.atTop_mul_pos hc hcoef
  apply h.congr'
  filter_upwards [logN_atTop.eventually (eventually_gt_atTop 0),
    (cliqueSize_atTop ha).eventually (eventually_gt_atTop 0),
    eventually_gt_atTop (0:ℕ)] with n hl hr hn
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  dsimp only [Pi.div_apply, Pi.pow_apply]
  unfold subsetRaw
  field_simp

 theorem union_failure_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (2:ℝ)^n*Real.exp
      (-((subsetSize n:ℝ)^2)/(2*overlapConstant a*(cliqueSize a n:ℝ)^5)))
      atTop (𝓝 0) := by
  have hC : 0 < 2*overlapConstant a := by unfold overlapConstant; positivity
  have hlim : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ))) atTop (𝓝 0) :=
    by simpa only [Function.comp_def] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop))
  refine squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hlim
  filter_upwards [(variance_ratio_atTop ha).eventually
    (eventually_ge_atTop (2*overlapConstant a*(Real.log 2+1))),
    (cliqueSize_atTop ha).eventually (eventually_gt_atTop 0),
    eventually_gt_atTop (0:ℕ)] with n hn hr hn0
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hbound := (le_div_iff₀ (mul_pos hnR (pow_pos hr 5))).mp hn
  have hcut : (n:ℝ)*(Real.log 2+1) ≤
      (subsetSize n:ℝ)^2/(2*overlapConstant a*(cliqueSize a n:ℝ)^5) := by
    apply (le_div_iff₀ (mul_pos hC (pow_pos hr 5))).mpr
    nlinarith only [hbound]
  have hexp : (2:ℝ)^n = Real.exp ((n:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [hexp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.UnionRate

-- BEGIN MODULE BCProof.NativeBounds

namespace BollobasChromatic.Main.BCFresh
open Filter Topology Finset

 theorem baseRate_exp {p : ℝ} (hp1 : p < 1) : 1-p=Real.exp (-baseRate p) := by
  unfold baseRate
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log (by linarith : (0:ℝ)<1-p)]

 theorem upper_almostEvery {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    AlmostEvery p (fun n G => (G.chromaticNumber.toNat:ℝ) ≤
      (n:ℝ)/(s0 p n:ℝ)*(1+3*Real.log (Real.log (n:ℝ))/Real.log (n:ℝ))) := by
  have ha := baseRate_pos hp0 hp1
  have hp : 0≤p ∧ p≤1 := ⟨hp0.le,hp1.le⟩
  apply almostEvery_of_failure p hp _ _ (union_failure_tendsto ha)
  filter_upwards [uniform_overlap_eventually ha, upper_parameter_bound hp0 hp1,
    subsetSize_atTop.eventually (eventually_gt_atTop 0)] with n hov hup hm
  let B := overlapConstant (baseRate p)*(cliqueSize (baseRate p) n:ℝ)^5/(subsetSize n:ℝ)^2
  have hr : (0:ℝ)<cliqueSize (baseRate p) n := by exact_mod_cast (show 0<cliqueSize (baseRate p) n by omega)
  have hB : 0<B := by unfold B overlapConstant; positivity
  have hb : (∑l∈Icc 2 (cliqueSize (baseRate p) n),
      overlapTerm (cliqueSize (baseRate p) n) (baseRate p)
        (subsetSize n-cliqueSize (baseRate p) n:ℕ) l) ≤ B := by
    simpa only [Nat.cast_sub hov.2.1.le] using hov.2.2
  have hh := all_subset_failure n p (baseRate p) hp ha.le (baseRate_exp hp1)
    (subsetSize n) (cliqueSize (baseRate p) n) (by omega) hov.2.1 B hB hb
  have hmP := gnpProb_mono n p hp (P := fun G => ¬(G.chromaticNumber.toNat:ℝ) ≤
      (n:ℝ)/(s0 p n:ℝ)*(1+3*Real.log (Real.log (n:ℝ))/Real.log (n:ℝ)))
    (Q := fun G => ¬∀T : Finset (Fin n),T.card=subsetSize n →
      ∃C⊆T,C.card=cliqueSize (baseRate p) n ∧ G.IsIndepSet (C:Set (Fin n))) (by
      intro G hbad hsets
      apply hbad
      have hg := greedy_chromatic_bound G _ _ (by omega) hsets
      simp only [Fintype.card_fin] at hg
      simpa only [loglogN, logN] using hg.trans hup)
  refine hmP.trans (hh.trans_eq ?_)
  congr 2
  unfold B
  field_simp

 theorem lower_almostEvery {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    AlmostEvery p (fun n G => (n:ℝ)/(s0 p n:ℝ) ≤ (G.chromaticNumber.toNat:ℝ)) := by
  have hp : 0≤p ∧ p≤1 := ⟨hp0.le,hp1.le⟩
  apply almostEvery_of_failure p hp _ _ (firstMoment_exp_tendsto hp0 hp1)
  filter_upwards [(s0_atTop hp0 hp1).eventually (eventually_gt_atTop 0),
    eventually_ge_atTop (1:ℕ)] with n hs hn
  have hsZ : 0 < s0 p n := by exact_mod_cast hs
  have hsN : 0 < (s0 p n).toNat := by omega
  have he : ((s0 p n).toNat:ℝ)=(s0 p n:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hsZ.le
  have hm := gnpProb_mono n p hp (P := fun G => ¬(n:ℝ)/(s0 p n:ℝ) ≤ (G.chromaticNumber.toNat:ℝ))
    (Q := fun G => ∃C : Finset (Fin n),C.card=lowerSize p n ∧ G.IsIndepSet (C:Set (Fin n))) (by
      intro G hbad
      by_contra hh
      apply hbad
      have hno : ∀C : Finset (Fin n), C.card=(s0 p n).toNat+1 → ¬G.IsIndepSet (C:Set (Fin n)) := by
        intro C hC hI
        exact hh ⟨C,hC,hI⟩
      have hb := chromatic_lower_of_indep_bound G _ hsN
        (fun C hC => indep_card_le_of_no_set G _ hno C hC)
      simpa only [Fintype.card_fin,he] using hb)
  refine hm.trans ((independent_first_moment n p hp (lowerSize p n)).trans ?_)
  unfold expCliques
  rw [baseRate_exp hp1]
  have h := first_moment_bound n (lowerSize p n) hn (by unfold lowerSize; omega) (baseRate p)
  simpa only [firstMomentBracket,logN] using h

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.NativeBounds

-- BEGIN MODULE BCProof.NativeConclusion

namespace BollobasChromatic.Main.BCFresh

open Filter Topology Asymptotics

theorem native_theorem_4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    AlmostEvery p (fun n G =>
      (n : ℝ) / (s0 p n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) ∧
        (G.chromaticNumber.toNat : ℝ) ≤
          (n : ℝ) / (s0 p n : ℝ) * (1 + 3 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))) := by
  exact almostEvery_and p ⟨hp0.le,hp1.le⟩ _ _
    (lower_almostEvery hp0 hp1) (upper_almostEvery hp0 hp1)

end BollobasChromatic.Main.BCFresh
-- END MODULE BCProof.NativeConclusion

-- BEGIN MODULE Canonical

namespace BollobasChromatic.Main

open Filter Topology Asymptotics

theorem theorem_4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    AlmostEvery p (fun n G =>
      (n : ℝ) / (s0 p n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) ∧
        (G.chromaticNumber.toNat : ℝ) ≤
          (n : ℝ) / (s0 p n : ℝ) * (1 + 3 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))) := by
  exact BCFresh.native_theorem_4 p hp0 hp1

end BollobasChromatic.Main
-- END MODULE Canonical

open Filter Topology Asymptotics BollobasChromatic.Main

theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    AlmostEvery p (fun n G =>
      (n : ℝ) / (s0 p n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) ∧
        (G.chromaticNumber.toNat : ℝ) ≤
          (n : ℝ) / (s0 p n : ℝ) * (1 + 3 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))) := by
  exact BollobasChromatic.Main.theorem_4 p hp0 hp1
