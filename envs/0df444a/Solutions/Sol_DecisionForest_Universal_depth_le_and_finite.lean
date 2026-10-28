-- Prove2me | solution 1 for DecisionForest.Universal.depth_le_and_finite
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:52:44.445255+00:00
-- url     : https://prove2.me/submissions/d4e6e4cb-8fb0-4c9e-8a33-e2303dcc2f48

import Definitions.Def_DecisionForest_Universal_Setting
import Init
import Mathlib


section
noncomputable section
namespace Queelius.DecisionForest
open DecisionForest.Universal
open Finset hiding choose
variable {N : ℕ}

theorem fullTreeAux_choose (o : Finset (Fin N) → Option (Fin N)) (ps : List (Fin N))
    (S T : Finset (Fin N)) :
    choose (fullTreeAux o ps S) T = o (S ∪ ps.toFinset.filter (fun p => p ∈ T)) := by
  induction ps generalizing S with
  | nil => simp [fullTreeAux,choose]
  | cons p ps ih =>
    simp only [fullTreeAux,choose]
    split_ifs with hp
    · rw [ih]
      congr 1
      ext x
      by_cases hx : x = p
      · subst x; simp [hp]
      · simp [hx,or_assoc]
    · rw [ih]
      congr 1
      ext x
      by_cases hx : x = p
      · subst x; simp [hp]
      · simp [hx,or_assoc]

theorem fullTreeAux_leaves (o : Finset (Fin N) → Option (Fin N)) (ps : List (Fin N))
    (S : Finset (Fin N)) : numLeaves (fullTreeAux o ps S) = 2 ^ ps.length := by
  induction ps generalizing S with
  | nil => simp [fullTreeAux,numLeaves]
  | cons p ps ih => simp [fullTreeAux,numLeaves,ih,pow_succ,two_mul, mul_comm]

theorem fullTreeAux_depth (o : Finset (Fin N) → Option (Fin N)) (ps : List (Fin N))
    (S : Finset (Fin N)) : depth (fullTreeAux o ps S) = ps.length + 1 := by
  induction ps generalizing S with
  | nil => simp [fullTreeAux,depth]
  | cons p ps ih => simp [fullTreeAux,depth,ih]

theorem fullTreeAux_req3 (o : Finset (Fin N) → Option (Fin N)) (ps : List (Fin N))
    (S A : Finset (Fin N)) (hd : ps.Nodup) (ha : ∀ p ∈ ps, p ∉ A) :
    req3Aux (fullTreeAux o ps S) A := by
  induction ps generalizing S A with
  | nil => trivial
  | cons p ps ih =>
    have hn := List.nodup_cons.mp hd
    have ht : ∀ q ∈ ps, q ∉ insert p A := by
      intro q hq
      simp only [mem_insert,not_or]
      exact ⟨fun h => hn.1 (h ▸ hq), ha q (by simp [hq])⟩
    exact ⟨ha p (by simp),ih (insert p S) (insert p A) hn.2 ht,ih S (insert p A) hn.2 ht⟩

theorem fullTree_choose (o : Finset (Fin N) → Option (Fin N)) (S : Finset (Fin N)) :
    choose (fullTree o) S = o S := by
  rw [fullTree,fullTreeAux_choose]
  congr 1
  ext x
  simp

theorem fullTree_injective : Function.Injective (@fullTree N) := by
  intro o p h
  funext S
  rw [← fullTree_choose o S, h, fullTree_choose]

end Queelius.DecisionForest

namespace DecisionForest.Universal
theorem fullTree_spec (N : ℕ) (o : Finset (Fin N) → Option (Fin N)) :
    (∀ S : Finset (Fin N), choose (fullTree o) S = o S) ∧ numLeaves (fullTree o) = 2 ^ N ∧
      depth (fullTree o) = N + 1 ∧ Req3 (fullTree o) := by
  refine ⟨Queelius.DecisionForest.fullTree_choose o, ?_, ?_, ?_⟩
  · simpa [fullTree] using Queelius.DecisionForest.fullTreeAux_leaves o (List.finRange N) ∅
  · simpa [fullTree] using Queelius.DecisionForest.fullTreeAux_depth o (List.finRange N) ∅
  · exact Queelius.DecisionForest.fullTreeAux_req3 o (List.finRange N) ∅ ∅
      (List.nodup_finRange N) (by simp)
end DecisionForest.Universal

end

section
noncomputable section
namespace Queelius.DecisionForest
open DecisionForest.Universal
open Finset hiding choose
variable {N : ℕ}

theorem weight_nonnegative (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) (o : Finset (Fin N) → Option (Fin N)) : 0 ≤ prodWeight P o := by
  exact Finset.prod_nonneg (fun S _ => hP.1 (o S) S)

theorem weights_sum (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) : ∑ o : Finset (Fin N) → Option (Fin N), prodWeight P o = 1 := by
  unfold prodWeight
  rw [← Fintype.prod_sum (fun (S : Finset (Fin N)) (c : Option (Fin N)) => P c S)]
  simp [hP.2.1]

theorem product_marginal (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) (S : Finset (Fin N)) (o' : Option (Fin N)) :
    ∑ o : Finset (Fin N) → Option (Fin N), prodWeight P o * (if o S = o' then 1 else 0) = P o' S := by
  classical
  let f (T : Finset (Fin N)) (c : Option (Fin N)) :=
    if T = S then (if c = o' then P c T else 0) else P c T
  have ht (o : Finset (Fin N) → Option (Fin N)) :
      (∏ T, f T (o T)) = prodWeight P o * (if o S = o' then 1 else 0) := by
    by_cases ho : o S = o'
    · simp only [ho,if_true,mul_one,prodWeight]
      apply Finset.prod_congr rfl
      intro T hT
      by_cases h : T = S
      · subst T; simp [f,ho]
      · simp [f,h]
    · rw [if_neg ho,mul_zero]
      exact Finset.prod_eq_zero (mem_univ S) (by simp [f,ho])
  simp_rw [← ht]
  rw [← Fintype.prod_sum]
  have hs (T : Finset (Fin N)) : (∑ c, f T c) = if T = S then P o' S else 1 := by
    by_cases h : T = S
    · subst T; simp [f]
    · simp [f,h,hP.2.1]
  simp_rw [hs]
  simp

end Queelius.DecisionForest

namespace DecisionForest.Universal
theorem prodWeight_isDistribution (N : ℕ) (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) :
    (∀ o : Finset (Fin N) → Option (Fin N), 0 ≤ prodWeight P o) ∧
      ∑ o : Finset (Fin N) → Option (Fin N), prodWeight P o = 1 :=
  ⟨Queelius.DecisionForest.weight_nonnegative P hP, Queelius.DecisionForest.weights_sum P hP⟩
end DecisionForest.Universal

end

section
noncomputable section
namespace Queelius.DecisionForest
open DecisionForest.Universal
open Finset hiding choose
variable {N : ℕ}

theorem depth_bound_aux (t : PTree N) (A : Finset (Fin N)) (h : req3Aux t A) :
    depth t + A.card ≤ N + 1 := by
  induction t generalizing A with
  | leaf o =>
    have hc : A.card ≤ N := by simpa using A.card_le_univ
    simp only [depth]
    omega
  | split p l r ihl ihr =>
    have hl := ihl (insert p A) h.2.1
    have hr := ihr (insert p A) h.2.2
    rw [card_insert_of_notMem h.1] at hl hr
    simp only [depth]
    omega

def levelTrees (N : ℕ) : ℕ → Finset (PTree N)
  | 0 => ∅
  | d+1 => by
    classical
    exact (Finset.univ.image PTree.leaf) ∪
      ((Finset.univ : Finset (Fin N)) ×ˢ ((levelTrees N d) ×ˢ (levelTrees N d))).image
        (fun plr => PTree.split plr.1 plr.2.1 plr.2.2)

theorem mem_level_of_depth (t : PTree N) (d : ℕ) (h : depth t ≤ d) : t ∈ levelTrees N d := by
  classical
  induction d generalizing t with
  | zero => cases t <;> simp [depth] at h
  | succ d ih =>
    cases t with
    | leaf o =>
      apply Finset.mem_union.mpr
      left
      exact mem_image.mpr ⟨o,mem_univ o,rfl⟩
    | split p l r =>
      have hl : depth l ≤ d := by simp only [depth] at h; omega
      have hr : depth r ≤ d := by simp only [depth] at h; omega
      apply Finset.mem_union.mpr
      right
      exact mem_image.mpr ⟨(p,(l,r)),by simp [ih l hl,ih r hr],rfl⟩

theorem finite_bounded_trees (N d : ℕ) : {t : PTree N | depth t ≤ d}.Finite := by
  apply (levelTrees N d).finite_toSet.subset
  intro t ht
  exact mem_level_of_depth t d ht

end Queelius.DecisionForest

namespace DecisionForest.Universal
theorem depth_le_and_finite (N : ℕ) :
    (∀ t : PTree N, Req3 t → depth t ≤ N + 1) ∧ {t : PTree N | IsPurchaseTree t}.Finite := by
  have hd (t : PTree N) (h : Req3 t) : depth t ≤ N+1 := by
    simpa using Queelius.DecisionForest.depth_bound_aux t ∅ h
  refine ⟨hd, (Queelius.DecisionForest.finite_bounded_trees N (N+1)).subset ?_⟩
  intro t ht
  exact hd t ht.2
end DecisionForest.Universal

end

section
noncomputable section
namespace Queelius.DecisionForest
open DecisionForest.Universal
open Finset hiding choose
variable {N : ℕ}

theorem fullTreeAux_req2 (o : Finset (Fin N) → Option (Fin N))
    (ho : ∀ S p, o S = some p → p ∈ S) (ps : List (Fin N)) (S : Finset (Fin N)) :
    req2Aux (fullTreeAux o ps S) S := by
  induction ps generalizing S with
  | nil => exact ho S
  | cons p ps ih => exact ⟨ih (insert p S),ih S⟩

theorem req2_choice (t : PTree N) (L S : Finset (Fin N)) (h : req2Aux t L) (hL : L ⊆ S)
    (p : Fin N) (hp : choose t S = some p) : p ∈ S := by
  induction t generalizing L with
  | leaf o => exact hL (h p hp)
  | split q l r ihl ihr =>
    by_cases hq : q ∈ S
    · exact ihl (insert q L) h.1 (insert_subset hq hL) (by simpa [choose,hq] using hp)
    · exact ihr L h.2 hL (by simpa [choose,hq] using hp)

theorem fullTree_req2_iff (o : Finset (Fin N) → Option (Fin N)) :
    Req2 (fullTree o) ↔ ∀ S p, o S = some p → p ∈ S := by
  constructor
  · intro h S p hp
    exact req2_choice (fullTree o) ∅ S h (empty_subset S) p (by simpa [fullTree_choose] using hp)
  · intro h
    exact fullTreeAux_req2 o h (List.finRange N) ∅

end Queelius.DecisionForest

namespace DecisionForest.Universal
theorem prodWeight_eq_zero_of_not_req2 (N : ℕ) (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) (o : Finset (Fin N) → Option (Fin N))
    (h : ¬ Req2 (fullTree o)) : prodWeight P o = 0 := by
  classical
  by_contra hw
  apply h
  apply (Queelius.DecisionForest.fullTree_req2_iff o).mpr
  intro S p hop
  by_contra hp
  apply hw
  exact Finset.prod_eq_zero (Finset.mem_univ S) (by rw [hop,hP.2.2 S p hp])

theorem forest_marginal (N : ℕ) (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) (S : Finset (Fin N)) (o' : Option (Fin N)) :
    ∑ o : Finset (Fin N) → Option (Fin N),
      prodWeight P o * (if choose (fullTree o) S = o' then 1 else 0) = P o' S := by
  simpa only [Queelius.DecisionForest.fullTree_choose] using
    Queelius.DecisionForest.product_marginal P hP S o'
end DecisionForest.Universal

end

section
noncomputable section
namespace Queelius.DecisionForest
open DecisionForest.Universal
open Finset hiding choose
variable {N : ℕ}

def validTuples (N : ℕ) : Finset (Finset (Fin N) → Option (Fin N)) :=
  by classical exact Finset.univ.filter (fun o => Req2 (fullTree o))

def representationForest (N : ℕ) : Finset (PTree N) :=
  by classical exact (validTuples N).image fullTree

def treeWeight (P : Option (Fin N) → Finset (Fin N) → ℝ) (t : PTree N) : ℝ :=
  prodWeight P (fun S => choose t S)

theorem treeWeight_fullTree (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (o : Finset (Fin N) → Option (Fin N)) : treeWeight P (fullTree o) = prodWeight P o := by
  simp [treeWeight,fullTree_choose]

theorem weight_sum_valid (P : Option (Fin N) → Finset (Fin N) → ℝ) (hP : IsChoiceModel P) :
    ∑ o ∈ validTuples N, prodWeight P o = 1 := by
  classical
  calc
    _ = ∑ o : Finset (Fin N) → Option (Fin N), prodWeight P o := by
      apply sum_subset (by intro o h; exact mem_univ o)
      intro o ho hnot
      exact prodWeight_eq_zero_of_not_req2 N P hP o (by simpa [validTuples] using hnot)
    _ = 1 := weights_sum P hP

theorem marginal_sum_valid (P : Option (Fin N) → Finset (Fin N) → ℝ) (hP : IsChoiceModel P)
    (S : Finset (Fin N)) (o' : Option (Fin N)) :
    ∑ o ∈ validTuples N, prodWeight P o * (if choose (fullTree o) S = o' then 1 else 0) = P o' S := by
  classical
  calc
    _ = ∑ o : Finset (Fin N) → Option (Fin N),
        prodWeight P o * (if choose (fullTree o) S = o' then 1 else 0) := by
      apply sum_subset (by intro o h; exact mem_univ o)
      intro o ho hnot
      rw [prodWeight_eq_zero_of_not_req2 N P hP o (by simpa [validTuples] using hnot),zero_mul]
    _ = P o' S := forest_marginal N P hP S o'

theorem representation_supported (N : ℕ) :
    (↑(representationForest N) : Set (PTree N)) ⊆ FSet N (N+1) := by
  classical
  intro t ht
  rcases mem_image.mp ht with ⟨o,ho,rfl⟩
  have h := fullTree_spec N o
  exact ⟨⟨(mem_filter.mp ho).2,h.2.2.2⟩,h.2.2.1.le⟩

theorem representation_weights (P : Option (Fin N) → Finset (Fin N) → ℝ) (hP : IsChoiceModel P) :
    ∑ t ∈ representationForest N, treeWeight P t = 1 := by
  classical
  unfold representationForest
  rw [sum_image]
  · simpa only [treeWeight_fullTree] using weight_sum_valid P hP
  · intro o ho p hp h
    exact fullTree_injective h

theorem representation_probabilities (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) (S : Finset (Fin N)) (o' : Option (Fin N)) :
    forestProb (representationForest N) (treeWeight P) o' S = P o' S := by
  classical
  unfold forestProb representationForest
  rw [sum_image]
  · simpa only [treeWeight_fullTree] using marginal_sum_valid P hP S o'
  · intro o ho p hp h
    exact fullTree_injective h

end Queelius.DecisionForest

namespace DecisionForest.Universal
theorem theorem_1 (N : ℕ) (P : Option (Fin N) → Finset (Fin N) → ℝ) (hP : IsChoiceModel P) :
    ∃ (F : Finset (PTree N)) (lam : PTree N → ℝ),
      (↑F ⊆ FSet N (N + 1)) ∧ (∀ t ∈ F, 0 ≤ lam t) ∧ ∑ t ∈ F, lam t = 1 ∧
      ∀ (S : Finset (Fin N)) (o : Option (Fin N)), P o S = forestProb F lam o S := by
  refine ⟨Queelius.DecisionForest.representationForest N,Queelius.DecisionForest.treeWeight P,
    Queelius.DecisionForest.representation_supported N,?_,
    Queelius.DecisionForest.representation_weights P hP,?_⟩
  · intro t ht
    exact Queelius.DecisionForest.weight_nonnegative P hP _
  · intro S o
    exact (Queelius.DecisionForest.representation_probabilities P hP S o).symm
end DecisionForest.Universal

end

section
noncomputable section
namespace Queelius.DecisionForest.Controls
open DecisionForest.Universal
open Finset hiding choose

def contextChoice (S : Finset (Fin 2)) : Option (Fin 2) :=
  if S = univ then some 0 else none

def contextModel (o : Option (Fin 2)) (S : Finset (Fin 2)) : ℝ :=
  (if o = contextChoice S then 1/2 else 0) + (if o = none then 1/2 else 0)

theorem context_model_valid : IsChoiceModel contextModel := by
  refine ⟨?_,?_,?_⟩
  · intro o S
    unfold contextModel
    split_ifs <;> norm_num
  · intro S
    norm_num [contextModel,Finset.sum_add_distrib]
  · intro S p hp
    by_cases h : S = univ
    · subst S; exact False.elim (hp (mem_univ p))
    · simp [contextModel,contextChoice,h]

theorem context_choice_valid : Req2 (fullTree contextChoice) := by
  apply (fullTree_req2_iff contextChoice).mpr
  intro S p hp
  by_cases h : S = univ
  · subst S; exact mem_univ p
  · simp [contextChoice,h] at hp

theorem context_weight : prodWeight contextModel contextChoice = 1/2 := by
  unfold prodWeight
  rw [Finset.prod_eq_single (univ : Finset (Fin 2))]
  · norm_num [contextModel,contextChoice] <;> decide
  · intro S hS h
    norm_num [contextChoice,h,contextModel]
  · simp

theorem outside_weight : prodWeight contextModel (fun _ => none) = 1/2 := by
  unfold prodWeight
  rw [Finset.prod_eq_single (univ : Finset (Fin 2))]
  · norm_num [contextModel,contextChoice] <;> decide
  · intro S hS h
    norm_num [contextChoice,h,contextModel]
  · simp

theorem context_increase : contextModel (some 0) ({0} : Finset (Fin 2)) = 0 ∧
    contextModel (some 0) univ = 1/2 := by
  have h : ({0} : Finset (Fin 2)) ≠ univ := by decide
  norm_num [contextModel,contextChoice,h] <;> decide

theorem unavailable_tree_zero :
    ¬ Req2 (fullTree (fun _ : Finset (Fin 2) => some 0)) ∧
    prodWeight contextModel (fun _ => some 0) = 0 := by
  have h : ¬ Req2 (fullTree (fun _ : Finset (Fin 2) => some 0)) := by
    intro hh
    have bad := (fullTree_req2_iff _).mp hh ∅ 0 rfl
    simp at bad
  exact ⟨h,prodWeight_eq_zero_of_not_req2 2 contextModel context_model_valid _ h⟩

theorem context_represented :
    forestProb (representationForest 2) (treeWeight contextModel) (some 0) {0} = 0 ∧
    forestProb (representationForest 2) (treeWeight contextModel) (some 0) univ = 1/2 := by
  simpa only [representation_probabilities contextModel context_model_valid] using context_increase

theorem no_products :
    numLeaves (fullTree (fun _ : Finset (Fin 0) => none)) = 1 ∧
    depth (fullTree (fun _ : Finset (Fin 0) => none)) = 1 ∧
    IsPurchaseTree (fullTree (fun _ : Finset (Fin 0) => none)) := by
  simp [fullTree,fullTreeAux,numLeaves,depth,IsPurchaseTree,Req2,Req3,req2Aux,req3Aux]

end Queelius.DecisionForest.Controls

end

section
open DecisionForest.Universal in
theorem submission_primary_solution (N : ℕ) (P : Option (Fin N) → Finset (Fin N) → ℝ) (hP : IsChoiceModel P) :
    ∃ (F : Finset (PTree N)) (lam : PTree N → ℝ),
      (↑F ⊆ FSet N (N + 1)) ∧ (∀ t ∈ F, 0 ≤ lam t) ∧ ∑ t ∈ F, lam t = 1 ∧
      ∀ (S : Finset (Fin N)) (o : Option (Fin N)), P o S = forestProb F lam o S :=
  theorem_1 N P hP

end


theorem solution : (
  ∀ (N : Nat),
    And
      (∀ (t : DecisionForest.Universal.PTree N),
        @DecisionForest.Universal.Req3 N t →
          @LE.le Nat instLENat (@DecisionForest.Universal.depth N t)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) N
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Set.Finite (DecisionForest.Universal.PTree N)
        (@Set.ofPred (DecisionForest.Universal.PTree N) fun (t : DecisionForest.Universal.PTree N) =>
          @DecisionForest.Universal.IsPurchaseTree N t))
) := @DecisionForest.Universal.depth_le_and_finite
