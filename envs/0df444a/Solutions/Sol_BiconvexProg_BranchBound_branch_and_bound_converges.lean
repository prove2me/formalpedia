-- Prove2me | solution 1 for BiconvexProg.BranchBound.branch_and_bound_converges
-- status  : ACCEPTED   (disprove)
-- author  : @sometik179
-- created : 2026-10-07T04:23:47.605432+00:00
-- url     : https://prove2.me/submissions/9a85a3ad-bb8d-49a7-9939-bbe6067e9ea5

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

set_option autoImplicit false

/- Complete checked body: MultisetCycle -/
section

namespace BiconvexProg.BranchBound.Counterexample

variable {α : Type*}

theorem split_residual [DecidableEq α] (a b : α) (s : Multiset α) (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : s = {a,b} + (s.erase a).erase b := by
  have hb' : b ∈ s.erase a := (Multiset.mem_erase_of_ne hab.symm).mpr hb
  calc
    s = a ::ₘ s.erase a := (Multiset.cons_erase ha).symm
    _ = a ::ₘ b ::ₘ (s.erase a).erase b := by rw [Multiset.cons_erase hb']
    _ = {a,b} + (s.erase a).erase b := by simp

def cycleNodes (a b : α) (r s : Multiset α) (t : ℕ) : Multiset α :=
  if t % 2 = 0 then {a} + (t / 2) • (r+s)
  else {a,b} + r + (t / 2) • (r+s)

def cycleSelect (a b : α) (t : ℕ) : α := if t % 2 = 0 then a else b

@[simp] theorem cycleNodes_even (a b : α) (r s : Multiset α) (k : ℕ) :
    cycleNodes a b r s (2*k) = {a} + k • (r+s) := by simp [cycleNodes]

@[simp] theorem cycleNodes_odd (a b : α) (r s : Multiset α) (k : ℕ) :
    cycleNodes a b r s (2*k+1) = {a,b} + r + k • (r+s) := by
  have hd : (2*k+1)/2=k := by omega
  simp [cycleNodes,hd]

@[simp] theorem cycleSelect_even (a b : α) (k : ℕ) : cycleSelect a b (2*k)=a := by
  simp [cycleSelect]

@[simp] theorem cycleSelect_odd (a b : α) (k : ℕ) : cycleSelect a b (2*k+1)=b := by
  simp [cycleSelect]

@[simp] theorem cycleNodes_zero (a b : α) (r s : Multiset α) : cycleNodes a b r s 0={a} := by
  simp [cycleNodes]

theorem cycleSelect_mem (a b : α) (r s : Multiset α) (t : ℕ) :
    cycleSelect a b t ∈ cycleNodes a b r s t := by
  by_cases ht : t%2=0 <;> simp [cycleSelect,cycleNodes,ht]

theorem cycleNodes_step [DecidableEq α] (a b : α) (r s : Multiset α) (t : ℕ) :
    cycleNodes a b r s (t+1) = (cycleNodes a b r s t).erase (cycleSelect a b t) +
      (if t%2=0 then {a,b}+r else s) := by
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨k,rfl⟩ := ht
    rw [show k+k=2*k by omega]
    simp only [cycleNodes_odd,cycleNodes_even,cycleSelect_even,Nat.mul_mod_right,if_true]
    simp only [Multiset.singleton_add,Multiset.erase_cons_head]
    ac_rfl
  · obtain ⟨k,rfl⟩ := ht
    rw [show 2*k+1+1=2*(k+1) by omega]
    simp only [cycleNodes_even,cycleNodes_odd,cycleSelect_odd]
    have hm : (2*k+1)%2≠0 := by omega
    rw [if_neg hm]
    have he : {a,b}+r+k • (r+s) = {b}+({a}+r+k • (r+s)) := by
      simp only [Multiset.insert_eq_cons,←Multiset.singleton_add]
      ac_rfl
    rw [he]
    simp only [Multiset.singleton_add,Multiset.erase_cons_head,add_nsmul,one_nsmul]
    simp only [←Multiset.singleton_add]
    ac_rfl

theorem mem_cycleNodes (a b : α) (r s : Multiset α) (t : ℕ) {x : α}
    (hx : x ∈ cycleNodes a b r s t) : x=a ∨ x=b ∨ x∈r ∨ x∈s := by
  unfold cycleNodes at hx
  split_ifs at hx
  all_goals simp only [Multiset.mem_add,Multiset.mem_singleton,Multiset.mem_nsmul] at hx
  all_goals aesop

end BiconvexProg.BranchBound.Counterexample

end

/- Complete checked body: CounterexampleData -/
section

set_option autoImplicit false

namespace BiconvexProg.BranchBound.Counterexample

abbrev Point := (Fin 2 → ℝ) × (Fin 2 → ℝ)

def zeroFun : (Fin 2 → ℝ) → ℝ := fun _ => 0

def bigBox : Box 2 := ⟨0,1,0,1⟩

def origin : Point := (0,0)

noncomputable def badPoint : Point := (![0,1/2],![0,1/2])

def faceBox : Box 2 := bigBox.child 0 0 0 0

lemma box_convex {n : ℕ} (B : Box n) : Convex ℝ B.toSet :=
  (convex_Icc B.l B.L).prod (convex_Icc B.m B.M)

lemma subBox_subset {n : ℕ} (B C : Box n) (h : B.IsSubBox C) : B.toSet ⊆ C.toSet := by
  rintro z ⟨⟨hxl,hxu⟩,⟨hyl,hyu⟩⟩
  exact ⟨⟨h.1.trans hxl,hxu.trans h.2.1⟩,⟨h.2.2.1.trans hyl,hyu.trans h.2.2.2⟩⟩

lemma child_isSubBox {n : ℕ} (B : Box n) (I : Fin n)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ B.toSet) (j : Fin 4) :
    (B.child I (z.1 I) (z.2 I) j).IsSubBox B := by
  rcases hz with ⟨⟨hxl,hxu⟩,⟨hyl,hyu⟩⟩
  have hx := hxl I
  have hX := hxu I
  have hy := hyl I
  have hY := hyu I
  fin_cases j <;>
    simp only [Box.child,Box.IsSubBox] <;>
    refine ⟨?_,?_,?_,?_⟩ <;> intro i <;>
    by_cases hi : i=I <;> simp_all

lemma origin_mem : origin ∈ bigBox.toSet := by
  norm_num [origin,bigBox,Box.toSet,Set.mem_Icc,Pi.le_def]

lemma bad_mem_face : badPoint ∈ faceBox.toSet := by
  norm_num [badPoint,faceBox,bigBox,Box.child,Box.toSet,Set.mem_Icc,Pi.le_def,Fin.forall_fin_two]

lemma face_isSubBox_big : faceBox.IsSubBox bigBox := child_isSubBox bigBox 0 origin origin_mem 0

lemma face_sub_big : faceBox.toSet ⊆ bigBox.toSet := subBox_subset _ _ face_isSubBox_big

lemma big_child_sub (j : Fin 4) : (bigBox.child 0 0 0 j).toSet ⊆ bigBox.toSet :=
  subBox_subset _ _ (child_isSubBox bigBox 0 origin origin_mem j)

lemma face_child_sub (j : Fin 4) : (faceBox.child 1 (1/2) (1/2) j).toSet ⊆ bigBox.toSet :=
  (subBox_subset _ _ (child_isSubBox faceBox 1 badPoint bad_mem_face j)).trans face_sub_big

lemma big_ne_face : bigBox ≠ faceBox := by
  intro h
  have hh := congrArg (fun B : Box 2 => B.L 0) h
  norm_num [bigBox,faceBox,Box.child] at hh

lemma big_child_two : bigBox.child 0 0 0 2=bigBox := by
  simp [Box.child,bigBox]

lemma big_mem_split : bigBox ∈ bigBox.split 0 0 0 := by
  simp [Box.split,big_child_two]

lemma face_mem_split : faceBox ∈ bigBox.split 0 0 0 := by
  simp [Box.split,faceBox]

lemma big_bilin_nonneg (z : Point) (hz : z ∈ bigBox.toSet) : 0 ≤ bilin z := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hz.1.1 i) (hz.2.1 i)

lemma problem : IsProblemP Set.univ zeroFun zeroFun bigBox := by
  refine ⟨by decide,?_,?_,?_,?_,?_,?_,isClosed_univ,convex_univ,?_⟩
  · intro i; norm_num [bigBox]
  · intro i; norm_num [bigBox]
  · exact convexOn_const 0 (convex_Icc _ _)
  · exact convexOn_const 0 (convex_Icc _ _)
  · exact continuousOn_const
  · exact continuousOn_const
  · exact ⟨origin,Set.mem_univ _,origin_mem⟩

@[simp] lemma objective_origin : objective zeroFun zeroFun origin=0 := by
  norm_num [objective,zeroFun,bilin,origin]

lemma objective_bad : objective zeroFun zeroFun badPoint=1/4 := by
  norm_num [objective,zeroFun,bilin,badPoint,Fin.sum_univ_two]

lemma bad_not_min : ¬IsMinOn (objective zeroFun zeroFun) (Set.univ ∩ bigBox.toSet) badPoint := by
  intro h
  have hh := h ⟨Set.mem_univ _,origin_mem⟩
  change objective zeroFun zeroFun badPoint ≤ objective zeroFun zeroFun origin at hh
  rw [objective_origin,objective_bad] at hh
  norm_num at hh

end BiconvexProg.BranchBound.Counterexample

end

/- Complete checked body: EnvelopeValues -/
section

set_option autoImplicit false

namespace BiconvexProg.BranchBound.Counterexample

section General
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma envelope_bounds (C : Set E) (hC : Convex ℝ C) (f : E → ℝ)
    (hf : ∀ z ∈ C,0 ≤ f z) (z : E) (hz : z ∈ C) :
    0 ≤ convexEnvelope C f z ∧ convexEnvelope C f z ≤ f z := by
  have hzero : (0:ℝ) ∈ {r : ℝ | ∃ g : E → ℝ, ConvexOn ℝ C g ∧
      (∀ w ∈ C,g w ≤ f w) ∧ r=g z} := ⟨fun _ => 0,convexOn_const 0 hC,hf,rfl⟩
  have hb : BddAbove {r : ℝ | ∃ g : E → ℝ, ConvexOn ℝ C g ∧
      (∀ w ∈ C,g w ≤ f w) ∧ r=g z} := by
    refine ⟨f z,?_⟩
    rintro r ⟨g,_hg,hgf,rfl⟩
    exact hgf z hz
  constructor
  · exact le_csSup hb hzero
  · apply csSup_le ⟨0,hzero⟩
    rintro r ⟨g,_hg,hgf,rfl⟩
    exact hgf z hz

lemma envelope_zero_between (C : Set E) (hC : Convex ℝ C) (f : E → ℝ)
    (hf : ∀ z ∈ C,0 ≤ f z) (z u v : E) (hz : z ∈ C) (hu : u ∈ C) (hv : v ∈ C)
    (hfu : f u=0) (hfv : f v=0) (he : z=(1/2:ℝ)•u+(1/2:ℝ)•v) :
    convexEnvelope C f z=0 := by
  apply le_antisymm _ (envelope_bounds C hC f hf z hz).1
  apply csSup_le
  · exact ⟨0,fun _ => 0,convexOn_const 0 hC,hf,rfl⟩
  · rintro r ⟨g,hg,hgf,rfl⟩
    have hgu := hgf u hu
    have hgv := hgf v hv
    rw [hfu] at hgu
    rw [hfv] at hgv
    have hm := hg.2 hu hv (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
    rw [←he] at hm
    dsimp only [smul_eq_mul] at hm
    linarith
end General

lemma node_nonneg_of_sub (B : Box 2) (hB : B.toSet ⊆ bigBox.toSet)
    (z : Point) (hz : z ∈ B.toSet) : 0 ≤ nodeFun zeroFun zeroFun B z := by
  simpa only [nodeFun,zeroFun,zero_add,add_zero] using
    (envelope_bounds B.toSet (box_convex B) bilin (fun z hz => big_bilin_nonneg z (hB hz)) z hz).1

lemma node_nonneg_of_subBox (B : Box 2) (hB : B.IsSubBox bigBox)
    (z : Point) (hz : z ∈ B.toSet) : 0 ≤ nodeFun zeroFun zeroFun B z :=
  node_nonneg_of_sub B (subBox_subset _ _ hB) z hz

lemma node_big_origin : nodeFun zeroFun zeroFun bigBox origin=0 := by
  have hb := envelope_bounds bigBox.toSet (box_convex bigBox) bilin big_bilin_nonneg origin origin_mem
  norm_num [nodeFun,zeroFun,bilin,origin] at hb ⊢
  exact le_antisymm hb.2 hb.1

lemma node_face_bad : nodeFun zeroFun zeroFun faceBox badPoint=0 := by
  let u : Point := (![0,0],![0,1])
  let v : Point := (![0,1],![0,0])
  have hu : u ∈ faceBox.toSet := by
    norm_num [u,faceBox,bigBox,Box.child,Box.toSet,Set.mem_Icc,Pi.le_def,Fin.forall_fin_two]
  have hv : v ∈ faceBox.toSet := by
    norm_num [v,faceBox,bigBox,Box.child,Box.toSet,Set.mem_Icc,Pi.le_def,Fin.forall_fin_two]
  have hfu : bilin u=0 := by norm_num [u,bilin,Fin.sum_univ_two]
  have hfv : bilin v=0 := by norm_num [v,bilin,Fin.sum_univ_two]
  have he : badPoint=(1/2:ℝ)•u+(1/2:ℝ)•v := by
    ext i <;> fin_cases i <;> norm_num [badPoint,u,v]
  have hh := envelope_zero_between faceBox.toSet (box_convex faceBox) bilin
    (fun z hz => big_bilin_nonneg z (face_sub_big hz)) badPoint u v bad_mem_face hu hv hfu hfv he
  simpa only [nodeFun,zeroFun,zero_add,add_zero] using hh

lemma rect_bilin_nonneg (C : Set (ℝ×ℝ)) (hC : C ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
    (z : ℝ×ℝ) (hz : z ∈ C) : 0 ≤ z.1*z.2 := mul_nonneg (hC hz).1.1 (hC hz).2.1

lemma gap_big_origin (i : Fin 2) : gap bigBox i origin=0 := by
  have hb := envelope_bounds (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
    ((convex_Icc (0:ℝ) 1).prod (convex_Icc (0:ℝ) 1)) (fun z : ℝ×ℝ => z.1*z.2)
    (rect_bilin_nonneg _ (Set.Subset.refl _)) (0,0) (by norm_num)
  have he : convexEnvelope (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
      (fun z : ℝ×ℝ => z.1*z.2) (0,0)=0 := by exact le_antisymm (by simpa only [mul_zero] using hb.2) hb.1
  simp only [gap,bigBox,origin,Box.rect,Pi.zero_apply,Pi.one_apply,zero_mul,he,sub_self]

lemma gap_face_bad_zero : gap faceBox 0 badPoint=0 := by
  have hb := envelope_bounds (Set.Icc (0:ℝ) 0 ×ˢ Set.Icc (0:ℝ) 0)
    ((convex_Icc (0:ℝ) 0).prod (convex_Icc (0:ℝ) 0)) (fun z : ℝ×ℝ => z.1*z.2)
    (fun z hz => mul_nonneg hz.1.1 hz.2.1) (0,0) (by norm_num)
  have he : convexEnvelope (Set.Icc (0:ℝ) 0 ×ˢ Set.Icc (0:ℝ) 0)
      (fun z : ℝ×ℝ => z.1*z.2) (0,0)=0 := by exact le_antisymm (by simpa only [mul_zero] using hb.2) hb.1
  norm_num [gap,faceBox,bigBox,badPoint,Box.child,Box.rect] at he ⊢
  exact he

lemma gap_face_bad_one : gap faceBox 1 badPoint=1/4 := by
  have hh := envelope_zero_between (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
    ((convex_Icc (0:ℝ) 1).prod (convex_Icc (0:ℝ) 1)) (fun z : ℝ×ℝ => z.1*z.2)
    (rect_bilin_nonneg _ (Set.Subset.refl _)) (1/2,1/2) (0,1) (1,0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ext <;> norm_num)
  norm_num [gap,faceBox,bigBox,badPoint,Box.child,Box.rect] at hh ⊢
  exact hh

lemma good_idx_max (i : Fin 2) : gap bigBox i origin ≤ gap bigBox 0 origin := by rw [gap_big_origin,gap_big_origin]

lemma bad_idx_max (i : Fin 2) : gap faceBox i badPoint ≤ gap faceBox 1 badPoint := by
  fin_cases i
  · change gap faceBox 0 badPoint ≤ gap faceBox 1 badPoint
    rw [gap_face_bad_zero,gap_face_bad_one]; norm_num
  · exact le_rfl

end BiconvexProg.BranchBound.Counterexample

end

/- Complete checked body: PeriodicRun -/
section

namespace BiconvexProg.BranchBound.Counterexample

open Filter Topology
open scoped Classical

noncomputable def residue : Multiset (Box 2) :=
  ((bigBox.split 0 0 0).erase bigBox).erase faceBox

noncomputable def badSplit : Multiset (Box 2) := faceBox.split 1 (1/2) (1/2)

noncomputable def periodicNodes (k : ℕ) : Multiset (Box 2) :=
  cycleNodes bigBox faceBox residue badSplit k

def periodicSel (k : ℕ) : Box 2 := cycleSelect bigBox faceBox k

def periodicIndex (k : ℕ) : Fin 2 := if k % 2 = 0 then 0 else 1

noncomputable def periodicPoint (k : ℕ) : Point := if k % 2 = 0 then origin else badPoint

lemma first_split : bigBox.split 0 0 0 = {bigBox,faceBox} + residue :=
  split_residual bigBox faceBox (bigBox.split 0 0 0) big_mem_split face_mem_split big_ne_face

lemma split_member_sub (B : Box 2) (i : Fin 2) (a b : ℝ)
    (h : ∀ j : Fin 4, (B.child i a b j).toSet ⊆ bigBox.toSet)
    {C : Box 2} (hC : C ∈ B.split i a b) : C.toSet ⊆ bigBox.toSet := by
  have hc : C=B.child i a b 0 ∨ C=B.child i a b 1 ∨
      C=B.child i a b 2 ∨ C=B.child i a b 3 := by simpa [Box.split] using hC
  rcases hc with rfl | rfl | rfl | rfl
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3

lemma residue_sub {B : Box 2} (hB : B ∈ residue) : B.toSet ⊆ bigBox.toSet := by
  have hb : B ∈ bigBox.split 0 0 0 :=
    Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hB)
  exact split_member_sub bigBox 0 0 0 big_child_sub hb

lemma periodic_nodes_sub (k : ℕ) {B : Box 2} (hB : B ∈ periodicNodes k) :
    B.toSet ⊆ bigBox.toSet := by
  rcases mem_cycleNodes bigBox faceBox residue badSplit k hB with rfl | rfl | hb | hb
  · exact Set.Subset.refl _
  · exact face_sub_big
  · exact residue_sub hb
  · exact split_member_sub faceBox 1 (1/2) (1/2) face_child_sub hb

theorem periodic_run :
    IsRun Set.univ zeroFun zeroFun bigBox periodicNodes periodicSel periodicIndex periodicPoint := by
  constructor
  · exact cycleNodes_zero _ _ _ _
  · intro k
    exact cycleSelect_mem _ _ _ _ k
  · intro k
    by_cases hk : k%2=0
    · simp [periodicSel,cycleSelect,periodicPoint,hk,origin_mem]
    · simp [periodicSel,cycleSelect,periodicPoint,hk,bad_mem_face]
  · intro k B hB z hz
    have hh := node_nonneg_of_sub B (periodic_nodes_sub k hB) z hz.2
    by_cases hk : k%2=0
    · simpa only [periodicSel,cycleSelect,periodicPoint,if_pos hk,node_big_origin] using hh
    · simpa only [periodicSel,cycleSelect,periodicPoint,if_neg hk,node_face_bad] using hh
  · intro k i
    by_cases hk : k%2=0
    · simpa only [periodicSel,cycleSelect,periodicPoint,periodicIndex,if_pos hk] using good_idx_max i
    · simpa only [periodicSel,cycleSelect,periodicPoint,periodicIndex,if_neg hk] using bad_idx_max i
  · intro k
    have hh := cycleNodes_step bigBox faceBox residue badSplit k
    rw [←first_split] at hh
    by_cases hk : k%2=0
    · simpa only [periodicNodes,periodicSel,cycleSelect,periodicIndex,periodicPoint,
        if_pos hk,origin,Pi.zero_apply] using hh
    · simpa [periodicNodes,periodicSel,cycleSelect,periodicIndex,periodicPoint,
        hk,badPoint,badSplit] using hh

@[simp] theorem periodicPoint_odd (k : ℕ) : periodicPoint (2*k+1)=badPoint := by
  simp [periodicPoint]

theorem bad_cluster : MapClusterPt badPoint atTop periodicPoint := by
  have ht : StrictMono (fun k : ℕ => 2*k+1) := by
    intro a b hab
    change 2*a+1 < 2*b+1
    omega
  have hc : Tendsto (periodicPoint ∘ fun k : ℕ => 2*k+1) atTop (𝓝 badPoint) := by
    simpa only [Function.comp_def,periodicPoint_odd] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => badPoint) atTop (𝓝 badPoint))
  exact MapClusterPt.of_comp ht.tendsto_atTop hc.mapClusterPt

theorem lower_zero (k : ℕ) : bestLower zeroFun zeroFun periodicSel periodicPoint k=0 := by
  by_cases hk : k%2=0
  · simp [bestLower,periodicSel,cycleSelect,periodicPoint,hk,node_big_origin]
  · simp [bestLower,periodicSel,cycleSelect,periodicPoint,hk,node_face_bad]

theorem initial_bounds_equal : bestLower zeroFun zeroFun periodicSel periodicPoint 0 =
    bestUpper zeroFun zeroFun periodicPoint 0 := by
  simp [lower_zero,bestUpper,periodicPoint,objective_origin]

end BiconvexProg.BranchBound.Counterexample

end

/- Complete checked body: BiconvexDisproof -/
section

namespace BiconvexProg.BranchBound.Counterexample

open Filter Topology

/-- The exact infinite-run statement fails after its ignored stopping test is met. -/
theorem full_negation :
    ¬ (∀ {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {f g : (Fin n → ℝ) → ℝ} {Ω : Box n} (_hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (_hrun : IsRun S f g Ω nodes sel idx pt),
    (∀ zbar, MapClusterPt zbar atTop pt →
      zbar ∈ S ∩ Ω.toSet ∧ IsMinOn (objective f g) (S ∩ Ω.toSet) zbar) ∧
    ∃ vstar : ℝ, (∃ z ∈ S ∩ Ω.toSet, objective f g z = vstar) ∧
      (∀ z ∈ S ∩ Ω.toSet, vstar ≤ objective f g z) ∧
      Tendsto (bestLower f g sel pt) atTop (𝓝 vstar) ∧
      Tendsto (bestUpper f g pt) atTop (𝓝 vstar)) := by
  intro h
  have hm := (h problem periodic_run).1 badPoint bad_cluster
  exact bad_not_min hm.2

end BiconvexProg.BranchBound.Counterexample

end

open Filter Topology BiconvexProg.BranchBound

theorem solution :
    ¬ (∀ {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {f g : (Fin n → ℝ) → ℝ} {Ω : Box n} (_hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (_hrun : IsRun S f g Ω nodes sel idx pt),
    (∀ zbar, MapClusterPt zbar atTop pt →
      zbar ∈ S ∩ Ω.toSet ∧ IsMinOn (objective f g) (S ∩ Ω.toSet) zbar) ∧
    ∃ vstar : ℝ, (∃ z ∈ S ∩ Ω.toSet, objective f g z = vstar) ∧
      (∀ z ∈ S ∩ Ω.toSet, vstar ≤ objective f g z) ∧
      Tendsto (bestLower f g sel pt) atTop (𝓝 vstar) ∧
      Tendsto (bestUpper f g pt) atTop (𝓝 vstar)) := by
  exact BiconvexProg.BranchBound.Counterexample.full_negation

#print axioms BiconvexProg.BranchBound.Counterexample.full_negation
#print axioms solution
