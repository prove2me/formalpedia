-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctions.l_natural_convex_characterizations
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T06:49:25.338246+00:00
-- url     : https://prove2.me/submissions/597feb54-4285-4683-83e2-69a33be59dfb

import Mathlib.Tactic.TFAE
import Definitions.Def_DiscreteConvex_LConvexFunctions_LAPR
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBFNat
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Definitions.Def_DiscreteConvex_LConvexFunctions_DiscreteMidpointConvexity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega
import Definitions.Def_DiscreteConvex_LConvexFunctions_LiftedFunctionL
import Theorems.Thm_DiscreteConvex_LConvexFunctions_lnat_convex_iff_sbf_nat
import Mathlib.Data.Fintype.Option
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ

set_option autoImplicit false

section
open DiscreteConvex.LConvexFunctions
namespace LConvexApproach
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma maximum_gap (p q : V → ℤ) (hne : (SuppPos p q).Nonempty) :
    ∃ M : ℤ, 0 < M ∧ (∀ v, p v-q v ≤ M) ∧
      (∃ v, p v-q v=M) ∧ ∀ v, v ∈ ArgMaxDiff p q ↔ p v-q v=M := by
  classical
  obtain ⟨u,hu⟩ := hne
  have hu' : q u < p u := by simpa [SuppPos] using hu
  obtain ⟨m,_,hm⟩ := Finset.exists_max_image Finset.univ (fun v => p v-q v)
    ⟨u,Finset.mem_univ u⟩
  have hmax (v : V) : p v-q v ≤ p m-q m := hm v (Finset.mem_univ v)
  refine ⟨p m-q m,by have := hmax u; omega,hmax,⟨m,rfl⟩,?_⟩
  intro v
  simp only [ArgMaxDiff,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hv
    exact le_antisymm (hmax v) (hv m)
  · intro he w
    rw [he]
    exact hmax w

theorem sbfNat_implies_approach (g : (V → ℤ) → WithTop ℝ) (hg : SBFNat g) : LAPR g := by
  intro p q hpq
  obtain ⟨M,hM,hmax,_,harg⟩ := maximum_gap p q hpq
  have hsup : (fun v => max (p v-(M-1)) (q v)) =
      (fun v => q v+IndicatorVec (ArgMaxDiff p q) v) := by
    funext v
    by_cases hv : v ∈ ArgMaxDiff p q
    · have he := (harg v).mp hv
      simp [IndicatorVec,hv]
      omega
    · have he : p v-q v ≠ M := fun he => hv ((harg v).mpr he)
      have hl := hmax v
      simp [IndicatorVec,hv]
      omega
  have hinf : (fun v => min (p v) (q v+(M-1))) =
      (fun v => p v-IndicatorVec (ArgMaxDiff p q) v) := by
    funext v
    by_cases hv : v ∈ ArgMaxDiff p q
    · have he := (harg v).mp hv
      simp [IndicatorVec,hv]
      omega
    · have he : p v-q v ≠ M := fun he => hv ((harg v).mpr he)
      have hl := hmax v
      simp [IndicatorVec,hv]
      omega
  simpa only [hsup,hinf,add_comm] using hg p q (M-1) (by omega)

end LConvexApproach
#print axioms LConvexApproach.sbfNat_implies_approach
end

section
open DiscreteConvex.LConvexFunctions
namespace LConvexMidpoint
variable {V : Type*} [Fintype V] [DecidableEq V]

def distance (p q : V → ℤ) : ℕ := ∑ v, (p v-q v).natAbs

lemma distance_comm (p q : V → ℤ) : distance p q = distance q p := by
  apply Finset.sum_congr rfl
  intro v _
  omega

lemma rounded_pair (p q : V → ℤ) (h : ∀ v, p v ≤ q v ∧ q v ≤ p v+1) :
    MidpointFloor p q = p ∧ MidpointCeil p q = q := by
  constructor
  · funext v
    apply Int.floor_eq_iff.mpr
    have h1 : (p v : ℝ) ≤ q v := by exact_mod_cast (h v).1
    have h2 : (q v : ℝ) ≤ p v+1 := by exact_mod_cast (h v).2
    push_cast
    constructor <;> linarith
  · funext v
    apply Int.ceil_eq_iff.mpr
    have h1 : (p v : ℝ) ≤ q v := by exact_mod_cast (h v).1
    have h2 : (q v : ℝ) ≤ p v+1 := by exact_mod_cast (h v).2
    push_cast
    constructor <;> linarith

lemma midpoint_sum_eq (p q r s : V → ℤ) (h : ∀ v, r v+s v=p v+q v) :
    MidpointFloor r s = MidpointFloor p q ∧ MidpointCeil r s = MidpointCeil p q := by
  constructor <;> funext v <;> simp only [MidpointFloor,MidpointCeil,h]

lemma advance_positive (g : (V → ℤ) → WithTop ℝ) (hg : LAPR g)
    (p q : V → ℤ) (hlarge : ∃ v, q v+2 ≤ p v) :
    ∃ r s : V → ℤ, (∀ v, r v+s v=p v+q v) ∧
      g r+g s ≤ g p+g q ∧ distance r s < distance p q := by
  obtain ⟨u,hu⟩ := hlarge
  have hne : (SuppPos p q).Nonempty := ⟨u,by simp [SuppPos]; omega⟩
  obtain ⟨M,_,hmax,⟨m,hm⟩,harg⟩ := LConvexApproach.maximum_gap p q hne
  have hM : 2 ≤ M := by have := hmax u; omega
  let X := ArgMaxDiff p q
  let r : V → ℤ := fun v => p v-IndicatorVec X v
  let s : V → ℤ := fun v => q v+IndicatorVec X v
  have hmX : m ∈ X := (harg m).mpr hm
  have hsame (v : V) : r v+s v=p v+q v := by dsimp [r,s]; omega
  have hle (v : V) : (r v-s v).natAbs ≤ (p v-q v).natAbs := by
    by_cases hv : v ∈ X
    · have he := (harg v).mp hv
      have hr : r v-s v=M-2 := by simp [r,s,IndicatorVec,hv]; omega
      rw [hr,he]
      omega
    · simp [r,s,IndicatorVec,hv]
  refine ⟨r,s,hsame,hg p q hne,?_⟩
  apply Finset.sum_lt_sum
  · intro v _
    exact hle v
  · refine ⟨m,Finset.mem_univ m,?_⟩
    have hr : r m-s m=M-2 := by simp [r,s,IndicatorVec,hmX]; omega
    rw [hr,hm]
    omega

lemma balanced_bound (g : (V → ℤ) → WithTop ℝ) (hg : LAPR g)
    (p q : V → ℤ) (hnear : ∀ v, p v-q v ≤ 1 ∧ q v-p v ≤ 1) :
    g (MidpointCeil p q)+g (MidpointFloor p q) ≤ g p+g q := by
  by_cases hne : (SuppPos p q).Nonempty
  · obtain ⟨M,hM,hmax,⟨m,hm⟩,harg⟩ := LConvexApproach.maximum_gap p q hne
    have hM1 : M=1 := by have := (hnear m).1; omega
    let X := ArgMaxDiff p q
    let r : V → ℤ := fun v => p v-IndicatorVec X v
    let s : V → ℤ := fun v => q v+IndicatorVec X v
    have hordered (v : V) : r v ≤ s v ∧ s v ≤ r v+1 := by
      have hv := hnear v
      by_cases hx : v ∈ X
      · have he := (harg v).mp hx
        simp [r,s,IndicatorVec,hx]
        omega
      · have he : p v-q v ≠ M := fun he => hx ((harg v).mpr he)
        simp [r,s,IndicatorVec,hx]
        omega
    have hsum (v : V) : r v+s v=p v+q v := by dsimp [r,s]; omega
    obtain ⟨hf,hc⟩ := midpoint_sum_eq p q r s hsum
    obtain ⟨hr,hs⟩ := rounded_pair r s hordered
    have he := hg p q hne
    change g r+g s ≤ g p+g q at he
    have hrfinal : r = MidpointFloor p q := hr.symm.trans hf
    have hsfinal : s = MidpointCeil p q := hs.symm.trans hc
    rw [hrfinal,hsfinal] at he
    simpa only [add_comm] using he
  · have hordered (v : V) : p v ≤ q v ∧ q v ≤ p v+1 := by
      have hp : ¬q v < p v := by intro hp; exact hne ⟨v,by simpa [SuppPos] using hp⟩
      have hv := hnear v
      omega
    obtain ⟨hf,hc⟩ := rounded_pair p q hordered
    rw [hf,hc,add_comm]

theorem approach_implies_midpoint (g : (V → ℤ) → WithTop ℝ) (hg : LAPR g) :
    DiscreteMidpointConvexity g := by
  suffices h : ∀ n : ℕ, ∀ p q : V → ℤ, distance p q=n →
      g (MidpointCeil p q)+g (MidpointFloor p q) ≤ g p+g q by
    intro p q
    exact h _ p q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p q hn
    by_cases hnear : ∀ v, p v-q v ≤ 1 ∧ q v-p v ≤ 1
    · exact balanced_bound g hg p q hnear
    have hadv : ∃ r s : V → ℤ, (∀ v, r v+s v=p v+q v) ∧
        g r+g s ≤ g p+g q ∧ distance r s < distance p q := by
      by_cases hp : ∃ v, q v+2 ≤ p v
      · exact advance_positive g hg p q hp
      · have hq : ∃ v, p v+2 ≤ q v := by
          by_contra hq
          push_neg at hp hq
          exact hnear (fun v => by have h1:=hp v; have h2:=hq v; omega)
        obtain ⟨r,s,he,hval,hd⟩ := advance_positive g hg q p hq
        refine ⟨s,r,?_,?_,?_⟩
        · intro v
          simpa only [add_comm] using he v
        · simpa only [add_comm] using hval
        · simpa only [distance_comm] using hd
    obtain ⟨r,s,he,hval,hd⟩ := hadv
    have hi := ih (distance r s) (by omega) r s rfl
    obtain ⟨hf,hc⟩ := midpoint_sum_eq p q r s he
    rw [hf,hc] at hi
    exact hi.trans hval

end LConvexMidpoint
#print axioms LConvexMidpoint.approach_implies_midpoint
end

section
open DiscreteConvex.LConvexFunctions
namespace LDiscreteClipping
variable {V : Type*}

theorem floor_half (n : ℤ) : ⌊(n : ℝ)/2⌋ = n/2 := by
  simpa using Int.floor_div_natCast (n : ℝ) 2

theorem ceil_half (n : ℤ) : ⌈(n : ℝ)/2⌉ = (n+1)/2 := by
  have hh := Int.floor_neg (a := (n : ℝ)/2)
  have hn : ⌊-((n : ℝ)/2)⌋ = (-n)/2 := by
    simpa only [Int.cast_neg, neg_div] using floor_half (-n)
  rw [hn] at hh
  omega

theorem midpointFloor_apply (p q : V → ℤ) (v : V) :
    MidpointFloor p q v = (p v+q v)/2 := floor_half _

theorem midpointCeil_apply (p q : V → ℤ) (v : V) :
    MidpointCeil p q v = (p v+q v+1)/2 := ceil_half _

def clip (d : V → ℤ) (k : ℕ) : V → ℤ := fun v => min (d v) (k : ℤ)

theorem clipping (g : (V → ℤ) → WithTop ℝ) (hg : DiscreteMidpointConvexity g)
    (m : ℕ) (x d : V → ℤ) (hd : ∀ v, 0 ≤ d v ∧ d v ≤ (m : ℤ)) (k : ℕ) :
    g (x+clip d k)+g (x+d-clip d k) ≤ g x+g (x+d) := by
  induction m using Nat.strong_induction_on generalizing x d k with
  | h m ih =>
    by_cases hm : m ≤ 1
    · by_cases hk : k = 0
      · subst k
        have he : clip d 0 = 0 := by
          funext v
          exact min_eq_right (hd v).1
        simp [he]
      · have he : clip d k = d := by
          funext v
          apply min_eq_left
          have hv := hd v
          omega
        simp [he,add_comm]
    by_cases hx : g x = ⊤
    · simp [hx]
    by_cases hy : g (x+d) = ⊤
    · simp [hy]
    let a : V → ℤ := fun w => (d w+1)/2
    let b : V → ℤ := fun w => d w/2
    have hab : a+b=d := by
      funext w
      dsimp [a,b]
      omega
    have hba : b+a=d := by rw [add_comm,hab]
    have ham : (m+1)/2 < m := by omega
    have hbm : m/2 < m := by omega
    have ha (w : V) : 0 ≤ a w ∧ a w ≤ (((m+1)/2 : ℕ) : ℤ) := by
      dsimp [a]
      have hh := hd w
      omega
    have hb (w : V) : 0 ≤ b w ∧ b w ≤ ((m/2 : ℕ) : ℤ) := by
      dsimp [b]
      have hh := hd w
      omega
    let u := clip a ((k+1)/2)
    let v := clip b (k/2)
    have huv : u+v=clip d k := by
      funext w
      dsimp [u,v,clip,a,b]
      have hh := hd w
      omega
    have h1 : g (x+u)+g (x+a-u) ≤ g x+g (x+a) :=
      ih _ ham x a ha ((k+1)/2)
    have e2 : x+b+a=x+d := by rw [add_assoc,hba]
    have h2 : g (x+b+u)+g (x+d-u) ≤ g (x+b)+g (x+d) := by
      simpa only [e2] using ih _ ham (x+b) a ha ((k+1)/2)
    have e3 : x+u+b=x+b+u := by abel
    have h3 : g (x+u+v)+g (x+b+u-v) ≤ g (x+u)+g (x+b+u) := by
      simpa only [e3] using ih _ hbm (x+u) b hb (k/2)
    have e4 : x+a-u+b=x+d-u := by rw [← hab]; abel
    have h4 : g (x+a-u+v)+g (x+d-u-v) ≤ g (x+a-u)+g (x+d-u) := by
      simpa only [e4] using ih _ hbm (x+a-u) b hb (k/2)
    have hhi : MidpointCeil x (x+d)=x+a := by
      funext w
      rw [midpointCeil_apply]
      simp only [Pi.add_apply]
      dsimp [a]
      omega
    have hlo : MidpointFloor x (x+d)=x+b := by
      funext w
      rw [midpointFloor_apply]
      simp only [Pi.add_apply]
      dsimp [b]
      omega
    have hmiddle := hg x (x+d)
    rw [hhi,hlo] at hmiddle
    have hfinite : g (x+a)+g (x+b) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hx,hy⟩) hmiddle
    have hcrosshi : MidpointCeil (x+b+u-v) (x+a-u+v)=x+a := by
      funext w
      rw [midpointCeil_apply]
      simp only [Pi.add_apply,Pi.sub_apply]
      dsimp [a,b]
      omega
    have hcrosslo : MidpointFloor (x+b+u-v) (x+a-u+v)=x+b := by
      funext w
      rw [midpointFloor_apply]
      simp only [Pi.add_apply,Pi.sub_apply]
      dsimp [a,b]
      omega
    have hcross := hg (x+b+u-v) (x+a-u+v)
    rw [hcrosshi,hcrosslo] at hcross
    have hsum : (g (x+u+v)+g (x+d-u-v)) +
        (g (x+b+u-v)+g (x+a-u+v)) ≤ (g x+g (x+d))+(g (x+a)+g (x+b)) := by
      calc
        _ = (g (x+u+v)+g (x+b+u-v))+(g (x+a-u+v)+g (x+d-u-v)) := by ac_rfl
        _ ≤ (g (x+u)+g (x+b+u))+(g (x+a-u)+g (x+d-u)) := add_le_add h3 h4
        _ = (g (x+u)+g (x+a-u))+(g (x+b+u)+g (x+d-u)) := by ac_rfl
        _ ≤ (g x+g (x+a))+(g (x+b)+g (x+d)) := add_le_add h1 h2
        _ = _ := by ac_rfl
    have htotal := (add_le_add (le_refl (g (x+u+v)+g (x+d-u-v))) hcross).trans hsum
    have hfinal := (add_le_add_iff_left_of_ne_top hfinite).mp htotal
    have et1 : x+u+v=x+clip d k := by rw [add_assoc,huv]
    have et2 : x+d-u-v=x+d-clip d k := by rw [← huv]; abel
    simpa only [et1,et2] using hfinal

#print axioms clipping
end LDiscreteClipping
end

section
open DiscreteConvex.LConvexFunctions
namespace LMidpointLift

lemma floor_half (a : ℤ) : ⌊(a : ℝ)/2⌋ = a/2 := by
  simpa using Int.floor_div_natCast (a : ℝ) 2

lemma ceil_half (a : ℤ) : ⌈(a : ℝ)/2⌉ = (a+1)/2 := by
  have hlo : 2*((a+1)/2)-2 < a := by omega
  have hhi : a ≤ 2*((a+1)/2) := by omega
  have hlo' : (2 : ℝ)*(((a+1)/2 : ℤ) : ℝ)-2 < (a : ℝ) := by exact_mod_cast hlo
  have hhi' : (a : ℝ) ≤ (2 : ℝ)*(((a+1)/2 : ℤ) : ℝ) := by exact_mod_cast hhi
  apply Int.ceil_eq_iff.mpr
  constructor <;> linarith

lemma floor_apply {V : Type*} (p q : V → ℤ) (v : V) :
    MidpointFloor p q v = (p v+q v)/2 := floor_half _

lemma ceil_apply {V : Type*} (p q : V → ℤ) (v : V) :
    MidpointCeil p q v = (p v+q v+1)/2 := ceil_half _

theorem lifted_midpoint {V : Type*} (g : (V → ℤ) → WithTop ℝ)
    (hg : DiscreteMidpointConvexity g) : DiscreteMidpointConvexity (LiftedFunctionL g) := by
  intro x y
  let p : V → ℤ := fun v => x (some v)-x none
  let q : V → ℤ := fun v => y (some v)-y none
  change g p+g q ≥ LiftedFunctionL g (MidpointCeil x y)+
    LiftedFunctionL g (MidpointFloor x y)
  by_cases heven : (x none+y none)%2=0
  · have hf : LiftedFunctionL g (MidpointFloor x y) = g (MidpointFloor p q) := by
      apply congrArg g
      funext v
      simp only [LiftedFunctionL,floor_apply]
      dsimp [p,q]
      omega
    have hc : LiftedFunctionL g (MidpointCeil x y) = g (MidpointCeil p q) := by
      apply congrArg g
      funext v
      simp only [LiftedFunctionL,ceil_apply]
      dsimp [p,q]
      omega
    rw [hf,hc]
    exact hg p q
  · have hodd : (x none+y none)%2=1 := by omega
    have hf : LiftedFunctionL g (MidpointFloor x y) = g (MidpointCeil p q) := by
      apply congrArg g
      funext v
      simp only [LiftedFunctionL,floor_apply,ceil_apply]
      dsimp [p,q]
      omega
    have hc : LiftedFunctionL g (MidpointCeil x y) = g (MidpointFloor p q) := by
      apply congrArg g
      funext v
      simp only [LiftedFunctionL,floor_apply,ceil_apply]
      dsimp [p,q]
      omega
    rw [hf,hc]
    simpa only [add_comm] using hg p q

end LMidpointLift
#print axioms LMidpointLift.lifted_midpoint
end

section
open DiscreteConvex.LConvexFunctions
namespace LMidpointConverse
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coordinate_bound (f : V → ℤ) (v : V) :
    f v ≤ ((∑ w, (f w).natAbs : ℕ) : ℤ) := by
  apply Int.le_natAbs.trans
  exact_mod_cast Finset.single_le_sum (fun w (_ : w ∈ Finset.univ) => Nat.zero_le (f w).natAbs)
    (Finset.mem_univ v)

theorem midpoint_shift_implies_sbf (g : (V → ℤ) → WithTop ℝ)
    (hg : DiscreteMidpointConvexity g)
    (hshift : ∀ (q : V → ℤ) (k : ℤ), g (fun v => q v+k)=g q) : SBF g := by
  intro p q
  let k : ℕ := ∑ v, (p v-q v).natAbs
  let d : V → ℤ := fun v => q v+(k : ℤ)-p v
  let m : ℕ := ∑ v, (d v).natAbs
  have hd (v : V) : 0 ≤ d v ∧ d v ≤ (m : ℤ) := by
    constructor
    · have h := coordinate_bound (fun w => p w-q w) v
      change p v-q v ≤ (k : ℤ) at h
      dsimp [d]
      omega
    · exact coordinate_bound d v
  have hh := LDiscreteClipping.clipping g hg m p d hd k
  have he1 : p+LDiscreteClipping.clip d k = fun v => (p ⊓ q) v+(k : ℤ) := by
    funext v
    simp only [Pi.add_apply,Pi.inf_apply,LDiscreteClipping.clip]
    dsimp [d]
    omega
  have he2 : p+d-LDiscreteClipping.clip d k = p ⊔ q := by
    funext v
    simp only [Pi.add_apply,Pi.sub_apply,Pi.sup_apply,LDiscreteClipping.clip]
    dsimp [d]
    omega
  have he3 : p+d = fun v => q v+(k : ℤ) := by
    funext v
    dsimp [d]
    omega
  rw [he1,he2,he3,hshift,hshift] at hh
  simpa only [add_comm] using hh

theorem midpoint_implies_sbfNat (g : (V → ℤ) → WithTop ℝ)
    (hne : (DomZ g).Nonempty) (hg : DiscreteMidpointConvexity g) : SBFNat g := by
  apply (DiscreteConvex.LConvexFunctions.lnat_convex_iff_sbf_nat g hne).mp
  constructor
  · apply midpoint_shift_implies_sbf (LiftedFunctionL g) (LMidpointLift.lifted_midpoint g hg)
    intro q k
    apply congrArg g
    funext v
    dsimp [LiftedFunctionL]
    omega
  · refine ⟨0,?_⟩
    intro q
    simp only [WithTop.coe_zero,add_zero]
    apply congrArg g
    funext v
    simp only [LiftedFunctionL,Pi.add_apply,Pi.one_apply]
    omega

end LMidpointConverse
#print axioms LMidpointConverse.midpoint_shift_implies_sbf
#print axioms LMidpointConverse.midpoint_implies_sbfNat
end

open DiscreteConvex.LConvexFunctions

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) (hg : (DomZ g).Nonempty) :
    [SBFNat g, LAPR g, DiscreteMidpointConvexity g].TFAE := by
  tfae_have 1 → 2 := LConvexApproach.sbfNat_implies_approach g
  tfae_have 2 → 3 := LConvexMidpoint.approach_implies_midpoint g
  tfae_have 3 → 1 := LMidpointConverse.midpoint_implies_sbfNat g hg
  tfae_finish

#print axioms solution
