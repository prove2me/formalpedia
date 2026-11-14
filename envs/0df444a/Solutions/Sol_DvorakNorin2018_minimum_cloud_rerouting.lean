-- Prove2me | solution 1 for DvorakNorin2018.minimum_cloud_rerouting
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T17:52:55.742706+00:00
-- url     : https://prove2.me/submissions/153df15a-204e-49fc-a7fc-95db6c4fb69f

import Definitions.Def_DvorakNorin2018_CloudNormalization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.TameCloud

inductive FlowWalk {V : Type} (p : Data V) (x : V) : V → ℕ → Prop
  | nil : FlowWalk p x x 0
  | step {u v : V} {n : ℕ} : FlowWalk p x u n → 0 < p.2 (u,v) → FlowWalk p x v (n+1)

noncomputable def edgeUnit {V : Type} [DecidableEq V] (u v : V) (a : V × V) : ℝ :=
  if a = (u,v) then 1 else 0
lemma edgeUnit_total {V : Type} [Fintype V] [DecidableEq V] (u v : V) :
    (∑ a, edgeUnit u v a) = 1 := by simp [edgeUnit]
lemma edgeUnit_in {V : Type} [Fintype V] [DecidableEq V] (u v k : V) :
    (∑ x, edgeUnit u v (x,k)) = if k = v then 1 else 0 := by
  by_cases hk : k = v
  · subst k; simp [edgeUnit]
  · simp [edgeUnit,hk,Ne.symm hk]
lemma edgeUnit_out {V : Type} [Fintype V] [DecidableEq V] (u v k : V) :
    (∑ x, edgeUnit u v (k,x)) = if k = u then 1 else 0 := by
  by_cases hk : k = u
  · subst k; simp [edgeUnit]
  · simp [edgeUnit,hk]

/- Counts arc traversals without requiring the walk to be simple. -/
theorem FlowWalk.usage {V : Type} [Fintype V] [DecidableEq V] {p : Data V}
    {x y : V} {n : ℕ} (h : FlowWalk p x y n) :
    ∃ e : V × V → ℝ, (∀ a, 0 ≤ e a) ∧
      (∀ a, 0 < e a → 0 < p.2 a) ∧ (∑ a, e a) = n ∧
      (∀ k, (∑ u, e (u,k)) - (∑ u, e (k,u)) =
        (if k = y then 1 else 0) - (if k = x then 1 else 0)) ∧
      (0 < n → 1 ≤ ∑ u, e (u,y)) := by
  induction h with
  | nil => exact ⟨fun _ => 0,fun _ => le_rfl,fun _ h => False.elim ((lt_irrefl 0) h),by simp,
      fun _ => by simp,by simp⟩
  | @step u v n h huv ih =>
    obtain ⟨e,hn,hp,ht,hbal,_⟩ := ih
    refine ⟨fun a => e a + edgeUnit u v a,?_,?_,?_,?_,?_⟩
    · intro a; exact add_nonneg (hn a) (by unfold edgeUnit; split_ifs <;> norm_num)
    · intro a ha
      by_cases he : a = (u,v)
      · exact he.symm ▸ huv
      · apply hp a; simpa [edgeUnit,he] using ha
    · rw [Finset.sum_add_distrib,ht,edgeUnit_total]; push_cast; rfl
    · intro k
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,edgeUnit_in,edgeUnit_out]
      have hb := hbal k
      split_ifs at hb ⊢ <;> linarith
    · intro _
      rw [Finset.sum_add_distrib,edgeUnit_in,if_pos rfl]
      exact le_add_of_nonneg_left (Finset.sum_nonneg (fun u _ => hn (u,v)))

/- Remove a scaled route and move its starting supply to its endpoint. -/
noncomputable def shorten {V : Type} [DecidableEq V] (p : Data V)
    (e : V × V → ℝ) (x y : V) (δ : ℝ) : Data V :=
  (fun v => p.1 v + δ * ((if v = y then 1 else 0) - (if v = x then 1 else 0)),
    fun a => p.2 a - δ * e a)

lemma shorten_incoming {V : Type} [Fintype V] [DecidableEq V]
    (p : Data V) (e : V × V → ℝ) (x y v : V) (δ : ℝ) :
    incoming (shorten p e x y δ) v = incoming p v - δ * ∑ u, e (u,v) := by
  simp only [incoming,shorten,Finset.sum_sub_distrib,Finset.mul_sum]
lemma shorten_total {V : Type} [Fintype V] [DecidableEq V]
    (p : Data V) (e : V × V → ℝ) (x y : V) (δ : ℝ) : total (shorten p e x y δ) = total p := by
  simp only [total,shorten,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]
  simp
lemma shorten_volume {V : Type} [Fintype V] [DecidableEq V]
    (p : Data V) (e : V × V → ℝ) (x y : V) (δ : ℝ) :
    volume (shorten p e x y δ) = volume p - δ * ∑ a, e a := by
  simp only [volume,shorten,Finset.sum_sub_distrib,Finset.mul_sum]

theorem shorten_cloud {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α : ℝ} {p : Data V} (hp : Cloud G W α p)
    (e : V × V → ℝ) (x y : V) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : ∀ a, 0 ≤ e a) (hsupp : ∀ a, 0 < e a → 0 < p.2 a)
    (hbound : ∀ a, δ * e a ≤ p.2 a)
    (hbal : ∀ k, (∑ u, e (u,k)) - (∑ u, e (k,u)) =
      (if k = y then 1 else 0) - (if k = x then 1 else 0))
    (hend : 1 ≤ ∑ u, e (u,y))
    (hstart : x ≠ y → δ ≤ p.1 x) (hfinish : x ≠ y → δ ≤ 1 - p.1 y) :
    Cloud G W α (shorten p e x y δ) := by
  classical
  have hz : ∀ a, p.2 a = 0 → e a = 0 := by
    intro a ha
    apply le_antisymm _ (he a)
    by_contra hn
    have hh := hsupp a (lt_of_not_ge hn)
    rw [ha] at hh; exact (lt_irrefl 0) hh
  refine ⟨?_,fun a => sub_nonneg.mpr (hbound a),?_,?_,?_,?_⟩
  · intro v
    change 0 ≤ p.1 v + δ * _ ∧ p.1 v + δ * _ ≤ 1
    by_cases hxy : x = y
    · subst y; simp only [sub_self,mul_zero,add_zero]; exact hp.supply v
    · have hx := hstart hxy; have hy := hfinish hxy
      by_cases hvx : v = x
      · subst v
        simp only [if_neg hxy,if_pos rfl,ite_true]
        have hb := hp.supply x
        constructor <;> linarith
      · by_cases hvy : v = y
        · subst v
          simp only [if_pos rfl,if_neg (Ne.symm hxy),ite_true]
          have hb := hp.supply y
          constructor <;> linarith
        · simp only [if_neg hvx,if_neg hvy,sub_self,mul_zero,add_zero]
          exact hp.supply v
  · intro u v hn
    have h := hp.support u v hn
    change p.2 (u,v) - δ * e (u,v) = 0
    rw [h,hz (u,v) h]; ring
  · intro u hu v
    have h := hp.sinks u hu v
    change p.2 (u,v) - δ * e (u,v) = 0
    rw [h,hz (u,v) h]; ring
  · intro v hv
    dsimp [congestion]
    rw [shorten_incoming]
    change p.1 v + δ * _ + (incoming p v - δ * ∑ u, e (u,v)) =
      ∑ u, (p.2 (v,u) - δ * e (v,u))
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    have hc := hp.conserve v hv
    dsimp [congestion] at hc
    have hb := hbal v
    nlinarith
  · intro v
    dsimp [congestion]
    rw [shorten_incoming]
    change p.1 v + δ * _ + (incoming p v - δ * ∑ u, e (u,v)) ≤ α
    have hc := hp.bound v; dsimp [congestion] at hc
    have hn : 0 ≤ ∑ u, e (u,v) := Finset.sum_nonneg (fun u _ => he (u,v))
    by_cases hvy : v = y
    · subst v
      split_ifs <;> nlinarith
    · simp only [if_neg hvy]
      split_ifs <;> nlinarith

lemma positive_lower_bound (T : Finset ℝ) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ T, 0 < y → ρ ≤ y := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1,one_pos,by simp⟩
  | insert y T hy ih =>
    obtain ⟨ρ,hρ,h⟩ := ih
    by_cases hp : 0 < y
    · refine ⟨min ρ y,lt_min hρ hp,?_⟩
      intro z hz hz0
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h z hz hz0)
    · refine ⟨ρ,hρ,?_⟩
      intro z hz hz0
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact False.elim (hp hz0)
      · exact h z hz hz0

/- Any positive-flow walk can be removed by a positive amount if its endpoints
are equal, or if supply can be moved from its start into its unsaturated end. -/
theorem improve_along_walk {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α : ℝ} {p : Data V} (hp : Cloud G W α p)
    {x y : V} {n : ℕ} (walk : FlowWalk p x y n) (hn : 0 < n)
    (hends : x ≠ y → 0 < p.1 x ∧ p.1 y < 1) :
    ∃ q : Data V, Cloud G W α q ∧ total q = total p ∧ volume q < volume p := by
  classical
  obtain ⟨e,he,hsupp,het,hbal,hend⟩ := walk.usage
  let T := Finset.univ.image p.2 ∪ {p.1 x,1-p.1 y}
  obtain ⟨ρ,hρ,hρle⟩ := positive_lower_bound T
  let δ := ρ / ((n : ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hprod : δ * ((n : ℝ)+1) = ρ := by dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
  have hδle : δ ≤ ρ := by have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
  have hbound : ∀ a, δ * e a ≤ p.2 a := by
    intro a
    by_cases hpos : 0 < e a
    · have hemax : e a ≤ (n : ℝ) := by
        rw [← het]; exact Finset.single_le_sum (fun b _ => he b) (Finset.mem_univ a)
      have hpmax := hρle (p.2 a) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))) (hsupp a hpos)
      nlinarith
    · have hz : e a = 0 := le_antisymm (le_of_not_gt hpos) (he a)
      rw [hz,mul_zero]; exact hp.flow a
  have hstart : x ≠ y → δ ≤ p.1 x := by
    intro hxy
    exact hδle.trans (hρle _ (Finset.mem_union_right _ (by simp)) (hends hxy).1)
  have hfinish : x ≠ y → δ ≤ 1-p.1 y := by
    intro hxy
    exact hδle.trans (hρle _ (Finset.mem_union_right _ (by simp)) (by linarith [(hends hxy).2]))
  refine ⟨shorten p e x y δ,shorten_cloud hp e x y δ hδ.le he hsupp hbound hbal
    (hend hn) hstart hfinish,shorten_total p e x y δ,?_⟩
  rw [shorten_volume,het]
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  nlinarith

theorem minimum_no_improving_walk {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α s : ℝ} {p : Data V}
    (hp : IsLexMinimum G W α s p) {x y : V} {n : ℕ}
    (walk : FlowWalk p x y n) (hn : 0 < n)
    (hends : x ≠ y → 0 < p.1 x ∧ p.1 y < 1) : False := by
  obtain ⟨q,hq,ht,hv⟩ := improve_along_walk hp.1 walk hn hends
  have hmin := (hp.2.2 q hq (ht.trans hp.2.1)).1
  exact (not_lt_of_ge hmin) hv

lemma FlowWalk.append {V : Type} {p : Data V} {x y z : V} {n m : ℕ}
    (h : FlowWalk p x y n) (q : FlowWalk p y z m) : FlowWalk p x z (n+m) := by
  induction q with
  | nil => simpa using h
  | step q hpos ih => simpa only [Nat.add_assoc] using FlowWalk.step ih hpos

def PosReach {V : Type} (p : Data V) (x y : V) : Prop := ∃ n, 0 < n ∧ FlowWalk p x y n

/- No positive circulation can occur in a minimum-volume cloud. -/
lemma minimum_posReach_irrefl {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α s : ℝ} {p : Data V}
    (hp : IsLexMinimum G W α s p) (x : V) : ¬ PosReach p x x := by
  rintro ⟨n,hn,hwalk⟩
  exact minimum_no_improving_walk hp hwalk hn (fun h => False.elim (h rfl))

lemma positive_supply_ancestor {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α s : ℝ} {p : Data V}
    (hp : IsLexMinimum G W α s p) :
    ∀ v z, 0 < p.2 (v,z) → ∃ x n, 0 < p.1 x ∧ FlowWalk p x v n := by
  classical
  letI : IsTrans V (PosReach p) := ⟨by
    intro x y z hxy hyz
    obtain ⟨n,hn,hw⟩ := hxy
    obtain ⟨m,hm,hq⟩ := hyz
    exact ⟨n+m,by omega,hw.append hq⟩⟩
  letI : Std.Irrefl (PosReach p) := ⟨minimum_posReach_irrefl hp⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl (PosReach p)
  intro v
  induction v using wf.induction with
  | h v ih =>
    intro z hvz
    by_cases hgv : 0 < p.1 v
    · exact ⟨v,0,hgv,.nil⟩
    · have hz : p.1 v = 0 := le_antisymm (le_of_not_gt hgv) (hp.1.supply v).1
      have hvW : v ∉ W := by
        intro h
        have he := hp.1.sinks v h z
        rw [he] at hvz
        exact (lt_irrefl 0) hvz
      have hout : 0 < ∑ u, p.2 (v,u) := lt_of_lt_of_le hvz
        (Finset.single_le_sum (fun u _ => hp.1.flow (v,u)) (Finset.mem_univ z))
      have hin : 0 < ∑ u, p.2 (u,v) := by
        have hc := hp.1.conserve v hvW
        dsimp [congestion,incoming] at hc
        rw [hz,zero_add] at hc
        exact hc.symm ▸ hout
      obtain ⟨u,_,hu⟩ := (Finset.sum_pos_iff_of_nonneg (fun u _ => hp.1.flow (u,v))).mp hin
      obtain ⟨x,n,hx,hw⟩ := ih u ⟨1,by omega,FlowWalk.step FlowWalk.nil hu⟩ v hu
      exact ⟨x,n+1,hx,FlowWalk.step hw hu⟩

/- Property (i) of tame clouds follows from primary volume minimization. -/
theorem minimum_hungry_no_inflow {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α s : ℝ} {p : Data V}
    (hp : IsLexMinimum G W α s p) : ∀ v, Hungry W p v → ∀ u, p.2 (u,v) = 0 := by
  intro v hv u
  apply le_antisymm _ (hp.1.flow (u,v))
  by_contra hn
  have hpos : 0 < p.2 (u,v) := lt_of_not_ge hn
  obtain ⟨x,n,hx,hw⟩ := positive_supply_ancestor hp u v hpos
  exact minimum_no_improving_walk hp (FlowWalk.step hw hpos) (by omega) (fun _ => ⟨hx,hv.1⟩)

lemma shorten_supply_bounds {V : Type} [DecidableEq V] (p : Data V) (e : V × V → ℝ)
    (x y : V) (hxy : x ≠ y) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ v, 0 ≤ p.1 v ∧ p.1 v ≤ 1) (hx : δ ≤ p.1 x) (hy : δ ≤ 1-p.1 y) :
    ∀ v, 0 ≤ (shorten p e x y δ).1 v ∧ (shorten p e x y δ).1 v ≤ 1 := by
  intro v
  change 0 ≤ p.1 v + δ * _ ∧ p.1 v + δ * _ ≤ 1
  by_cases hvx : v = x
  · subst v; simp only [if_neg hxy,ite_true]
    have hb := hp x; constructor <;> linarith
  · by_cases hvy : v = y
    · subst v; simp only [ite_true,if_neg (Ne.symm hxy)]
      have hb := hp y; constructor <;> linarith
    · simp only [if_neg hvx,if_neg hvy,sub_self,mul_zero,add_zero]
      exact hp v

noncomputable def mergeEdit {V : Type} [DecidableEq V] (u v z : V) : V × V → ℝ :=
  fun a => edgeUnit u z a - edgeUnit v z a
lemma merge_incoming {V : Type} [Fintype V] [DecidableEq V] (u v z k : V) :
    (∑ x, mergeEdit u v z (x,k)) = 0 := by
  simp only [mergeEdit,Finset.sum_sub_distrib,edgeUnit_in,sub_self]
lemma merge_outgoing {V : Type} [Fintype V] [DecidableEq V] (u v z k : V) :
    (∑ x, mergeEdit u v z (k,x)) = (if k = u then 1 else 0) - (if k = v then 1 else 0) := by
  simp only [mergeEdit,Finset.sum_sub_distrib,edgeUnit_out]
lemma merge_volume {V : Type} [Fintype V] [DecidableEq V] (u v z : V) :
    (∑ a, mergeEdit u v z a) = 0 := by
  simp only [mergeEdit,Finset.sum_sub_distrib,edgeUnit_total,sub_self]

/- Merge two hungry predecessors without changing total supply or edge volume. -/
theorem merge_cloud {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α s : ℝ} {p : Data V}
    (hp : IsLexMinimum G W α s p) (hα : 1 ≤ α)
    (u v z : V) (hu : Hungry W p u) (hv : Hungry W p v) (huv : u ≠ v)
    (huz : 0 < p.2 (u,z)) (hvz : 0 < p.2 (v,z))
    (δ : ℝ) (hδ : 0 ≤ δ) (hδf : δ ≤ p.2 (u,z)) (hδg : δ ≤ 1-p.1 v) :
    Cloud G W α (shorten p (mergeEdit u v z) u v δ) ∧
      total (shorten p (mergeEdit u v z) u v δ) = total p ∧
      volume (shorten p (mergeEdit u v z) u v δ) = volume p := by
  classical
  have hno := minimum_hungry_no_inflow hp
  have hiu : incoming p u = 0 := Finset.sum_eq_zero (fun x _ => hno u hu x)
  have hiv : incoming p v = 0 := Finset.sum_eq_zero (fun x _ => hno v hv x)
  have huW : u ∉ W := by
    intro h; have he := hp.1.sinks u h z; rw [he] at huz; exact (lt_irrefl 0) huz
  have hgu : δ ≤ p.1 u := by
    have hc := hp.1.conserve u huW
    dsimp [congestion] at hc
    rw [hiu,add_zero] at hc
    have hle := Finset.single_le_sum (s := Finset.univ)
      (fun x _ => hp.1.flow (u,x)) (Finset.mem_univ z)
    linarith
  have heq : ∀ a, (shorten p (mergeEdit u v z) u v δ).2 a =
      p.2 a - δ * (edgeUnit u z a - edgeUnit v z a) := fun _ => rfl
  have hb : ∀ a, 0 ≤ (shorten p (mergeEdit u v z) u v δ).2 a := by
    intro a; rw [heq]
    by_cases ha : a = (u,z)
    · subst a
      have hpair : (u,z) ≠ (v,z) := fun h => huv (congrArg Prod.fst h)
      simp only [edgeUnit,ite_true,if_neg hpair]; linarith
    · by_cases hb : a = (v,z)
      · subst a; simp [edgeUnit,ha]
        have hn := hp.1.flow (v,z); linarith
      · simp only [edgeUnit,if_neg ha,if_neg hb,sub_self,mul_zero,sub_zero]
        exact hp.1.flow a
  have hsupp : ∀ a, p.2 a = 0 → mergeEdit u v z a = 0 := by
    intro a ha
    have h₁ : a ≠ (u,z) := by intro h; subst a; linarith
    have h₂ : a ≠ (v,z) := by intro h; subst a; linarith
    simp [mergeEdit,edgeUnit,h₁,h₂]
  refine ⟨?_,shorten_total p _ u v δ,?_⟩
  · refine ⟨shorten_supply_bounds p _ u v huv δ hδ hp.1.supply hgu hδg,hb,?_,?_,?_,?_⟩
    · intro a b hn
      change p.2 (a,b) - δ * mergeEdit u v z (a,b) = 0
      rw [hsupp _ (hp.1.support a b hn),hp.1.support a b hn]; ring
    · intro a ha b
      change p.2 (a,b) - δ * mergeEdit u v z (a,b) = 0
      rw [hsupp _ (hp.1.sinks a ha b),hp.1.sinks a ha b]; ring
    · intro k hk
      dsimp [congestion]
      rw [shorten_incoming,merge_incoming]
      change p.1 k + δ * _ + (incoming p k - δ * 0) =
        ∑ x, (p.2 (k,x) - δ * mergeEdit u v z (k,x))
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,merge_outgoing]
      have hc := hp.1.conserve k hk; dsimp [congestion] at hc
      split_ifs <;> nlinarith
    · intro k
      dsimp [congestion]
      rw [shorten_incoming,merge_incoming]
      change p.1 k + δ * _ + (incoming p k - δ * 0) ≤ α
      by_cases hkv : k = v
      · subst k; simp only [ite_true,if_neg (Ne.symm huv),hiv]
        linarith
      · have hc := hp.1.bound k; dsimp [congestion] at hc
        simp only [if_neg hkv,mul_zero,sub_zero]
        split_ifs <;> nlinarith
  · rw [shorten_volume,merge_volume]; ring

/- The secondary objective excludes two hungry predecessors of one vertex. -/
theorem minimum_hungry_predecessor_unique {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α s : ℝ} {p : Data V}
    (hp : IsLexMinimum G W α s p) (hα : 1 ≤ α)
    (u v z : V) (hu : Hungry W p u) (hv : Hungry W p v)
    (huz : 0 < p.2 (u,z)) (hvz : 0 < p.2 (v,z)) : u = v := by
  classical
  by_contra huv
  let δ := min (p.2 (u,z)) (1-p.1 v)
  have hδ : 0 < δ := lt_min huz (by linarith [hv.1])
  have hδf : δ ≤ p.2 (u,z) := min_le_left _ _
  have hδg : δ ≤ 1-p.1 v := min_le_right _ _
  let q := shorten p (mergeEdit u v z) u v δ
  obtain ⟨hq,hqt,hqvol⟩ := merge_cloud hp hα u v z hu hv huv huz hvz δ hδ.le hδf hδg
  have hsupport : (Finset.univ.filter (fun a => q.2 a ≠ 0)) ⊆
      (Finset.univ.filter (fun a => p.2 a ≠ 0)) := by
    intro a ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro hz
    have h₁ : a ≠ (u,z) := by intro h; subst a; linarith
    have h₂ : a ≠ (v,z) := by intro h; subst a; linarith
    have hqz : q.2 a = 0 := by simp [q,shorten,mergeEdit,edgeUnit,h₁,h₂,hz]
    exact (Finset.mem_filter.mp ha).2 hqz
  have hunsat : (Finset.univ.filter (fun w => q.1 w ≠ 1)) ⊆
      (Finset.univ.filter (fun w => p.1 w ≠ 1)) := by
    intro w hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro hsat
    have hwu : w ≠ u := by intro h; subst w; linarith [hu.1]
    have hwv : w ≠ v := by intro h; subst w; linarith [hv.1]
    have heq : q.1 w = 1 := by simp [q,shorten,hwu,hwv,hsat]
    exact (Finset.mem_filter.mp hw).2 heq
  have hsc := Finset.card_le_card hsupport
  have huc := Finset.card_le_card hunsat
  have hpen : penalty p ≤ penalty q := (hp.2.2 q hq (hqt.trans hp.2.1)).2 hqvol
  change (Finset.univ.filter (fun a => p.2 a ≠ 0)).card +
      (Finset.univ.filter (fun w => p.1 w ≠ 1)).card ≤
      (Finset.univ.filter (fun a => q.2 a ≠ 0)).card +
      (Finset.univ.filter (fun w => q.1 w ≠ 1)).card at hpen
  by_cases hcase : δ = p.2 (u,z)
  · have hzero : q.2 (u,z) = 0 := by
      have hpair : (u,z) ≠ (v,z) := fun h => huv (congrArg Prod.fst h)
      simp [q,shorten,mergeEdit,edgeUnit,hpair,hcase]
    have hstrict : (Finset.univ.filter (fun a => q.2 a ≠ 0)) ⊂
        (Finset.univ.filter (fun a => p.2 a ≠ 0)) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsupport,?_⟩
      intro heq
      have hmem : (u,z) ∈ Finset.univ.filter (fun a => p.2 a ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne_of_gt huz⟩
      rw [← heq] at hmem
      exact (Finset.mem_filter.mp hmem).2 hzero
    have hc := Finset.card_lt_card hstrict
    omega
  · have hright : δ = 1-p.1 v := by
      dsimp [δ] at hcase ⊢
      exact min_eq_right (le_of_not_ge (fun h => hcase (min_eq_left h)))
    have hsat : q.1 v = 1 := by
      simp only [q,shorten,ite_true,if_neg (Ne.symm huv)]
      rw [hright]; ring
    have hstrict : (Finset.univ.filter (fun w => q.1 w ≠ 1)) ⊂
        (Finset.univ.filter (fun w => p.1 w ≠ 1)) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hunsat,?_⟩
      intro heq
      have hmem : v ∈ Finset.univ.filter (fun w => p.1 w ≠ 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne_of_lt hv.1⟩
      rw [← heq] at hmem
      exact (Finset.mem_filter.mp hmem).2 hsat
    have hc := Finset.card_lt_card hstrict
    omega

theorem minimum_rerouting {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 1 < α)
    (p : Data V) (hp : IsLexMinimum G W α s p) : ReroutingConclusion W p := by
  refine ⟨minimum_hungry_no_inflow hp,?_⟩
  intro z _ u v hu hv huz hvz
  exact minimum_hungry_predecessor_unique hp hα.le u v z hu hv huz hvz
end StableMSR.Recovery.TameCloud

open StableMSR.Recovery.TameCloud
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 1 < α)
    (p : Data V) (hp : IsLexMinimum G W α s p) : ReroutingConclusion W p := by
  exact minimum_rerouting G W α s hα p hp
