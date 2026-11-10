-- Prove2me | solution 1 for BKAbsorption.component_subuniverse
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-09T16:41:32.787766+00:00
-- url     : https://prove2.me/submissions/51acb5e0-4e6a-4ee2-a7ae-fa22e2284c10

import Definitions.Def_BKAbsorption_defs

/-!
Barto–Kozik, consequence of Claim 3.8: in a smooth digraph `(S, E ∩ S²)` with `E ≤ A²`,
`S ≤ A`, `A` idempotent, the weak component of a vertex of algebraic length `1` is a subuniverse.

Section `C38` (reusable): oriented paths are encoded as words `w : List Bool`
(`true` = forward edge, `false` = backward edge); `img E X w` is the set `X^w` of the paper.
* `chain_img` / `exists_chain` / `mem_img_self` (Prop 3.2, first item): in a smooth digraph every
  vertex is reachable from itself along every word of algebraic length `0`.
* `exists_word_eq_component` (Claim 3.8): one word `w` with `{a}^w` = the weak component of `a`.
* `img_subuniverse`: `X^w` is a subuniverse whenever `X` is (Lemma 2.5, subuniverse half).
-/

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language

namespace BKAbsorption

namespace C38

variable {A : Type w₁}

section words

variable (E : Set (A × A))

/-- One letter: `true` = forward neighbours `X⁺`, `false` = backward neighbours `X⁻`. -/
def step (X : Set A) : Bool → Set A
  | true => {y | ∃ x ∈ X, (x, y) ∈ E}
  | false => {y | ∃ x ∈ X, (y, x) ∈ E}

/-- `X^w`: the image of `X` along the oriented path encoded by the word `w`. -/
def img (X : Set A) (w : List Bool) : Set A := w.foldl (step E) X

/-- Sign of a letter. -/
def sgn : Bool → ℤ
  | true => 1
  | false => -1

/-- Algebraic length of a word. -/
def net : List Bool → ℤ
  | [] => 0
  | b :: w => sgn b + net w

/-- The reversed path. -/
def revw (w : List Bool) : List Bool := (w.map not).reverse

variable {E}

theorem img_append (X : Set A) (u v : List Bool) : img E X (u ++ v) = img E (img E X u) v := by
  simp [img, List.foldl_append]

theorem step_mono {X Y : Set A} (h : X ⊆ Y) (b : Bool) : step E X b ⊆ step E Y b := by
  cases b <;> rintro y ⟨x, hx, hxy⟩ <;> exact ⟨x, h hx, hxy⟩

theorem img_mono {X Y : Set A} (h : X ⊆ Y) (w : List Bool) : img E X w ⊆ img E Y w := by
  induction w generalizing X Y with
  | nil => exact h
  | cons b w ih => exact ih (step_mono h b)

theorem net_append (u v : List Bool) : net (u ++ v) = net u + net v := by
  induction u with
  | nil => simp [net]
  | cons b u ih => simp only [List.cons_append, net, ih]; omega

theorem net_revw (w : List Bool) : net (revw w) = - net w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [revw, List.map_cons, List.reverse_cons] at ih ⊢
    rw [net_append, ih]
    cases b <;> simp [net, sgn]

theorem img_sub {V : Set A} (hEV : E ⊆ V ×ˢ V) {X : Set A} (hX : X ⊆ V) (w : List Bool) :
    img E X w ⊆ V := by
  induction w generalizing X with
  | nil => exact hX
  | cons b w ih =>
    refine ih ?_
    cases b
    · rintro y ⟨x, _, hyx⟩; exact (Set.mem_prod.1 (hEV hyx)).1
    · rintro y ⟨x, _, hxy⟩; exact (Set.mem_prod.1 (hEV hxy)).2

theorem walk_cons_fwd {a b c : A} {z : ℤ} (hab : (a, b) ∈ E) (h : Walk E b c z) :
    Walk E a c (1 + z) := by
  induction h with
  | refl => simpa using Walk.fwd (Walk.refl a) hab
  | fwd _ hbc ih =>
    have e : ∀ z' : ℤ, 1 + (z' + 1) = 1 + z' + 1 := fun _ => by omega
    rw [e]; exact Walk.fwd ih hbc
  | bwd _ hcb ih =>
    have e : ∀ z' : ℤ, 1 + (z' - 1) = 1 + z' - 1 := fun _ => by omega
    rw [e]; exact Walk.bwd ih hcb

theorem walk_cons_bwd {a b c : A} {z : ℤ} (hba : (b, a) ∈ E) (h : Walk E b c z) :
    Walk E a c (-1 + z) := by
  induction h with
  | refl => simpa using Walk.bwd (Walk.refl a) hba
  | fwd _ hbc ih =>
    have e : ∀ z' : ℤ, -1 + (z' + 1) = -1 + z' + 1 := fun _ => by omega
    rw [e]; exact Walk.fwd ih hbc
  | bwd _ hcb ih =>
    have e : ∀ z' : ℤ, -1 + (z' - 1) = -1 + z' - 1 := fun _ => by omega
    rw [e]; exact Walk.bwd ih hcb

/-- Every element of `X^w` is reached from `X` by a walk of algebraic length `net w`. -/
theorem walk_of_img {X : Set A} {x : A} {w : List Bool} (h : x ∈ img E X w) :
    ∃ y ∈ X, Walk E y x (net w) := by
  induction w generalizing X with
  | nil => exact ⟨x, h, Walk.refl x⟩
  | cons b w ih =>
    obtain ⟨y', hy', hw⟩ := ih h
    cases b
    · obtain ⟨y, hy, hyy⟩ := hy'
      exact ⟨y, hy, walk_cons_bwd hyy hw⟩
    · obtain ⟨y, hy, hyy⟩ := hy'
      exact ⟨y, hy, walk_cons_fwd hyy hw⟩

/-- Conversely every walk is realised by a word. -/
theorem img_of_walk {a x : A} {z : ℤ} (h : Walk E a x z) :
    ∃ w, net w = z ∧ x ∈ img E {a} w := by
  induction h with
  | refl => exact ⟨[], rfl, Set.mem_singleton _⟩
  | fwd _ hbc ih =>
    obtain ⟨w, hw, hb⟩ := ih
    refine ⟨w ++ [true], ?_, ?_⟩
    · rw [net_append, hw]; rfl
    · rw [img_append]; exact ⟨_, hb, hbc⟩
  | bwd _ hcb ih =>
    obtain ⟨w, hw, hb⟩ := ih
    refine ⟨w ++ [false], ?_, ?_⟩
    · rw [net_append, hw]; simp [net, sgn]; omega
    · rw [img_append]; exact ⟨_, hb, hcb⟩

/-- Along a bi-infinite directed walk `f`, the vertex at height `j + net w` is reached from
`f j` along the word `w` (Prop 3.2, first item). -/
theorem chain_img (f : ℤ → A) (hf : ∀ i, (f i, f (i + 1)) ∈ E) (w : List Bool) (j : ℤ) :
    f (j + net w) ∈ img E {f j} w := by
  induction w generalizing j with
  | nil => simp [net, img]
  | cons b w ih =>
    cases b
    · have h1 : f (j - 1) ∈ step E {f j} false := ⟨f j, Set.mem_singleton _, by simpa using hf (j - 1)⟩
      have h2 := img_mono (Set.singleton_subset_iff.2 h1) w (ih (j - 1))
      have e : j - 1 + net w = j + net (false :: w) := by simp only [net, sgn]; omega
      rw [← e]; exact h2
    · have h1 : f (j + 1) ∈ step E {f j} true := ⟨f j, Set.mem_singleton _, hf j⟩
      have h2 := img_mono (Set.singleton_subset_iff.2 h1) w (ih (j + 1))
      have e : j + 1 + net w = j + net (true :: w) := by simp only [net, sgn]; omega
      rw [← e]; exact h2

/-- Bi-infinite walk built from a successor map `s` and a predecessor map `p`. -/
def zchain (s p : A → A) (x : A) : ℤ → A
  | Int.ofNat n => s^[n] x
  | Int.negSucc n => p^[n + 1] x

/-- In a smooth digraph every vertex lies on a bi-infinite directed walk. -/
theorem exists_chain {V : Set A}
    (hsm : ∀ x ∈ V, (∃ y ∈ V, (x, y) ∈ E) ∧ ∃ y ∈ V, (y, x) ∈ E) {x : A} (hx : x ∈ V) :
    ∃ f : ℤ → A, f 0 = x ∧ ∀ i, (f i, f (i + 1)) ∈ E := by
  classical
  let s : A → A := fun y => if h : y ∈ V then (hsm y h).1.choose else y
  let p : A → A := fun y => if h : y ∈ V then (hsm y h).2.choose else y
  have hs : ∀ y ∈ V, s y ∈ V ∧ (y, s y) ∈ E := fun y h => by
    simp only [s, dif_pos h]; exact (hsm y h).1.choose_spec
  have hp : ∀ y ∈ V, p y ∈ V ∧ (p y, y) ∈ E := fun y h => by
    simp only [p, dif_pos h]; exact (hsm y h).2.choose_spec
  have hsV : ∀ n, s^[n] x ∈ V := fun n => by
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hs _ ih).1
  have hpV : ∀ n, p^[n] x ∈ V := fun n => by
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hp _ ih).1
  refine ⟨zchain s p x, rfl, ?_⟩
  intro i
  rcases i with n | n
  · have e : Int.ofNat n + 1 = Int.ofNat (n + 1) := rfl
    rw [e]
    show (s^[n] x, s^[n + 1] x) ∈ E
    rw [Function.iterate_succ_apply']; exact (hs _ (hsV n)).2
  · rcases n with _ | m
    · have e : Int.negSucc 0 + 1 = Int.ofNat 0 := rfl
      rw [e]
      show (p^[0 + 1] x, x) ∈ E
      exact (hp x hx).2
    · have e : Int.negSucc (m + 1) + 1 = Int.negSucc m := rfl
      rw [e]
      show (p^[m + 1 + 1] x, p^[m + 1] x) ∈ E
      rw [Function.iterate_succ_apply' p (m + 1)]; exact (hp _ (hpV _)).2

/-- In a smooth digraph, words of algebraic length `0` return to their start. -/
theorem mem_img_self {V : Set A}
    (hsm : ∀ x ∈ V, (∃ y ∈ V, (x, y) ∈ E) ∧ ∃ y ∈ V, (y, x) ∈ E) {x : A} (hx : x ∈ V)
    {w : List Bool} (hw : net w = 0) : x ∈ img E {x} w := by
  obtain ⟨f, hf0, hf⟩ := exists_chain hsm hx
  have h := chain_img f hf w 0
  simpa only [hw, add_zero, hf0] using h

/-- Two words of equal algebraic length covering `F` and `y` merge into one word. -/
theorem combine {V : Set A} (hEV : E ⊆ V ×ˢ V)
    (hsm : ∀ x ∈ V, (∃ y ∈ V, (x, y) ∈ E) ∧ ∃ y ∈ V, (y, x) ∈ E) {a : A} (ha : a ∈ V)
    {F : Set A} {y : A} {U v : List Bool} (hnet : net U = net v) (hF : F ⊆ img E {a} U)
    (hy : y ∈ img E {a} v) : ∃ W, F ⊆ img E {a} W ∧ y ∈ img E {a} W := by
  refine ⟨U ++ (revw U ++ v), ?_, ?_⟩
  · intro x hx
    have hxU := hF hx
    have hxV : x ∈ V := img_sub hEV (Set.singleton_subset_iff.2 ha) U hxU
    rw [img_append]
    refine img_mono (Set.singleton_subset_iff.2 hxU) _ (mem_img_self hsm hxV ?_)
    rw [net_append, net_revw, hnet]; omega
  · rw [← List.append_assoc, img_append]
    refine img_mono (Set.singleton_subset_iff.2 (mem_img_self hsm ha ?_)) _ hy
    rw [net_append, net_revw]; omega

/-- Closed words at `a` of every nonnegative algebraic length, from one of length `1`. -/
theorem pad {a : A} {q : List Bool} (hq : net q = 1) (haq : a ∈ img E {a} q) :
    ∀ n : ℕ, ∃ p, net p = n ∧ a ∈ img E {a} p := by
  intro n
  induction n with
  | zero => exact ⟨[], rfl, Set.mem_singleton _⟩
  | succ n ih =>
    obtain ⟨p, hp, hap⟩ := ih
    refine ⟨p ++ q, ?_, ?_⟩
    · rw [net_append, hp, hq]; push_cast; rfl
    · rw [img_append]; exact img_mono (Set.singleton_subset_iff.2 hap) q haq

theorem pad_int {a : A} {q : List Bool} (hq : net q = 1) (haq : a ∈ img E {a} q) {n : ℤ}
    (hn : 0 ≤ n) : ∃ p, net p = n ∧ a ∈ img E {a} p := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact pad hq haq m

/-- Barto–Kozik Claim 3.8 (word form): in a smooth finite digraph, if `a` has a closed walk of
algebraic length `1`, a single word `w` reaches the whole weak component of `a` from `a`. -/
theorem exists_word_eq_component [Finite A] {V : Set A} (hEV : E ⊆ V ×ˢ V)
    (hsm : ∀ x ∈ V, (∃ y ∈ V, (x, y) ∈ E) ∧ ∃ y ∈ V, (y, x) ∈ E) {a : A} (ha : a ∈ V)
    (hlen : Walk E a a 1) : ∃ w, img E {a} w = {x | ∃ z, Walk E a x z} := by
  classical
  obtain ⟨q, hq, haq⟩ := img_of_walk hlen
  set H : Set A := {x | ∃ z, Walk E a x z}
  have key : ∀ F : Finset A, (↑F : Set A) ⊆ H → ∃ w, (↑F : Set A) ⊆ img E {a} w := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact fun _ => ⟨[], by simp⟩
    | insert y F _ ih =>
      intro hsub
      rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨U, hU⟩ := ih hsub.2
      obtain ⟨z, hz⟩ := hsub.1
      obtain ⟨v, hv, hyv⟩ := img_of_walk hz
      have hcomb : ∃ W, (↑F : Set A) ⊆ img E {a} W ∧ y ∈ img E {a} W := by
        rcases le_total (net U) (net v) with hle | hle
        · obtain ⟨p, hp, hap⟩ := pad_int hq haq (sub_nonneg.2 hle)
          refine combine hEV hsm ha (U := p ++ U) (v := v) ?_ ?_ hyv
          · rw [net_append, hp]; omega
          · intro x hx; rw [img_append]
            exact img_mono (Set.singleton_subset_iff.2 hap) U (hU hx)
        · obtain ⟨p, hp, hap⟩ := pad_int hq haq (sub_nonneg.2 hle)
          refine combine hEV hsm ha (U := U) (v := p ++ v) ?_ hU ?_
          · rw [net_append, hp]; omega
          · rw [img_append]; exact img_mono (Set.singleton_subset_iff.2 hap) v hyv
      obtain ⟨W, hW1, hW2⟩ := hcomb
      exact ⟨W, by rw [Finset.coe_insert]; exact Set.insert_subset hW2 hW1⟩
  obtain ⟨w, hw⟩ := key (Set.toFinite H).toFinset (by simp)
  refine ⟨w, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := walk_of_img hx
    rw [Set.mem_singleton_iff.1 hy] at hyx
    exact ⟨_, hyx⟩
  · intro x hx
    exact hw (by simpa using hx)

end words

section alg

variable {L : FirstOrder.Language.{u₁, v₁}} [L.Structure A]

/-- `X⁺`/`X⁻` along `E ∩ S²` of a subuniverse `X` is a subuniverse (Lemma 2.5, first half). -/
theorem step_subuniverse (E : L.Substructure (A × A)) {S X : Set A} (hS : IsSubuniverse L S)
    (hX : IsSubuniverse L X) (b : Bool) :
    IsSubuniverse L (step ((E : Set (A × A)) ∩ S ×ˢ S) X b) := by
  intro n f x hx
  cases b
  · choose y hyX hy using hx
    have hE' : (Structure.funMap f (fun i => (x i, y i)) : A × A) ∈ E :=
      E.fun_mem f _ (fun i => (hy i).1)
    refine ⟨Structure.funMap f y, hX _ f y hyX, hE', Set.mk_mem_prod ?_ ?_⟩
    · exact hS _ f x (fun i => (Set.mem_prod.1 (hy i).2).1)
    · exact hS _ f y (fun i => (Set.mem_prod.1 (hy i).2).2)
  · choose y hyX hy using hx
    have hE : (Structure.funMap f (fun i => (y i, x i)) : A × A) ∈ E :=
      E.fun_mem f _ (fun i => (hy i).1)
    refine ⟨Structure.funMap f y, hX _ f y hyX, hE, Set.mk_mem_prod ?_ ?_⟩
    · exact hS _ f y (fun i => (Set.mem_prod.1 (hy i).2).1)
    · exact hS _ f x (fun i => (Set.mem_prod.1 (hy i).2).2)

theorem img_subuniverse (E : L.Substructure (A × A)) {S X : Set A} (hS : IsSubuniverse L S)
    (hX : IsSubuniverse L X) (w : List Bool) :
    IsSubuniverse L (img ((E : Set (A × A)) ∩ S ×ˢ S) X w) := by
  induction w generalizing X with
  | nil => exact hX
  | cons b w ih => exact ih (step_subuniverse E hS hX b)

theorem singleton_subuniverse (hid : IsIdempotent L A) (a : A) : IsSubuniverse L {a} := by
  intro n f x hx
  have : x = fun _ => a := funext hx
  subst this
  exact hid n f a

end alg

end C38

end BKAbsorption

open BKAbsorption

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁} [L.Structure A]
    [Finite A] (hid : IsIdempotent L A)
    (E : L.Substructure (A × A)) (S : Set A) (hS : IsSubuniverse L S)
    (hsm : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ E) ∧ ∃ y ∈ S, (y, x) ∈ E)
    (a : A) (ha : a ∈ S) (hlen : Walk ((E : Set (A × A)) ∩ S ×ˢ S) a a 1) :
    IsSubuniverse L {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z} := by
  have hsm' : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ (E : Set (A × A)) ∩ S ×ˢ S) ∧
      ∃ y ∈ S, (y, x) ∈ (E : Set (A × A)) ∩ S ×ˢ S := by
    intro x hx
    obtain ⟨⟨y, hy, hxy⟩, ⟨y', hy', hyx⟩⟩ := hsm x hx
    exact ⟨⟨y, hy, hxy, Set.mk_mem_prod hx hy⟩, ⟨y', hy', hyx, Set.mk_mem_prod hy' hx⟩⟩
  obtain ⟨w, hw⟩ := C38.exists_word_eq_component Set.inter_subset_right hsm' ha hlen
  rw [← hw]
  exact C38.img_subuniverse E hS (C38.singleton_subuniverse hid a) w
