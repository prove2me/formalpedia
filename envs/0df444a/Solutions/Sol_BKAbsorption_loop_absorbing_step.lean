-- Prove2me | solution 1 for BKAbsorption.loop_absorbing_step
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-09T17:15:59.938041+00:00
-- url     : https://prove2.me/submissions/fe129311-d211-4638-8485-de470d72a2fd

import Definitions.Def_BKAbsorption_defs
import Mathlib.Data.Fintype.Pigeonhole

/-!
Barto–Kozik, Lemma 3.3 + Claims 3.9–3.10 (absorbing step of the Loop Lemma).
Sections: `C38` (word images, Claim 3.8, copied from `component_subuniverse`) and `LAS`
(walk algebra, paths along words, relative Lemma 2.5, Lemma 3.3 smooth part, Claim 3.10 column
trick).

Original C38 header: Barto–Kozik, consequence of Claim 3.8: in a smooth digraph `(S, E ∩ S²)` with `E ≤ A²`,
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

namespace LAS

open C38

variable {A : Type w₁}

section walks

variable {E : Set (A × A)}

theorem walk_trans {a b c : A} {z₁ z₂ : ℤ} (h₁ : Walk E a b z₁) (h₂ : Walk E b c z₂) :
    Walk E a c (z₁ + z₂) := by
  induction h₂ with
  | refl => simpa using h₁
  | fwd _ hbc ih =>
    have e : ∀ z' : ℤ, z₁ + (z' + 1) = z₁ + z' + 1 := fun _ => by omega
    rw [e]; exact Walk.fwd ih hbc
  | bwd _ hcb ih =>
    have e : ∀ z' : ℤ, z₁ + (z' - 1) = z₁ + z' - 1 := fun _ => by omega
    rw [e]; exact Walk.bwd ih hcb

theorem walk_symm {a b : A} {z : ℤ} (h : Walk E a b z) : Walk E b a (-z) := by
  induction h with
  | refl => simpa using Walk.refl (E := E) a
  | fwd _ hbc ih =>
    have e : ∀ z' : ℤ, -(z' + 1) = -1 + -z' := fun _ => by omega
    rw [e]; exact walk_cons_bwd hbc ih
  | bwd _ hcb ih =>
    have e : ∀ z' : ℤ, -(z' - 1) = 1 + -z' := fun _ => by omega
    rw [e]; exact walk_cons_fwd hcb ih

/-- From a closed walk of algebraic length `1` at `a`, closed walks of every length. -/
theorem walk_loop_int {a : A} (h : Walk E a a 1) (m : ℤ) : Walk E a a m := by
  induction m using Int.induction_on with
  | zero => exact Walk.refl a
  | succ m ih => exact walk_trans ih h
  | pred m ih => simpa [sub_eq_add_neg] using walk_trans ih (walk_symm h)

/-- Any two vertices of a weak component containing a closed walk of algebraic length `1`
are joined by a walk of algebraic length `0`. -/
theorem walk_zero {a b c : A} {z₁ z₂ : ℤ} (hlen : Walk E a a 1) (hb : Walk E a b z₁)
    (hc : Walk E a c z₂) : Walk E b c 0 := by
  have h1 : Walk E b a (-z₁) := walk_symm hb
  have h2 := walk_trans (walk_trans h1 (walk_loop_int hlen (z₁ - z₂))) hc
  have e : -z₁ + (z₁ - z₂) + z₂ = 0 := by omega
  rwa [e] at h2

theorem walk_restrict {S : Set A} {a b : A} {z : ℤ} (h : Walk (E ∩ S ×ˢ S) a b z) :
    Walk (E ∩ {x | ∃ z, Walk (E ∩ S ×ˢ S) a x z} ×ˢ {x | ∃ z, Walk (E ∩ S ×ˢ S) a x z}) a b z := by
  induction h with
  | refl => exact Walk.refl _
  | fwd h hbc ih =>
    exact Walk.fwd ih (Set.mem_inter hbc.1 (Set.mk_mem_prod ⟨_, h⟩ ⟨_, Walk.fwd h hbc⟩))
  | bwd h hcb ih =>
    exact Walk.bwd ih (Set.mem_inter hcb.1 (Set.mk_mem_prod ⟨_, Walk.bwd h hcb⟩ ⟨_, h⟩))

/-- The weak component is closed under one step of a word. -/
theorem step_component {a : A} (b : Bool) :
    step E {x | ∃ z, Walk E a x z} b ⊆ {x | ∃ z, Walk E a x z} := by
  cases b
  · rintro y ⟨x, ⟨z, hz⟩, hyx⟩; exact ⟨_, Walk.bwd hz hyx⟩
  · rintro y ⟨x, ⟨z, hz⟩, hxy⟩; exact ⟨_, Walk.fwd hz hxy⟩

theorem img_component {a : A} (w : List Bool) :
    img E {x | ∃ z, Walk E a x z} w ⊆ {x | ∃ z, Walk E a x z} := by
  induction w with
  | nil => exact le_rfl
  | cons b w ih => exact (img_mono (step_component b) w).trans ih

/-- The first prefix of a word along which `X` reaches `H` (Claim 3.9 / "longest initial
segment"). -/
theorem exists_last_prefix {H : Set A} (w : List Bool) :
    ∀ X : Set A, X ≠ H → img E X w = H →
      ∃ u b, img E X u ≠ H ∧ step E (img E X u) b = H := by
  induction w with
  | nil => intro X hX h; exact absurd h hX
  | cons b w ih =>
    intro X hX h
    by_cases hb : step E X b = H
    · exact ⟨[], b, hX, hb⟩
    · obtain ⟨u, b', hu, hu'⟩ := ih (step E X b) hb h
      exact ⟨b :: u, b', hu, hu'⟩

end walks

/-! ### Paths along a word, as vertex sequences -/

section follows

/-- One letter edge. -/
def edge (E : Set (A × A)) : Bool → A → A → Prop
  | true, x, y => (x, y) ∈ E
  | false, x, y => (y, x) ∈ E

/-- `φ` is a homomorphic image of the oriented path `w` (vertices `φ 0, …, φ |w|`). -/
def Follows (E : Set (A × A)) : List Bool → (ℕ → A) → Prop
  | [], _ => True
  | b :: w, φ => edge E b (φ 0) (φ 1) ∧ Follows E w (fun k => φ (k + 1))

variable {E : Set (A × A)}

theorem path_of_img {X : Set A} {x : A} {w : List Bool} (h : x ∈ img E X w) :
    ∃ φ : ℕ → A, φ 0 ∈ X ∧ φ w.length = x ∧ Follows E w φ := by
  induction w generalizing X with
  | nil => exact ⟨fun _ => x, h, rfl, trivial⟩
  | cons b w ih =>
    obtain ⟨φ', h0, hl, hf⟩ := ih h
    obtain ⟨u, hu, hue⟩ : ∃ u ∈ X, edge E b u (φ' 0) := by
      cases b
      · obtain ⟨u, hu, hue⟩ := h0; exact ⟨u, hu, hue⟩
      · obtain ⟨u, hu, hue⟩ := h0; exact ⟨u, hu, hue⟩
    let φ : ℕ → A := fun k => match k with
      | 0 => u
      | k + 1 => φ' k
    exact ⟨φ, hu, hl, hue, hf⟩

theorem walk_of_follows {w : List Bool} {φ : ℕ → A} (h : Follows E w φ) :
    Walk E (φ 0) (φ w.length) (net w) := by
  induction w generalizing φ with
  | nil => exact Walk.refl _
  | cons b w ih =>
    have h2 := ih h.2
    cases b
    · exact walk_cons_bwd h.1 h2
    · exact walk_cons_fwd h.1 h2

theorem follows_mono {E' : Set (A × A)} (hE : E ⊆ E') {w : List Bool} {φ : ℕ → A}
    (h : Follows E w φ) : Follows E' w φ := by
  induction w generalizing φ with
  | nil => trivial
  | cons b w ih =>
    refine ⟨?_, ih h.2⟩
    cases b
    · exact hE h.1
    · exact hE h.1

theorem follows_mem {V : Set A} {w : List Bool} {φ : ℕ → A} (h : Follows (E ∩ V ×ˢ V) w φ)
    (h0 : φ 0 ∈ V) : ∀ k ≤ w.length, φ k ∈ V := by
  induction w generalizing φ with
  | nil => intro k hk; simp at hk; subst hk; exact h0
  | cons b w ih =>
    have h1 : φ 1 ∈ V := by
      cases b
      · exact (Set.mem_prod.1 h.1.2).1
      · exact (Set.mem_prod.1 h.1.2).2
    intro k hk
    rcases k with _ | k
    · exact h0
    · exact ih h.2 h1 k (by simpa using hk)

theorem follows_restrict {V : Set A} {w : List Bool} {φ : ℕ → A} (h : Follows E w φ)
    (hV : ∀ k ≤ w.length, φ k ∈ V) : Follows (E ∩ V ×ˢ V) w φ := by
  induction w generalizing φ with
  | nil => trivial
  | cons b w ih =>
    refine ⟨?_, ih h.2 (fun k hk => hV (k + 1) (by simp; omega))⟩
    have h0 := hV 0 (by simp)
    have h1 := hV 1 (by simp)
    cases b
    · exact ⟨h.1, Set.mk_mem_prod h1 h0⟩
    · exact ⟨h.1, Set.mk_mem_prod h0 h1⟩

end follows

/-! ### Algebra: relative absorption, Lemma 2.5/3.3 relative, Claim 3.10 -/

section alg

variable {L : FirstOrder.Language.{u₁, v₁}} [L.Structure A]

theorem realize_mem {S : Set A} (hS : IsSubuniverse L S) {α : Type*} (t : L.Term α)
    (a : α → A) (ha : ∀ i, a i ∈ S) : t.realize a ∈ S := by
  induction t with
  | var i => exact ha i
  | func f ts ih => exact hS _ f _ ih

theorem realize_const (hid : IsIdempotent L A) {α : Type*} (t : L.Term α) (a : A) :
    t.realize (fun _ => a) = a := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [show (fun i => (ts i).realize fun _ => a) = fun _ => a from funext ih]
    exact hid _ f a

theorem realize_prod {α : Type*} (t : L.Term α) (x : α → A × A) :
    t.realize x = (t.realize (fun i => (x i).1), t.realize (fun i => (x i).2)) := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [show (fun i => (ts i).realize x) = fun i =>
      ((ts i).realize (fun i => (x i).1), (ts i).realize (fun i => (x i).2)) from funext ih]
    rfl

theorem term_edge (E : L.Substructure (A × A)) {α : Type*} (t : L.Term α) (x y : α → A)
    (h : ∀ i, (x i, y i) ∈ E) : (t.realize x, t.realize y) ∈ E := by
  have := realize_mem (S := (E : Set (A × A))) (fun n f v hv => E.fun_mem f v hv) t
    (fun i => (x i, y i)) h
  rwa [realize_prod] at this

/-- `X` absorbs `S` with respect to the term `t` (relative absorption, fixed term). -/
def AbsBy {n : ℕ} (t : L.Term (Fin n)) (S X : Set A) : Prop :=
  ∀ (k : Fin n) (x : Fin n → A), (∀ i, x i ∈ S) → (∀ i, i ≠ k → x i ∈ X) → t.realize x ∈ X

/-- Lemma 2.5 (relative): `X⁺`, `X⁻` along `E ∩ S²` absorb `S` w.r.t. the same term, if `S` is
smooth. -/
theorem step_absBy (E : L.Substructure (A × A)) {S X : Set A}
    (hsm : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ E) ∧ ∃ y ∈ S, (y, x) ∈ E) (hS : IsSubuniverse L S)
    {n : ℕ} {t : L.Term (Fin n)} (hX : AbsBy t S X) (b : Bool) :
    AbsBy t S (step ((E : Set (A × A)) ∩ S ×ˢ S) X b) := by
  intro k x hxS hx
  cases b
  · have : ∀ i, ∃ y, y ∈ S ∧ (i ≠ k → y ∈ X) ∧ (x i, y) ∈ (E : Set (A × A)) := by
      intro i
      by_cases hik : i = k
      · obtain ⟨y, hy, hxy⟩ := (hsm _ (hxS i)).1
        exact ⟨y, hy, fun h => absurd hik h, hxy⟩
      · obtain ⟨y, hyX, hxy⟩ := hx i hik
        exact ⟨y, (Set.mem_prod.1 hxy.2).2, fun _ => hyX, hxy.1⟩
    choose y hyS hyX hxy using this
    exact ⟨t.realize y, hX k y hyS hyX, term_edge E t x y hxy,
      Set.mk_mem_prod (realize_mem hS t x hxS) (realize_mem hS t y hyS)⟩
  · have : ∀ i, ∃ y, y ∈ S ∧ (i ≠ k → y ∈ X) ∧ (y, x i) ∈ (E : Set (A × A)) := by
      intro i
      by_cases hik : i = k
      · obtain ⟨y, hy, hyx⟩ := (hsm _ (hxS i)).2
        exact ⟨y, hy, fun h => absurd hik h, hyx⟩
      · obtain ⟨y, hyX, hyx⟩ := hx i hik
        exact ⟨y, (Set.mem_prod.1 hyx.2).1, fun _ => hyX, hyx.1⟩
    choose y hyS hyX hyx using this
    exact ⟨t.realize y, hX k y hyS hyX, term_edge E t y x hyx,
      Set.mk_mem_prod (realize_mem hS t y hyS) (realize_mem hS t x hxS)⟩

theorem img_absBy (E : L.Substructure (A × A)) {S X : Set A}
    (hsm : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ E) ∧ ∃ y ∈ S, (y, x) ∈ E) (hS : IsSubuniverse L S)
    {n : ℕ} {t : L.Term (Fin n)} (hX : AbsBy t S X) (w : List Bool) :
    AbsBy t S (img ((E : Set (A × A)) ∩ S ×ˢ S) X w) := by
  induction w generalizing X with
  | nil => exact hX
  | cons b w ih => exact ih (step_absBy E hsm hS hX b)

end alg

/-! ### Lemma 3.3: the smooth part -/

section smoothpart

variable {G : Set (A × A)}

/-- `B_{k+1} = B_k ∩ B_k⁺ ∩ B_k⁻`. -/
def spIter (G : Set (A × A)) (X : Set A) : ℕ → Set A
  | 0 => X
  | k + 1 => spIter G X k ∩ step G (spIter G X k) true ∩ step G (spIter G X k) false

theorem spIter_succ_sub (X : Set A) (k : ℕ) : spIter G X (k + 1) ⊆ spIter G X k :=
  fun _ h => h.1.1

theorem spIter_antitone (X : Set A) : Antitone (spIter G X) :=
  antitone_nat_of_succ_le (spIter_succ_sub X)

/-- A smooth subset of `X` survives every iteration. -/
theorem sub_spIter {X Y : Set A} (hYX : Y ⊆ X)
    (hY : ∀ y ∈ Y, (∃ z ∈ Y, (z, y) ∈ G) ∧ ∃ z ∈ Y, (y, z) ∈ G) (k : ℕ) : Y ⊆ spIter G X k := by
  induction k with
  | zero => exact hYX
  | succ k ih =>
    intro y hy
    obtain ⟨⟨z, hz, hzy⟩, ⟨z', hz', hyz⟩⟩ := hY y hy
    exact ⟨⟨ih hy, z, ih hz, hzy⟩, z', ih hz', hyz⟩

theorem spIter_stable [Finite A] (X : Set A) : ∃ K, spIter G X (K + 1) = spIter G X K := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (spIter G X)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨i, Set.Subset.antisymm (spIter_succ_sub X i) ?_⟩
    rw [h]; exact spIter_antitone X (Nat.succ_le_of_lt hlt)
  · refine ⟨j, Set.Subset.antisymm (spIter_succ_sub X j) ?_⟩
    rw [← h]; exact spIter_antitone X (Nat.succ_le_of_lt hlt)

theorem spIter_smooth {X : Set A} {K : ℕ} (hK : spIter G X (K + 1) = spIter G X K) :
    ∀ x ∈ spIter G X K, (∃ y ∈ spIter G X K, (x, y) ∈ G) ∧ ∃ y ∈ spIter G X K, (y, x) ∈ G := by
  intro x hx
  rw [← hK] at hx
  obtain ⟨⟨_, y, hy, hyx⟩, y', hy', hxy⟩ := hx
  exact ⟨⟨y', hy', hxy⟩, y, hy, hyx⟩

/-- Prop 3.2 (third item): if every vertex of the nonempty finite `X` has an `R`-predecessor
in `X`, then `X` contains a nonempty set closed under predecessors and successors (a cycle). -/
theorem exists_cycle [Finite A] (R : A → A → Prop) {X : Set A} (hne : X.Nonempty)
    (hX : ∀ x ∈ X, ∃ y ∈ X, R y x) :
    ∃ Y ⊆ X, Y.Nonempty ∧ ∀ y ∈ Y, (∃ z ∈ Y, R z y) ∧ ∃ z ∈ Y, R y z := by
  classical
  let p : A → A := fun y => if h : y ∈ X then (hX y h).choose else y
  have hp : ∀ y ∈ X, p y ∈ X ∧ R (p y) y := fun y h => by
    simp only [p, dif_pos h]; exact (hX y h).choose_spec
  obtain ⟨x₀, hx₀⟩ := hne
  have hit : ∀ n, p^[n] x₀ ∈ X := fun n => by
    induction n with
    | zero => exact hx₀
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hp _ ih).1
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => p^[n] x₀)
  have per : ∃ i N, 0 < N ∧ p^[N] (p^[i] x₀) = p^[i] x₀ := by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · refine ⟨i, j - i, by omega, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact h.symm
    · refine ⟨j, i - j, by omega, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact h
  obtain ⟨i, N, hN, hper⟩ := per
  set x := p^[i] x₀
  have hxX : ∀ m, p^[m] x ∈ X := fun m => by
    simp only [x]; rw [← Function.iterate_add_apply]; exact hit _
  refine ⟨Set.range (fun m => p^[m] x), ?_, ⟨x, 0, rfl⟩, ?_⟩
  · rintro _ ⟨m, rfl⟩; exact hxX m
  · rintro _ ⟨m, rfl⟩
    refine ⟨⟨p^[m + 1] x, ⟨m + 1, rfl⟩, ?_⟩, ⟨p^[m + N - 1] x, ⟨m + N - 1, rfl⟩, ?_⟩⟩
    · rw [Function.iterate_succ_apply']; exact (hp _ (hxX m)).2
    · have e : p (p^[m + N - 1] x) = p^[m] x := by
        rw [← Function.iterate_succ_apply' p (m + N - 1),
          show (m + N - 1).succ = m + N by omega, Function.iterate_add_apply, hper]
      have := (hp _ (hxX (m + N - 1))).2
      rwa [e] at this

end smoothpart

/-! ### Claim 3.10: the column trick -/

section column

variable {L : FirstOrder.Language.{u₁, v₁}} [L.Structure A]

/-- Applying a term column-wise to paths along the same word gives a path along that word. -/
theorem follows_term (E : L.Substructure (A × A)) {n : ℕ} (t : L.Term (Fin n))
    {w : List Bool} (ρ : Fin n → ℕ → A) (h : ∀ j, Follows (E : Set (A × A)) w (ρ j)) :
    Follows (E : Set (A × A)) w (fun k => t.realize (fun j => ρ j k)) := by
  induction w generalizing ρ with
  | nil => trivial
  | cons b w ih =>
    refine ⟨?_, ih (fun j k => ρ j (k + 1)) (fun j => (h j).2)⟩
    cases b
    · exact term_edge E t _ _ (fun j => (h j).1)
    · exact term_edge E t _ _ (fun j => (h j).1)

/-- Barto–Kozik Claim 3.10 (column trick).  Let `S' ⊆ S` absorb `S` with respect to `t` of
arity `n`, in an idempotent algebra.  If `a', b' ∈ S'` are joined along a word `w` by a path
`h` in `S`, and each of `a'`, `b'` has a closed path along `w` inside `S'`, then `a'` and `b'`
are joined inside `S'` by a walk of algebraic length `n · net w`. -/
theorem column_walk (hid : IsIdempotent L A) (E : L.Substructure (A × A)) {S S' : Set A}
    (hS'S : S' ⊆ S) {n : ℕ} (t : L.Term (Fin n)) (habs : AbsBy t S S') {a' b' : A}
    (w : List Bool) (f g h : ℕ → A)
    (hf : Follows (E : Set (A × A)) w f) (hg : Follows (E : Set (A × A)) w g)
    (hh : Follows (E : Set (A × A)) w h)
    (hf0 : f 0 = a') (hfl : f w.length = a') (hg0 : g 0 = b') (hgl : g w.length = b')
    (hh0 : h 0 = a') (hhl : h w.length = b')
    (hfS : ∀ k ≤ w.length, f k ∈ S') (hgS : ∀ k ≤ w.length, g k ∈ S')
    (hhS : ∀ k ≤ w.length, h k ∈ S) :
    Walk ((E : Set (A × A)) ∩ S' ×ˢ S') a' b' (n * net w) := by
  classical
  let c : ℕ → A := fun i => t.realize (fun j : Fin n => if j.val + i < n then a' else b')
  have step : ∀ i, i < n → Walk ((E : Set (A × A)) ∩ S' ×ˢ S') (c i) (c (i + 1)) (net w) := by
    intro i hi
    let ρ : Fin n → ℕ → A := fun j k =>
      if j.val + i + 1 < n then f k else if j.val + i + 1 = n then h k else g k
    have hρ : ∀ j, Follows (E : Set (A × A)) w (ρ j) := by
      intro j; simp only [ρ]; split_ifs
      · exact hf
      · exact hh
      · exact hg
    have hψ := follows_term E t ρ hρ
    have hmem : ∀ k ≤ w.length, t.realize (fun j => ρ j k) ∈ S' := by
      intro k hk
      refine habs ⟨n - i - 1, by omega⟩ _ ?_ ?_
      · intro j; simp only [ρ]; split_ifs
        · exact hS'S (hfS k hk)
        · exact hhS k hk
        · exact hS'S (hgS k hk)
      · intro j hj
        have hj' : j.val + i + 1 ≠ n := fun e => hj (Fin.ext (by simp; omega))
        simp only [ρ]; split_ifs <;> first | exact hfS k hk | exact hgS k hk | omega
    have hw := walk_of_follows (follows_restrict hψ hmem)
    have e0 : (fun j => ρ j 0) = fun j : Fin n => if j.val + i < n then a' else b' := by
      funext j; simp only [ρ]; split_ifs <;> first | omega | simp_all
    have el : (fun j => ρ j w.length) = fun j : Fin n => if j.val + (i + 1) < n then a' else b' := by
      funext j; simp only [ρ]; split_ifs <;> first | omega | simp_all
    rw [e0, el] at hw
    exact hw
  have chain : ∀ i, i ≤ n → Walk ((E : Set (A × A)) ∩ S' ×ˢ S') (c 0) (c i) (i * net w) := by
    intro i
    induction i with
    | zero => intro _; simpa using Walk.refl (E := (E : Set (A × A)) ∩ S' ×ˢ S') (c 0)
    | succ i ih =>
      intro hi
      have := walk_trans (ih (by omega)) (step i (by omega))
      have e : (i : ℤ) * net w + net w = ((i + 1 : ℕ) : ℤ) * net w := by
        push_cast; rw [add_mul, one_mul]
      rwa [e] at this
  have hc0 : c 0 = a' := by
    simp only [c]
    rw [show (fun j : Fin n => if j.val + 0 < n then a' else b') = fun _ => a' from
      funext fun j => if_pos (by omega)]
    exact realize_const hid t a'
  have hcn : c n = b' := by
    simp only [c]
    rw [show (fun j : Fin n => if j.val + n < n then a' else b') = fun _ => b' from
      funext fun j => if_neg (by omega)]
    exact realize_const hid t b'
  have := chain n le_rfl
  rwa [hc0, hcn] at this

end column

end LAS

end BKAbsorption

open BKAbsorption BKAbsorption.C38 BKAbsorption.LAS

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁} [L.Structure A]
    [Finite A] (hid : IsIdempotent L A)
    (E : L.Substructure (A × A)) (S : Set A) (hS : IsSubuniverse L S)
    (hsm : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ E) ∧ ∃ y ∈ S, (y, x) ∈ E)
    (a : A) (ha : a ∈ S) (hlen : Walk ((E : Set (A × A)) ∩ S ×ˢ S) a a 1)
    (I : Set A) (hIne : I.Nonempty) (hIS : I ≠ S)
    (hIc : ∀ x ∈ I, ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z)
    (hIabs : IsSubuniverse L I ∧ ∃ (n : ℕ) (t : L.Term (Fin n)), 0 < n ∧
      ∀ (k : Fin n) (x : Fin n → A), (∀ i, x i ∈ S) → (∀ i, i ≠ k → x i ∈ I) →
        t.realize x ∈ I) :
    ∃ S' : Set A, S' ⊂ S ∧ S'.Nonempty ∧
      (IsSubuniverse L S' ∧ ∃ (n : ℕ) (t : L.Term (Fin n)), 0 < n ∧
        ∀ (k : Fin n) (x : Fin n → A), (∀ i, x i ∈ S) → (∀ i, i ≠ k → x i ∈ S') →
          t.realize x ∈ S') ∧
      (∀ x ∈ S', (∃ y ∈ S', (x, y) ∈ E) ∧ ∃ y ∈ S', (y, x) ∈ E) ∧
      ∃ b ∈ S', Walk ((E : Set (A × A)) ∩ S' ×ˢ S') b b 1 ∧
        ∀ x ∈ S', ∃ z, Walk ((E : Set (A × A)) ∩ S' ×ˢ S') b x z := by
  classical
  obtain ⟨hIsub, n, t, hn, htabs⟩ := hIabs
  have hsmG : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ (E : Set (A × A)) ∩ S ×ˢ S) ∧
      ∃ y ∈ S, (y, x) ∈ (E : Set (A × A)) ∩ S ×ˢ S := by
    intro x hx
    obtain ⟨⟨y, hy, hxy⟩, ⟨y', hy', hyx⟩⟩ := hsm x hx
    exact ⟨⟨y, hy, hxy, Set.mk_mem_prod hx hy⟩, ⟨y', hy', hyx, Set.mk_mem_prod hy' hx⟩⟩
  have hHS : ∀ x, (∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z) → x ∈ S := by
    rintro x ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ := img_of_walk hz
    exact img_sub Set.inter_subset_right (Set.singleton_subset_iff.2 ha) w hw
  by_cases hIH : I = {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z}
  · -- `I` is the whole component: take `S' = I`.
    subst hIH
    refine ⟨_, Set.ssubset_iff_subset_ne.2 ⟨hHS, hIS⟩, hIne, ⟨hIsub, n, t, hn, htabs⟩, ?_,
      a, ⟨0, Walk.refl a⟩, walk_restrict hlen, fun x ⟨z, hz⟩ => ⟨z, walk_restrict hz⟩⟩
    rintro x ⟨z, hz⟩
    have hx := hHS x ⟨z, hz⟩
    obtain ⟨⟨y, hy, hxy⟩, ⟨y', hy', hyx⟩⟩ := hsm x hx
    exact ⟨⟨y, ⟨_, Walk.fwd hz ⟨hxy, Set.mk_mem_prod hx hy⟩⟩, hxy⟩,
      ⟨y', ⟨_, Walk.bwd hz ⟨hyx, Set.mk_mem_prod hy' hx⟩⟩, hyx⟩⟩
  set G : Set (A × A) := (E : Set (A × A)) ∩ S ×ˢ S with hG
  set H : Set A := {x | ∃ z, Walk G a x z} with hH
  have hIH' : I ⊆ H := hIc
  -- Claim 3.9: `I^w = H` for a single word `w`.
  obtain ⟨i, hiI⟩ := hIne
  obtain ⟨zi, hi⟩ := hIc i hiI
  have hii : Walk G i i 1 := by
    have := walk_trans (walk_trans (walk_symm hi) hlen) hi
    rwa [show -zi + 1 + zi = 1 by omega] at this
  have hHi : {x | ∃ z, Walk G i x z} = H := by
    ext x; constructor
    · rintro ⟨z, hz⟩; exact ⟨_, walk_trans hi hz⟩
    · rintro ⟨z, hz⟩; exact ⟨_, walk_trans (walk_symm hi) hz⟩
  obtain ⟨w, hw⟩ := exists_word_eq_component Set.inter_subset_right hsmG (hHS i ⟨_, hi⟩) hii
  rw [hHi] at hw
  have himg : img G I w = H := by
    refine Set.Subset.antisymm ((img_mono hIH' w).trans (img_component w)) ?_
    rw [← hw]; exact img_mono (Set.singleton_subset_iff.2 hiI) w
  obtain ⟨u, b, hu, hub⟩ := exists_last_prefix w I hIH himg
  set S₁ := img G I u with hS₁
  have hS₁H : S₁ ⊆ H := (img_mono hIH' u).trans (img_component u)
  have hS₁sub : IsSubuniverse L S₁ := img_subuniverse E hS hIsub u
  have hS₁abs : AbsBy t S S₁ := img_absBy E hsm hS htabs u
  have haH : a ∈ H := ⟨0, Walk.refl a⟩
  -- Prop 3.2 (iii): `S₁` contains a cycle.
  have hcyc : ∃ Y ⊆ S₁, Y.Nonempty ∧ ∀ y ∈ Y, (∃ z ∈ Y, (z, y) ∈ G) ∧ ∃ z ∈ Y, (y, z) ∈ G := by
    have hne : S₁.Nonempty := by
      have : a ∈ step G S₁ b := hub ▸ haH
      cases b <;> obtain ⟨x, hx, _⟩ := this <;> exact ⟨x, hx⟩
    cases b
    · have hX : ∀ x ∈ S₁, ∃ y ∈ S₁, (fun y x => (x, y) ∈ G) y x := by
        intro x hx; have : x ∈ step G S₁ false := hub ▸ hS₁H hx; exact this
      obtain ⟨Y, hY, hYne, hYs⟩ := exists_cycle (fun y x => (x, y) ∈ G) hne hX
      exact ⟨Y, hY, hYne, fun y hy => ⟨(hYs y hy).2, (hYs y hy).1⟩⟩
    · have hX : ∀ x ∈ S₁, ∃ y ∈ S₁, (fun y x => (y, x) ∈ G) y x := by
        intro x hx; have : x ∈ step G S₁ true := hub ▸ hS₁H hx; exact this
      exact exists_cycle (fun y x => (y, x) ∈ G) hne hX
  obtain ⟨Y, hYS₁, hYne, hYs⟩ := hcyc
  -- Lemma 3.3: the smooth part of `G|S₁`.
  obtain ⟨K, hK⟩ := spIter_stable (G := G) S₁
  set S' := spIter G S₁ K with hS'
  have hS'S₁ : S' ⊆ S₁ := spIter_antitone S₁ (Nat.zero_le K)
  have hYS' : Y ⊆ S' := sub_spIter hYS₁ hYs K
  have halg : ∀ k, IsSubuniverse L (spIter G S₁ k) ∧ AbsBy t S (spIter G S₁ k) := by
    intro k
    induction k with
    | zero => exact ⟨hS₁sub, hS₁abs⟩
    | succ k ih =>
      have h1 := step_subuniverse E hS ih.1 true
      have h2 := step_subuniverse E hS ih.1 false
      have h3 := step_absBy E hsm hS ih.2 true
      have h4 := step_absBy E hsm hS ih.2 false
      refine ⟨fun m f x hx => ⟨⟨ih.1 m f x (fun j => (hx j).1.1), h1 m f x (fun j => (hx j).1.2)⟩,
        h2 m f x (fun j => (hx j).2)⟩, fun k x hxS hx =>
        ⟨⟨ih.2 k x hxS (fun j hj => (hx j hj).1.1), h3 k x hxS (fun j hj => (hx j hj).1.2)⟩,
          h4 k x hxS (fun j hj => (hx j hj).2)⟩⟩
  have hS'sm := spIter_smooth hK
  have hS'S : S' ⊆ S := fun x hx => hHS x (hS₁H (hS'S₁ hx))
  have hsmG' : ∀ x ∈ S', (∃ y ∈ S', (x, y) ∈ (E : Set (A × A)) ∩ S' ×ˢ S') ∧
      ∃ y ∈ S', (y, x) ∈ (E : Set (A × A)) ∩ S' ×ˢ S' := by
    intro x hx
    obtain ⟨⟨y, hy, hxy⟩, ⟨y', hy', hyx⟩⟩ := hS'sm x hx
    exact ⟨⟨y, hy, hxy.1, Set.mk_mem_prod hx hy⟩, ⟨y', hy', hyx.1, Set.mk_mem_prod hy' hx⟩⟩
  -- Claim 3.10: any two vertices of `S'` are joined inside `S'` by a walk of length `0`.
  have hconn : ∀ a' ∈ S', ∀ b' ∈ S', Walk ((E : Set (A × A)) ∩ S' ×ˢ S') a' b' 0 := by
    intro a' ha' b' hb'
    obtain ⟨za, hza⟩ := hS₁H (hS'S₁ ha')
    obtain ⟨zb, hzb⟩ := hS₁H (hS'S₁ hb')
    obtain ⟨W, hW, hbW⟩ := img_of_walk (walk_zero hlen hza hzb)
    obtain ⟨h, h0, hl, hhF⟩ := path_of_img hbW
    rw [Set.mem_singleton_iff] at h0
    obtain ⟨f, f0, fl, hfF⟩ := path_of_img (mem_img_self hsmG' ha' hW)
    rw [Set.mem_singleton_iff] at f0
    obtain ⟨g, g0, gl, hgF⟩ := path_of_img (mem_img_self hsmG' hb' hW)
    rw [Set.mem_singleton_iff] at g0
    have := column_walk hid E hS'S t (halg K).2 W f g h
      (follows_mono Set.inter_subset_left hfF) (follows_mono Set.inter_subset_left hgF)
      (follows_mono Set.inter_subset_left hhF) f0 fl g0 gl h0 hl
      (follows_mem hfF (f0 ▸ ha')) (follows_mem hgF (g0 ▸ hb'))
      (follows_mem hhF (h0 ▸ hS'S ha'))
    rwa [hW, mul_zero] at this
  obtain ⟨x, hx⟩ := hYne
  have hxS' := hYS' hx
  obtain ⟨⟨y, hy, hxy⟩, -⟩ := hsmG' x hxS'
  refine ⟨S', Set.ssubset_iff_subset_ne.2 ⟨hS'S, ?_⟩, ⟨x, hxS'⟩, ⟨(halg K).1, n, t, hn, (halg K).2⟩,
    fun z hz => ⟨⟨(hsmG' z hz).1.choose, (hsmG' z hz).1.choose_spec.1,
      (hsmG' z hz).1.choose_spec.2.1⟩, ⟨(hsmG' z hz).2.choose, (hsmG' z hz).2.choose_spec.1,
      (hsmG' z hz).2.choose_spec.2.1⟩⟩, x, hxS', ?_, fun z hz => ⟨0, hconn x hxS' z hz⟩⟩
  · intro hEq
    apply hu
    refine Set.Subset.antisymm hS₁H ?_
    intro z hz
    exact hS'S₁ (hEq ▸ hHS z hz)
  · have := walk_trans (Walk.fwd (Walk.refl x) hxy) (hconn y hy x hxS')
    simpa using this
