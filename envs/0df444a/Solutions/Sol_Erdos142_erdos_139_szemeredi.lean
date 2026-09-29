-- Prove2me | solution 1 for Erdos142.erdos_139_szemeredi
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-26T15:30:43.314625+00:00
-- url     : https://prove2.me/submissions/c495f1d5-dabc-4f87-b6b9-333be4687c98

import Mathlib
import Definitions.Def_Erdos142Basic




/-!
# Infrastructure for combinatorial subspaces

Operations on `Combinatorics.Subspace` (composition, alphabet maps, fixing variables, gluing)
and elementary counting lemmas used in the proof of the density Hales–Jewett theorem.
-/

open Combinatorics Finset

namespace Szem

noncomputable section

open Classical

variable {η θ α β ι ι' κ : Type*}

namespace Sub

/-- Composition of subspaces: `(comp V W) x = V (W x)`. -/
def comp (V : Subspace η α ι) (W : Subspace θ α η) : Subspace θ α ι where
  idxFun i := (V.idxFun i).elim Sum.inl W.idxFun
  proper t := by
    obtain ⟨e, he⟩ := W.proper t
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨i, by simp [hi, he]⟩

@[simp] theorem comp_apply (V : Subspace η α ι) (W : Subspace θ α η) (x : θ → α) :
    comp V W x = V (W x) := by
  funext i
  rw [Subspace.coe_apply, Subspace.coe_apply]
  cases h : V.idxFun i with
  | inl a => simp [comp, h]
  | inr e => simp [comp, h, Subspace.coe_apply]

theorem comp_assoc {ζ : Type*} (V : Subspace η α ι) (W : Subspace θ α η) (U : Subspace ζ α θ) :
    comp (comp V W) U = comp V (comp W U) := by
  ext i : 2
  simp only [comp]
  cases h : V.idxFun i <;> simp

/-- Change of alphabet along a map `f`. -/
def map (f : α → β) (V : Subspace η α ι) : Subspace η β ι where
  idxFun i := Sum.map f id (V.idxFun i)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨i, by simp [hi]⟩

theorem map_apply (f : α → β) (V : Subspace η α ι) (x : η → α) :
    map f V (f ∘ x) = f ∘ V x := by
  funext i
  rw [Subspace.coe_apply, Function.comp_apply, Subspace.coe_apply]
  cases h : V.idxFun i <;> simp [map, h]

theorem map_comp (f : α → β) (V : Subspace η α ι) (W : Subspace θ α η) :
    map f (comp V W) = comp (map f V) (map f W) := by
  ext i : 2
  simp only [map, comp]
  cases h : V.idxFun i <;> simp

/-- The subspace given by an equivalence of coordinates: `ofEquiv e x = x ∘ e`. -/
def ofEquiv (e : ι ≃ η) : Subspace η α ι where
  idxFun i := Sum.inr (e i)
  proper t := ⟨e.symm t, by simp⟩

@[simp] theorem ofEquiv_apply (e : ι ≃ η) (x : η → α) : (ofEquiv e : Subspace η α ι) x = x ∘ e := by
  funext i; simp [ofEquiv, Subspace.coe_apply]

/-- Fix the right variables of a subspace to the values `y`. -/
def fixRight (V : Subspace (η ⊕ θ) α ι) (y : θ → α) : Subspace η α ι where
  idxFun i := match V.idxFun i with
    | Sum.inl a => Sum.inl a
    | Sum.inr (Sum.inl e) => Sum.inr e
    | Sum.inr (Sum.inr t) => Sum.inl (y t)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper (Sum.inl e)
    exact ⟨i, by simp [hi]⟩

@[simp] theorem fixRight_apply (V : Subspace (η ⊕ θ) α ι) (y : θ → α) (w : η → α) :
    fixRight V y w = V (Sum.elim w y) := by
  funext i
  rw [Subspace.coe_apply, Subspace.coe_apply]
  rcases h : V.idxFun i with a | e | t <;> simp [fixRight, h]

/-- Sum of two subspaces on disjoint coordinate sets. -/
def sum {η₁ η₂ ι₁ ι₂ : Type*} (V₁ : Subspace η₁ α ι₁) (V₂ : Subspace η₂ α ι₂) :
    Subspace (η₁ ⊕ η₂) α (ι₁ ⊕ ι₂) where
  idxFun i := match i with
    | Sum.inl i => Sum.map id Sum.inl (V₁.idxFun i)
    | Sum.inr i => Sum.map id Sum.inr (V₂.idxFun i)
  proper e := by
    rcases e with e | e
    · obtain ⟨i, hi⟩ := V₁.proper e
      exact ⟨Sum.inl i, by simp [hi]⟩
    · obtain ⟨i, hi⟩ := V₂.proper e
      exact ⟨Sum.inr i, by simp [hi]⟩

@[simp] theorem sum_apply {η₁ η₂ ι₁ ι₂ : Type*} (V₁ : Subspace η₁ α ι₁) (V₂ : Subspace η₂ α ι₂)
    (x : η₁ ⊕ η₂ → α) : sum V₁ V₂ x = Sum.elim (V₁ (x ∘ Sum.inl)) (V₂ (x ∘ Sum.inr)) := by
  funext i
  rcases i with i | i
  · rw [Subspace.coe_apply]
    simp only [Sum.elim_inl]
    rw [Subspace.coe_apply]
    rcases h : V₁.idxFun i with a | e <;> simp [sum, h]
  · rw [Subspace.coe_apply]
    simp only [Sum.elim_inr]
    rw [Subspace.coe_apply]
    rcases h : V₂.idxFun i with a | e <;> simp [sum, h]

/-- A constant block followed by a subspace. -/
def constLeft {ι₁ ι₂ : Type*} (p : ι₁ → α) (V : Subspace η α ι₂) : Subspace η α (ι₁ ⊕ ι₂) where
  idxFun i := match i with
    | Sum.inl i => Sum.inl (p i)
    | Sum.inr i => V.idxFun i
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨Sum.inr i, by simp [hi]⟩

@[simp] theorem constLeft_apply {ι₁ ι₂ : Type*} (p : ι₁ → α) (V : Subspace η α ι₂) (x : η → α) :
    constLeft p V x = Sum.elim p (V x) := by
  funext i
  rcases i with i | i
  · simp [constLeft, Subspace.coe_apply]
  · rw [Subspace.coe_apply]; simp [constLeft, Subspace.coe_apply]

/-- Reindex the variables of a subspace along an equivalence. -/
def reVar (V : Subspace η α ι) (e : η ≃ θ) : Subspace θ α ι where
  idxFun i := Sum.map id e (V.idxFun i)
  proper t := by
    obtain ⟨i, hi⟩ := V.proper (e.symm t)
    exact ⟨i, by simp [hi]⟩

@[simp] theorem reVar_apply (V : Subspace η α ι) (e : η ≃ θ) (x : θ → α) :
    reVar V e x = V (x ∘ e) := by
  funext i
  rw [Subspace.coe_apply, Subspace.coe_apply]
  rcases h : V.idxFun i with a | t <;> simp [reVar, h]

theorem injective (V : Subspace η α ι) : Function.Injective (⇑V) := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := V.proper e
  have := congrFun hxy i
  rwa [Subspace.apply_inr hi, Subspace.apply_inr hi] at this

/-- An injection of variables with default value elsewhere: embeds `η → α` into `θ → α`. -/
def embed (f : η ↪ θ) (a : α) : Subspace η α θ where
  idxFun t := if h : ∃ e, f e = t then Sum.inr h.choose else Sum.inl a
  proper e := ⟨f e, by
    have h : ∃ e', f e' = f e := ⟨e, rfl⟩
    rw [dif_pos h]
    congr 1
    exact f.injective h.choose_spec⟩

theorem embed_apply_self (f : η ↪ θ) (a : α) (x : η → α) (e : η) : embed f a x (f e) = x e := by
  have h : ∃ e', f e' = f e := ⟨e, rfl⟩
  rw [Subspace.apply_inr (e := h.choose)]
  · rw [f.injective h.choose_spec]
  · simp only [embed, dif_pos h]

theorem embed_idxFun_self (f : η ↪ θ) (a : α) (e : η) : (embed f a).idxFun (f e) = Sum.inr e := by
  have h : ∃ e', f e' = f e := ⟨e, rfl⟩
  simp only [embed, dif_pos h]
  rw [f.injective h.choose_spec]

theorem embed_idxFun_other (f : η ↪ θ) (a : α) (t : θ) (ht : ∀ e, f e ≠ t) :
    (embed f a).idxFun t = Sum.inl a := by
  have h : ¬ ∃ e', f e' = t := fun ⟨e, he⟩ => ht e he
  simp only [embed, dif_neg h]

theorem embed_apply_other (f : η ↪ θ) (a : α) (x : η → α) (t : θ) (ht : ∀ e, f e ≠ t) :
    embed f a x t = a := by
  have h : ¬ ∃ e', f e' = t := fun ⟨e, he⟩ => ht e he
  rw [Subspace.apply_inl]
  simp only [embed, dif_neg h]

instance [Fintype η] [Fintype α] [Fintype ι] [DecidableEq ι] :
    Fintype (Subspace η α ι) :=
  Fintype.ofInjective Subspace.idxFun (fun V W h => by ext1; exact h)

theorem card_le [Fintype η] [Fintype α] [Fintype ι] [DecidableEq ι] :
    Fintype.card (Subspace η α ι) ≤ (Fintype.card α + Fintype.card η) ^ Fintype.card ι := by
  have := Fintype.card_le_of_injective (Subspace.idxFun (η := η) (α := α) (ι := ι))
    (fun V W h => by ext1; exact h)
  simpa [Fintype.card_sum] using this

/-- The image (as a finset of points) of a subspace. -/
def img [Fintype η] [DecidableEq η] [Fintype α] (V : Subspace η α ι) : Finset (ι → α) := Finset.univ.image V

theorem card_img [Fintype η] [DecidableEq η] [Fintype α] (V : Subspace η α ι) :
    (img V).card = Fintype.card α ^ Fintype.card η := by
  rw [img, Finset.card_image_of_injective _ (injective V), Finset.card_univ, Fintype.card_fun]

theorem mem_img [Fintype η] [DecidableEq η] [Fintype α] {V : Subspace η α ι} {z : ι → α} : z ∈ img V ↔ ∃ x, V x = z := by
  simp [img]

end Sub

/-- The points of a line (a subspace with one variable). -/
abbrev lpt (ℓ : Subspace Unit α ι) (a : α) : ι → α := ℓ (fun _ => a)

/-- The preimage of a set of points under a subspace. -/
def pb [Fintype η] [DecidableEq η] [Fintype α] (A : Finset (ι → α)) (V : Subspace η α ι) : Finset (η → α) :=
  Finset.univ.filter (fun x => V x ∈ A)

@[simp] theorem mem_pb [Fintype η] [DecidableEq η] [Fintype α] {A : Finset (ι → α)} {V : Subspace η α ι} {x : η → α} :
    x ∈ pb A V ↔ V x ∈ A := by simp [pb]

theorem pb_comp [Fintype η] [DecidableEq η] [Fintype θ] [DecidableEq θ] [Fintype α] (A : Finset (ι → α)) (V : Subspace η α ι)
    (W : Subspace θ α η) : pb A (Sub.comp V W) = pb (pb A V) W := by
  ext x; simp

/-- The section of `A` at `w` along a subspace with variables `η ⊕ θ`. -/
def sec [Fintype θ] [DecidableEq θ] [Fintype α] (A : Finset (ι → α)) (V : Subspace (η ⊕ θ) α ι) (w : η → α) :
    Finset (θ → α) :=
  Finset.univ.filter (fun y => V (Sum.elim w y) ∈ A)

@[simp] theorem mem_sec [Fintype θ] [DecidableEq θ] [Fintype α] {A : Finset (ι → α)} {V : Subspace (η ⊕ θ) α ι}
    {w : η → α} {y : θ → α} : y ∈ sec A V w ↔ V (Sum.elim w y) ∈ A := by simp [sec]

/-- The fibre of `A` over `y` in the left variables. -/
theorem pb_fixRight [Fintype η] [DecidableEq η] [Fintype α] (A : Finset (ι → α)) (V : Subspace (η ⊕ θ) α ι) (y : θ → α) :
    pb A (Sub.fixRight V y) = Finset.univ.filter (fun w => V (Sum.elim w y) ∈ A) := by
  ext w; simp

/-- Fubini: summing section sizes over `w` equals summing fibre sizes over `y`. -/
theorem sum_card_sec [Fintype η] [DecidableEq η] [Fintype θ] [DecidableEq θ] [Fintype α] (A : Finset (ι → α)) (V : Subspace (η ⊕ θ) α ι) :
    ∑ w : η → α, (sec A V w).card = ∑ y : θ → α, (pb A (Sub.fixRight V y)).card := by
  simp only [sec, pb_fixRight, Finset.card_filter]
  exact Finset.sum_comm

/-- Line with a single variable from a word `x` over `Option α`: `none` positions become the
variable. Needs at least one `none`. -/
def lineOfWord (x : ι → Option α) (h : ∃ i, x i = none) : Subspace Unit α ι where
  idxFun i := match x i with
    | none => Sum.inr ()
    | some a => Sum.inl a
  proper _ := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by simp [hi]⟩

/-! ### Counting -/

theorem card_fun_real [Fintype ι] [Fintype α] :
    (Fintype.card (ι → α) : ℝ) = (Fintype.card α : ℝ) ^ Fintype.card ι := by
  rw [Fintype.card_fun]; push_cast; ring

theorem card_fun_pos [Fintype ι] [Fintype α] [Nonempty α] : (0 : ℝ) < Fintype.card (ι → α) := by
  exact_mod_cast Fintype.card_pos

/-- Pigeonhole: some fibre of a map from a finset into a fintype is large. -/
theorem exists_large_fiber {X Y : Type*} [Fintype Y] [Nonempty Y] [DecidableEq Y] (s : Finset X) (f : X → Y) :
    ∃ y, (s.card : ℝ) ≤ Fintype.card Y * ((s.filter (fun x => f x = y)).card : ℝ) := by
  by_contra hcon
  push_neg at hcon
  have h1 : (s.card : ℝ) = ∑ y : Y, ((s.filter (fun x => f x = y)).card : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x)))
  have h2 : ∑ y : Y, (Fintype.card Y : ℝ) * ((s.filter (fun x => f x = y)).card : ℝ) <
      ∑ _y : Y, (s.card : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun y _ => hcon y)
  rw [← Finset.mul_sum, ← h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  linarith

/-- Markov-type bound: if values in `[0, M]` sum to at least `a * |s|`, then at least
`(a - b)/M * |s|` of them are at least `b`. Stated multiplicatively. -/
theorem markov {X : Type*} (s : Finset X) (f : X → ℝ) (M b : ℝ) (hM : ∀ x ∈ s, f x ≤ M)
    (hb : 0 ≤ b) :
    ∑ x ∈ s, f x ≤ M * (s.filter (fun x => b ≤ f x)).card + b * s.card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (fun x => b ≤ f x)]
  have h1 : ∑ x ∈ s.filter (fun x => b ≤ f x), f x ≤ M * (s.filter (fun x => b ≤ f x)).card := by
    rw [mul_comm]
    have := Finset.sum_le_card_nsmul (s.filter (fun x => b ≤ f x)) f M
      (fun x hx => hM x (Finset.mem_filter.1 hx).1)
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ x ∈ s.filter (fun x => ¬ b ≤ f x), f x ≤ b * s.card := by
    have := Finset.sum_le_card_nsmul (s.filter (fun x => ¬ b ≤ f x)) f b
      (fun x hx => le_of_lt (not_le.1 (Finset.mem_filter.1 hx).2))
    have hc : ((s.filter (fun x => ¬ b ≤ f x)).card : ℝ) ≤ s.card := by
      exact_mod_cast Finset.card_filter_le _ _
    rw [nsmul_eq_mul] at this
    nlinarith
  linarith

end

end Szem




/-!
# Density Hales–Jewett: basic density tools

The statement `DHJProp`, the multidimensional version (Proposition 3 of Dodos–Kanellopoulos–Tyros),
the uniform-sections lemma (Lemma 4) and Corollary 5.
-/

open Combinatorics Finset

namespace Szem

noncomputable section

open Classical

/-- The density Hales–Jewett property for the alphabet `α`: every subset of `α^ι` of density at
least `δ` contains a combinatorial line, once `|ι|` is large. -/
def DHJProp (α : Type) [Fintype α] : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ (ι : Type) [Fintype ι], N ≤ Fintype.card ι →
    ∀ A : Finset (ι → α), δ * (Fintype.card α : ℝ) ^ Fintype.card ι ≤ A.card →
      ∃ ℓ : Subspace Unit α ι, ∀ a, lpt ℓ a ∈ A

/-- Split a finite type of cardinality `a + b` as `Fin a ⊕ Fin b`. -/
def splitEquiv (ι : Type) [Fintype ι] (a b : ℕ) (h : Fintype.card ι = a + b) :
    ι ≃ Fin a ⊕ Fin b :=
  (Fintype.equivFin ι).trans ((finCongr h).trans finSumFinEquiv.symm)

theorem sum_card_sec_equiv {η θ α ι : Type*} [Fintype η] [Fintype θ] [Fintype α] [Fintype ι]
    [DecidableEq η] [DecidableEq θ] (A : Finset (ι → α)) (e : ι ≃ η ⊕ θ) :
    ∑ w : η → α, ((sec A (Sub.ofEquiv e) w).card : ℝ) = A.card := by
  have h1 : ∀ w : η → α, ((sec A (Sub.ofEquiv e) w).card : ℝ) =
      ∑ y : θ → α, if (Sum.elim w y) ∘ e ∈ A then (1 : ℝ) else 0 := by
    intro w
    rw [sec, Finset.card_filter]
    push_cast
    simp only [Sub.ofEquiv_apply]
  simp_rw [h1]
  rw [← Fintype.sum_prod_type' (f := fun w y => if (Sum.elim w y) ∘ e ∈ A then (1:ℝ) else 0)]
  let E : (η → α) × (θ → α) ≃ (ι → α) :=
    (Equiv.sumArrowEquivProdArrow η θ α).symm.trans (Equiv.arrowCongr e.symm (Equiv.refl α))
  rw [Fintype.sum_equiv E _ (fun z => if z ∈ A then (1:ℝ) else 0)]
  · simp only [Finset.sum_boole]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  · intro p
    rfl

theorem exists_ge_of_sum_ge {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (c : ℝ)
    (h : c * Fintype.card X ≤ ∑ x, f x) : ∃ x, c ≤ f x := by
  by_contra hcon
  push_neg at hcon
  have : ∑ x, f x < ∑ _x : X, c :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ => hcon x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  linarith

theorem card_le_pow {ι α : Type*} [Fintype ι] [Fintype α] (A : Finset (ι → α)) :
    (A.card : ℝ) ≤ (Fintype.card α : ℝ) ^ Fintype.card ι := by
  have := Finset.card_le_univ A
  rw [Fintype.card_fun] at this
  exact_mod_cast this

/-- A constant (zero-dimensional) subspace. -/
def constSub {α ι : Type*} (p : ι → α) : Subspace (Fin 0) α ι where
  idxFun i := Sum.inl (p i)
  proper e := e.elim0

theorem constSub_apply {α ι : Type*} (p : ι → α) (x : Fin 0 → α) : constSub p x = p := by
  funext i; simp [constSub, Subspace.coe_apply]

/-- The all-variable line. -/
def diagLine (α ι : Type*) [Nonempty ι] : Subspace Unit α ι where
  idxFun _ := Sum.inr ()
  proper _ := ⟨Classical.arbitrary ι, rfl⟩

instance {α ι : Type*} [Nonempty ι] : Nonempty (Subspace Unit α ι) := ⟨diagLine α ι⟩

/-- Proposition 3: DHJ implies the multidimensional DHJ. -/
theorem mdhj {α : Type} [Fintype α] [Nonempty α] (hD : DHJProp α) (m : ℕ) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ (ι : Type) [Fintype ι], N ≤ Fintype.card ι →
      ∀ A : Finset (ι → α), δ * (Fintype.card α : ℝ) ^ Fintype.card ι ≤ A.card →
        ∃ V : Subspace (Fin m) α ι, ∀ x, V x ∈ A := by
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  induction m with
  | zero =>
    intro δ hδ
    refine ⟨0, fun ι _ _ A hA => ?_⟩
    have hpos : 0 < A.card := by
      have : (0:ℝ) < δ * (Fintype.card α : ℝ) ^ Fintype.card ι := by positivity
      exact_mod_cast this.trans_le hA
    obtain ⟨p, hp⟩ := Finset.card_pos.1 hpos
    exact ⟨constSub p, fun x => by rw [constSub_apply]; exact hp⟩
  | succ m ih =>
    intro δ hδ
    obtain ⟨M0, hM0⟩ := hD (δ / 2) (by positivity)
    set M := max M0 1 with hMdef
    have hM1 : 1 ≤ M := le_max_right _ _
    haveI : Nonempty (Fin M) := ⟨⟨0, hM1⟩⟩
    set L := Fintype.card (Subspace Unit α (Fin M)) with hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast Fintype.card_pos
    obtain ⟨N', hN'⟩ := ih (δ / 2 / L) (by positivity)
    refine ⟨N' + M, fun ι _ hι A hA => ?_⟩
    set a := Fintype.card ι - M with ha
    have hcard : Fintype.card ι = a + M := by omega
    let e := splitEquiv ι a M hcard
    let E : Subspace (Fin a ⊕ Fin M) α ι := Sub.ofEquiv e
    have hsum : ∑ w : Fin a → α, ((sec A E w).card : ℝ) = A.card := sum_card_sec_equiv A e
    set K := (Fintype.card α : ℝ) with hKdef
    -- the set of good prefixes
    set B := Finset.univ.filter
      (fun x : Fin a → α => δ / 2 * K ^ M ≤ ((sec A E x).card : ℝ)) with hB
    have hBcard : δ / 2 * K ^ a ≤ (B.card : ℝ) := by
      have hm := markov (Finset.univ : Finset (Fin a → α)) (fun x => ((sec A E x).card : ℝ))
        (K ^ M) (δ / 2 * K ^ M) (fun x _ => by
          have := card_le_pow (sec A E x); simpa using this) (by positivity)
      try simp only at hm
      rw [hsum] at hm
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hm
      rw [hcard, pow_add] at hA
      push_cast at hm
      have hKM : 0 < K ^ M := by positivity
      rw [← hB] at hm
      nlinarith
    -- for each good prefix choose a line
    have hline : ∀ x ∈ B, ∃ ℓ : Subspace Unit α (Fin M), ∀ c, lpt ℓ c ∈ sec A E x := by
      intro x hx
      apply hM0 (Fin M) (by simp [hMdef]) (sec A E x)
      simp only [hB, Finset.mem_filter] at hx
      simpa [Fintype.card_fin] using hx.2
    choose! ℓf hℓf using hline
    obtain ⟨ℓ0, hℓ0⟩ := exists_large_fiber B ℓf
    set C := Finset.univ.filter (fun x : Fin a → α => ∀ c, E (Sum.elim x (lpt ℓ0 c)) ∈ A) with hC
    have hsub : B.filter (fun x => ℓf x = ℓ0) ⊆ C := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
      intro c
      have := hℓf x hx.1 c
      rw [hx.2] at this
      simpa using this
    have hCcard : δ / 2 / L * K ^ a ≤ (C.card : ℝ) := by
      have h1 : ((B.filter (fun x => ℓf x = ℓ0)).card : ℝ) ≤ C.card := by
        exact_mod_cast Finset.card_le_card hsub
      rw [← hL] at hℓ0
      have h2 : δ / 2 / L * K ^ a ≤ ((B.filter (fun x => ℓf x = ℓ0)).card : ℝ) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hLpos]
        nlinarith
      linarith
    obtain ⟨W, hW⟩ := hN' (Fin a) (by simp [ha]; omega) C (by simpa using hCcard)
    let eqv : Fin m ⊕ Unit ≃ Fin (m + 1) :=
      (Equiv.sumCongr (Equiv.refl (Fin m)) finOneEquiv.symm).trans finSumFinEquiv
    refine ⟨Sub.reVar (Sub.comp E (Sub.sum W ℓ0)) eqv, fun x => ?_⟩
    rw [Sub.reVar_apply, Sub.comp_apply, Sub.sum_apply]
    have hWx := hW (x ∘ eqv ∘ Sum.inl)
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hWx
    have := hWx (x (eqv (Sum.inr ())))
    convert this using 3 <;> rfl

/-- Recursive form of Lemma 4. -/
theorem incr_aux {γ : Type} [Fintype γ] [Nonempty γ] (m : ℕ) (ε ρ : ℝ) (hε : 0 < ε)
    (hρ : ρ * (Fintype.card γ : ℝ) ^ m ≤ ε) (hρ0 : 0 ≤ ρ) :
    ∀ t : ℕ, ∀ (ι : Type) [Fintype ι], (t + 1) * m ≤ Fintype.card ι →
      ∀ (A : Finset (ι → γ)) (τ : ℝ),
        (τ + ε) * (Fintype.card γ : ℝ) ^ Fintype.card ι ≤ A.card →
        (Fintype.card γ : ℝ) ^ Fintype.card ι <
          A.card + t * ρ * (Fintype.card γ : ℝ) ^ Fintype.card ι →
        ∃ (n : ℕ) (V : Subspace (Fin m ⊕ Fin n) γ ι),
          ∀ w, τ * (Fintype.card γ : ℝ) ^ n ≤ (sec A V w).card := by
  set K := (Fintype.card γ : ℝ) with hK
  have hKpos : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  intro t
  induction t with
  | zero =>
    intro ι _ _ A τ _ h2
    have := card_le_pow A
    simp at h2
    linarith
  | succ t ih =>
    intro ι _ hι A τ h1 h2
    set n' := Fintype.card ι - m with hn'
    have hcard : Fintype.card ι = m + n' := by
      have : m ≤ Fintype.card ι := by nlinarith
      omega
    let e := splitEquiv ι m n' hcard
    let E : Subspace (Fin m ⊕ Fin n') γ ι := Sub.ofEquiv e
    by_cases hall : ∀ w, τ * K ^ n' ≤ ((sec A E w).card : ℝ)
    · exact ⟨n', E, hall⟩
    push_neg at hall
    obtain ⟨w0, hw0⟩ := hall
    have hsum : ∑ w : Fin m → γ, ((sec A E w).card : ℝ) = A.card := sum_card_sec_equiv A e
    rw [hcard, pow_add] at h1 h2
    have hKm : 0 < K ^ m := by positivity
    have hKn : 0 < K ^ n' := by positivity
    -- some section has large size
    have hbig : ∃ w1, (A.card : ℝ) / K ^ m + ρ * K ^ n' ≤ (sec A E w1).card := by
      by_contra hcon
      push_neg at hcon
      have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin m → γ))
        (fun w => ((sec A E w).card : ℝ)) (Finset.mem_univ w0)
      have hle := Finset.sum_le_card_nsmul ((Finset.univ : Finset (Fin m → γ)).erase w0)
        (fun w => ((sec A E w).card : ℝ)) ((A.card : ℝ) / K ^ m + ρ * K ^ n')
        (fun w _ => (hcon w).le)
      have hc : (((Finset.univ : Finset (Fin m → γ)).erase w0).card : ℝ) = K ^ m - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin]
        have : 1 ≤ Fintype.card γ ^ m := Nat.one_le_pow _ _ Fintype.card_pos
        push_cast [this]; ring
      rw [nsmul_eq_mul, hc] at hle
      rw [hsum] at hsplit
      have hA' : (τ + ε) * K ^ n' ≤ (A.card : ℝ) / K ^ m := by
        rw [le_div_iff₀ hKm]; nlinarith
      have hexp : (K ^ m - 1) * ((A.card : ℝ) / K ^ m + ρ * K ^ n') =
          A.card - (A.card : ℝ) / K ^ m + (ρ * K ^ m) * K ^ n' - ρ * K ^ n' := by
        field_simp; ring
      have h3 := mul_le_mul_of_nonneg_right hρ hKn.le
      have h4 : 0 ≤ ρ * K ^ n' := by positivity
      try simp only at hsplit hle
      linarith
    obtain ⟨w1, hw1⟩ := hbig
    have hA' : (τ + ε) * K ^ n' ≤ (A.card : ℝ) / K ^ m := by
      rw [le_div_iff₀ hKm]; nlinarith
    obtain ⟨n, V', hV'⟩ := ih (Fin n') (by simp; nlinarith) (sec A E w1) τ
      (by simp only [Fintype.card_fin]; nlinarith)
      (by
        simp only [Fintype.card_fin]
        have : K ^ m * K ^ n' < A.card + (↑(t + 1)) * ρ * (K ^ m * K ^ n') := h2
        have h3 : K ^ n' < (A.card : ℝ) / K ^ m + (↑(t + 1)) * ρ * K ^ n' := by
          rw [← sub_pos]
          have : (A.card : ℝ) / K ^ m + (↑(t + 1)) * ρ * K ^ n' - K ^ n' =
              (A.card + (↑(t + 1)) * ρ * (K ^ m * K ^ n') - K ^ m * K ^ n') / K ^ m := by
            field_simp
          rw [this]
          apply div_pos _ hKm
          linarith
        push_cast at h3 ⊢
        nlinarith)
    refine ⟨n, Sub.comp E (Sub.constLeft w1 V'), fun w => ?_⟩
    have : sec A (Sub.comp E (Sub.constLeft w1 V')) w = sec (sec A E w1) V' w := by
      ext y
      simp
    rw [this]
    exact hV' w

/-- Lemma 4 (uniform sections): every set of density `d` has, along a subspace with `m` free
left variables, all sections of density at least `d - ε`. -/
theorem incr_sections {γ : Type} [Fintype γ] [Nonempty γ] (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (ι : Type) [Fintype ι], N ≤ Fintype.card ι → ∀ (A : Finset (ι → γ)) (τ : ℝ),
      (τ + ε) * (Fintype.card γ : ℝ) ^ Fintype.card ι ≤ A.card →
      ∃ (n : ℕ) (V : Subspace (Fin m ⊕ Fin n) γ ι),
        ∀ w, τ * (Fintype.card γ : ℝ) ^ n ≤ (sec A V w).card := by
  set K := (Fintype.card γ : ℝ)
  have hKpos : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  set ρ := ε / K ^ m with hρ
  have hρpos : 0 < ρ := by positivity
  set t := ⌈1 / ρ⌉₊ + 1 with ht
  refine ⟨(t + 1) * m, fun ι _ hι A τ hA => ?_⟩
  apply incr_aux m ε ρ hε (by rw [hρ, div_mul_cancel₀]; positivity) hρpos.le t ι hι A τ hA
  have h1 : 1 < (t : ℝ) * ρ := by
    have : (1 / ρ) ≤ ⌈1 / ρ⌉₊ := Nat.le_ceil _
    rw [ht]; push_cast
    rw [div_le_iff₀ hρpos] at this
    nlinarith
  have hKc : 0 < K ^ Fintype.card ι := by positivity
  have := (A.card.cast_nonneg : (0:ℝ) ≤ A.card)
  nlinarith

/-- Corollary 5: DHJ for `α` gives, in every dense subset of `(Option α)^ι`, a subspace whose
restriction to the letters of `α` lies in the set. -/
theorem mdhj_star {α : Type} [Fintype α] [Nonempty α] (hD : DHJProp α) (m : ℕ) (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (ι : Type) [Fintype ι], N ≤ Fintype.card ι →
      ∀ A : Finset (ι → Option α),
        δ * (Fintype.card (Option α) : ℝ) ^ Fintype.card ι ≤ A.card →
        ∃ V : Subspace (Fin m) (Option α) ι, ∀ w : Fin m → α, V (some ∘ w) ∈ A := by
  obtain ⟨M, hM⟩ := mdhj hD m (δ / 2) (by positivity)
  obtain ⟨N, hN⟩ := incr_sections (γ := Option α) M (δ / 2) (by positivity)
  refine ⟨N, fun ι _ hι A hA => ?_⟩
  obtain ⟨n, V', hV'⟩ := hN ι hι A (δ / 2) (by ring_nf; ring_nf at hA; linarith)
  set K := (Fintype.card α : ℝ)
  have hK1 : (Fintype.card (Option α) : ℝ) = K + 1 := by simp [Fintype.card_option, K]
  rw [hK1] at hV'
  -- sum over the `α`-points
  have hsum : ∑ u : Fin M → α, ((sec A V' (some ∘ u)).card : ℝ) =
      ∑ y : Fin n → Option α,
        ((Finset.univ.filter (fun u : Fin M → α => V' (Sum.elim (some ∘ u) y) ∈ A)).card : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    congr 1
    simp only [sec, Finset.card_filter]
    rw [Finset.sum_comm]; congr! 3
  have hlow : δ / 2 * (K + 1) ^ n * K ^ M ≤ ∑ u : Fin M → α, ((sec A V' (some ∘ u)).card : ℝ) := by
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin M → α))
      (fun u => ((sec A V' (some ∘ u)).card : ℝ)) (δ / 2 * (K + 1) ^ n) (fun u _ => hV' _)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    linarith
  rw [hsum] at hlow
  obtain ⟨y, hy⟩ := exists_ge_of_sum_ge
    (fun y : Fin n → Option α =>
      ((Finset.univ.filter (fun u : Fin M → α => V' (Sum.elim (some ∘ u) y) ∈ A)).card : ℝ))
    (δ / 2 * K ^ M) (by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_option]
      push_cast
      rw [← hK1] at hlow ⊢
      simp only [Fintype.card_option] at hlow ⊢
      push_cast at hlow ⊢
      linarith)
  obtain ⟨W, hW⟩ := hM (Fin M) (by simp) _ (by simpa using hy)
  refine ⟨Sub.comp (Sub.fixRight V' y) (Sub.map some W), fun w => ?_⟩
  rw [Sub.comp_apply, Sub.map_apply, Sub.fixRight_apply]
  have := hW w
  simpa using this

end

end Szem




/-!
# Canonical colourings of lines

Using the multidimensional Hales–Jewett theorem over the alphabet `Option α`, we find, for any
finite colouring of the combinatorial lines of `α^n` (`n` large), an `M`-dimensional subspace in
which the colour of a line only depends on the position of its first variable coordinate and on
the constant coordinates before it.
-/

open Combinatorics Finset

namespace Szem

noncomputable section

open Classical

/-- In the subspace `Y`, the colour of a line depends only on its first variable coordinate and
the constants before it. -/
def FirstWildCanon {α ι κ : Type*} {M : ℕ} (c : Subspace Unit α ι → κ)
    (Y : Subspace (Fin M) α ι) : Prop :=
  ∀ (ℓ ℓ' : Subspace Unit α (Fin M)) (j : Fin M), ℓ.idxFun j = Sum.inr () →
    ℓ'.idxFun j = Sum.inr () →
    (∀ j' < j, ℓ.idxFun j' = ℓ'.idxFun j' ∧ ∃ a, ℓ.idxFun j' = Sum.inl a) →
    c (Sub.comp Y ℓ) = c (Sub.comp Y ℓ')

/-- One step: a subspace with a distinguished variable `none` such that all lines in which
`none` is a variable coordinate have the same colour. -/
theorem lemmaX (α : Type) [Fintype α] [Nonempty α] (κ : Type) [Fintype κ] [Nonempty κ] (d : ℕ) :
    ∃ n : ℕ, ∀ c : Subspace Unit α (Fin n) → κ,
      ∃ (Z : Subspace (Option (Fin d)) α (Fin n)) (col : κ),
        ∀ ℓ : Subspace Unit α (Option (Fin d)), ℓ.idxFun none = Sum.inr () →
          c (Sub.comp Z ℓ) = col := by
  obtain ⟨n, hn⟩ := Subspace.exists_mono_in_high_dimension_fin (Option α) (Option κ) (Option (Fin d))
  refine ⟨n, fun c => ?_⟩
  let C : (Fin n → Option α) → Option κ := fun x =>
    if h : ∃ i, x i = none then some (c (lineOfWord x h)) else none
  obtain ⟨Z', col', hZ'⟩ := hn C
  let Z : Subspace (Option (Fin d)) α (Fin n) :=
    { idxFun := fun i => match Z'.idxFun i with
        | Sum.inl none => Sum.inr none
        | Sum.inl (some a) => Sum.inl a
        | Sum.inr none => Sum.inr none
        | Sum.inr (some e) => Sum.inr (some e)
      proper := by
        intro v
        rcases v with _ | e
        · obtain ⟨i, hi⟩ := Z'.proper none
          exact ⟨i, by simp [hi]⟩
        · obtain ⟨i, hi⟩ := Z'.proper (some e)
          exact ⟨i, by simp [hi]⟩ }
  -- the word attached to a line
  have key : ∀ ℓ : Subspace Unit α (Option (Fin d)), ℓ.idxFun none = Sum.inr () →
      C (Z' (fun v => (ℓ.idxFun v).elim some (fun _ => none))) = some (c (Sub.comp Z ℓ)) := by
    intro ℓ hℓ
    set u : Option (Fin d) → Option α := fun v => (ℓ.idxFun v).elim some (fun _ => none)
    have hnone : ∃ i, Z' u i = none := by
      obtain ⟨i, hi⟩ := Z'.proper none
      refine ⟨i, ?_⟩
      rw [Subspace.apply_inr hi]
      simp [u, hℓ]
    simp only [C, dif_pos hnone]
    congr 2
    ext i : 2
    simp only [lineOfWord, Sub.comp]
    rcases h : Z'.idxFun i with (_ | a) | (_ | e)
    · rw [Subspace.apply_inl h]; simp [Z, h, hℓ]
    · rw [Subspace.apply_inl h]; simp [Z, h]
    · rw [Subspace.apply_inr h]; simp [Z, h, u, hℓ]
    · rw [Subspace.apply_inr h]
      simp only [Z, h, u]
      rcases hl : ℓ.idxFun (some e) with a | _ <;> simp [hl]
  obtain ⟨ℓ0⟩ : Nonempty (Subspace Unit α (Option (Fin d))) :=
    ⟨⟨fun _ => Sum.inr (), fun _ => ⟨none, rfl⟩⟩⟩
  refine ⟨Z, c (Sub.comp Z ⟨fun _ => Sum.inr (), fun _ => ⟨none, rfl⟩⟩), fun ℓ hℓ => ?_⟩
  have h1 := key ℓ hℓ
  have h2 := key ⟨fun _ => Sum.inr (), fun _ => ⟨none, rfl⟩⟩ rfl
  rw [hZ'] at h1 h2
  rw [h1] at h2
  exact Option.some_injective _ h2

/-- Extend a line of `Fin n'` by a constant `a` at the coordinate `none`. -/
def extLine {α : Type*} {n' : ℕ} (a : α) (lam : Subspace Unit α (Fin n')) :
    Subspace Unit α (Option (Fin n')) where
  idxFun v := match v with
    | none => Sum.inl a
    | some e => lam.idxFun e
  proper _ := by
    obtain ⟨i, hi⟩ := lam.proper ()
    exact ⟨some i, hi⟩

/-- Canonical form theorem. -/
theorem canon (α : Type) [Fintype α] [Nonempty α] :
    ∀ (M : ℕ) (κ : Type) [Fintype κ] [Nonempty κ], ∃ n : ℕ,
      ∀ c : Subspace Unit α (Fin n) → κ, ∃ Y : Subspace (Fin M) α (Fin n), FirstWildCanon c Y := by
  intro M
  induction M with
  | zero =>
    intro κ _ _
    refine ⟨0, fun c => ⟨⟨fun i => i.elim0, fun e => e.elim0⟩, ?_⟩⟩
    intro ℓ ℓ' j
    exact j.elim0
  | succ M ih =>
    intro κ _ _
    obtain ⟨n', hn'⟩ := ih (α → κ)
    obtain ⟨n, hn⟩ := lemmaX α κ n'
    refine ⟨n, fun c => ?_⟩
    obtain ⟨Z, col, hZ⟩ := hn c
    let c' : Subspace Unit α (Fin n') → (α → κ) := fun lam a => c (Sub.comp Z (extLine a lam))
    obtain ⟨Y', hY'⟩ := hn' c'
    let Y'' : Subspace (Fin (M + 1)) α (Option (Fin n')) :=
      { idxFun := fun v => match v with
          | none => Sum.inr 0
          | some e => Sum.map id Fin.succ (Y'.idxFun e)
        proper := by
          intro j
          refine Fin.cases ⟨none, rfl⟩ (fun k => ?_) j
          obtain ⟨i, hi⟩ := Y'.proper k
          exact ⟨some i, by simp [hi]⟩ }
    refine ⟨Sub.comp Z Y'', ?_⟩
    intro ℓ ℓ' j hj hj' hpre
    rw [Sub.comp_assoc, Sub.comp_assoc]
    refine Fin.cases (motive := fun j => ℓ.idxFun j = Sum.inr () → ℓ'.idxFun j = Sum.inr () →
      (∀ j' < j, ℓ.idxFun j' = ℓ'.idxFun j' ∧ ∃ a, ℓ.idxFun j' = Sum.inl a) →
      c (Sub.comp Z (Sub.comp Y'' ℓ)) = c (Sub.comp Z (Sub.comp Y'' ℓ'))) ?_ ?_ j hj hj' hpre
    · intro h0 h0' _
      rw [hZ _ (by simp [Sub.comp, Y'', h0]), hZ _ (by simp [Sub.comp, Y'', h0'])]
    · intro k hk hk' hpre'
      obtain ⟨h00, a, ha⟩ := hpre' 0 (Fin.succ_pos k)
      let ℓr : Subspace Unit α (Fin M) := ⟨fun e => ℓ.idxFun e.succ, fun _ => ⟨k, hk⟩⟩
      let ℓr' : Subspace Unit α (Fin M) := ⟨fun e => ℓ'.idxFun e.succ, fun _ => ⟨k, hk'⟩⟩
      have e1 : Sub.comp Y'' ℓ = extLine a (Sub.comp Y' ℓr) := by
        ext v : 2
        rcases v with _ | e
        · simp [Sub.comp, Y'', extLine, ha]
        · simp only [Sub.comp, Y'', extLine, ℓr]
          rcases Y'.idxFun e with b | t <;> simp
      have e2 : Sub.comp Y'' ℓ' = extLine a (Sub.comp Y' ℓr') := by
        ext v : 2
        rcases v with _ | e
        · simp [Sub.comp, Y'', extLine, ← h00, ha]
        · simp only [Sub.comp, Y'', extLine, ℓr']
          rcases Y'.idxFun e with b | t <;> simp
      rw [e1, e2]
      have := hY' ℓr ℓr' k hk hk' (fun j' hj' => by
        have := hpre' j'.succ (Fin.succ_lt_succ_iff.2 hj')
        exact this)
      exact congrFun this a

end

end Szem




/-!
# Density increment, part 1 (Lemmas 7 and 8 of Dodos–Kanellopoulos–Tyros, modified)

Instead of the Graham–Rothschild theorem we use the canonical colouring lemma `canon`: it yields a
subspace in which a positive proportion (at least `(k+1)^{-m₀}`) of all combinatorial lines are
"good".
-/

open Combinatorics Finset

namespace Szem

noncomputable section

open Classical

variable {α : Type} [Fintype α] [Nonempty α]

/-- If goodness of lines of `Fin m` only depends on the first variable coordinate and the
constants before it, and some good line has a variable coordinate below `N0`, then at least
`(k+1)^(m - N0)` lines are good. -/
theorem count_good_lines {m N0 : ℕ} (hm : N0 ≤ m) (P : Subspace Unit α (Fin m) → Prop)
    (hcanon : ∀ (ℓ ℓ' : Subspace Unit α (Fin m)) (j : Fin m), ℓ.idxFun j = Sum.inr () →
      ℓ'.idxFun j = Sum.inr () →
      (∀ j' < j, ℓ.idxFun j' = ℓ'.idxFun j' ∧ ∃ a, ℓ.idxFun j' = Sum.inl a) → (P ℓ ↔ P ℓ'))
    (ℓs : Subspace Unit α (Fin m)) (hP : P ℓs) (j₀ : Fin m) (hj₀ : (j₀ : ℕ) < N0)
    (hwild : ℓs.idxFun j₀ = Sum.inr ()) :
    ((Fintype.card α : ℝ) + 1) ^ (m - N0) ≤ ((Finset.univ.filter P).card : ℝ) := by
  obtain ⟨a0⟩ := ‹Nonempty α›
  set Wd := Finset.univ.filter (fun j => ℓs.idxFun j = Sum.inr ()) with hWd
  have hne : Wd.Nonempty := ⟨j₀, by simp [hWd, hwild]⟩
  set t := Wd.min' hne with ht
  have htW : ℓs.idxFun t = Sum.inr () := by
    have := Wd.min'_mem hne
    simpa [hWd] using this
  have htj : t ≤ j₀ := Wd.min'_le _ (by simp [hWd, hwild])
  have hbefore : ∀ j < t, ∃ a, ℓs.idxFun j = Sum.inl a := by
    intro j hj
    rcases h : ℓs.idxFun j with a | u
    · exact ⟨a, rfl⟩
    · exfalso
      have : t ≤ j := Wd.min'_le _ (by simp [hWd, h])
      exact absurd hj (not_lt.2 this)
  have htN : (t : ℕ) < N0 := lt_of_le_of_lt (Fin.le_def.1 htj) hj₀
  let F : (Fin (m - N0) → α ⊕ Unit) → Subspace Unit α (Fin m) := fun f =>
    { idxFun := fun j => if h : N0 ≤ (j : ℕ) then f ⟨j - N0, by omega⟩
        else if j ≤ t then ℓs.idxFun j else Sum.inl a0
      proper := fun _ => ⟨t, by simp [htW, not_le.2 htN]⟩ }
  have hF : ∀ f, P (F f) := by
    intro f
    refine (hcanon (F f) ℓs t (by simp [F, htW, not_le.2 htN]) htW (fun j' hj' => ?_)).2 hP
    have hj'N : ¬ N0 ≤ (j' : ℕ) := by
      have : (j' : ℕ) < t := hj'
      omega
    have e1 : (F f).idxFun j' = ℓs.idxFun j' := by simp [F, hj'N, le_of_lt hj']
    rw [e1]
    exact ⟨rfl, hbefore j' hj'⟩
  have hFinj : Function.Injective F := by
    intro f g hfg
    funext k
    have := congrArg (fun V : Subspace Unit α (Fin m) => V.idxFun ⟨k + N0, by omega⟩) hfg
    simp only [F] at this
    rw [dif_pos (by simp), dif_pos (by simp)] at this
    convert this using 2 <;> ext <;> simp
  have hsub : Finset.univ.image F ⊆ Finset.univ.filter P := by
    intro V hV
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hV
    simp [hF f]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_fun,
    Fintype.card_sum, Fintype.card_unit, Fintype.card_fin] at hcard
  exact_mod_cast hcard

/-- Lemma 7 (modified). -/
theorem lemma7 (δ₀ η θ : ℝ) (hδ₀ : 0 < δ₀) (hη : 0 < η) (N0 : ℕ) (hN0pos : 0 < N0)
    (hN0 : ∀ (ι : Type) [Fintype ι], N0 ≤ Fintype.card ι → ∀ A : Finset (ι → α),
      δ₀ / 4 * (Fintype.card α : ℝ) ^ Fintype.card ι ≤ A.card →
        ∃ ℓ : Subspace Unit α ι, ∀ a, lpt ℓ a ∈ A)
    (hθ : θ * Fintype.card (Subspace Unit α (Fin N0)) ≤ δ₀ / 4)
    (m : ℕ) (hm : N0 ≤ m) :
    ∃ N : ℕ, ∀ δ : ℝ, δ₀ ≤ δ → η ^ 2 ≤ δ → ∀ (ι : Type) [Fintype ι], N ≤ Fintype.card ι →
      ∀ A : Finset (ι → Option α), δ * ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι ≤ A.card →
      ∃ (n : ℕ) (U : Subspace (Fin m ⊕ Fin n) (Option α) ι),
        (∀ w, (δ - η ^ 2 / 2) * ((Fintype.card α : ℝ) + 1) ^ n ≤ (sec A U w).card) ∧
        ((Fintype.card α : ℝ) + 1) ^ (m - N0) ≤
          ((Finset.univ.filter (fun ℓ : Subspace Unit α (Fin m) =>
            θ * ((Fintype.card α : ℝ) + 1) ^ n ≤
            ((Finset.univ.filter (fun y : Fin n → Option α =>
              ∀ a : α, U (Sum.elim (some ∘ lpt ℓ a) y) ∈ A)).card : ℝ))).card : ℝ) := by
  obtain ⟨G, hG⟩ := canon α m Bool
  obtain ⟨NL, hNL⟩ := incr_sections (γ := Option α) G (η ^ 2 / 2) (by positivity)
  refine ⟨NL, fun δ hδ hηδ ι _ hι A hA => ?_⟩
  set K := (Fintype.card α : ℝ) with hK
  have hKpos : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  have hco : (Fintype.card (Option α) : ℝ) = K + 1 := by simp [Fintype.card_option, hK]
  obtain ⟨n, V, hV⟩ := hNL ι hι A (δ - η ^ 2 / 2) (by rw [hco]; ring_nf; ring_nf at hA; linarith)
  rw [hco] at hV
  let good : Subspace Unit α (Fin G) → Prop := fun lam =>
    θ * (K + 1) ^ n ≤ ((Finset.univ.filter (fun y : Fin n → Option α =>
      ∀ a : α, V (Sum.elim (some ∘ lpt lam a) y) ∈ A)).card : ℝ)
  obtain ⟨Y, hY⟩ := hG (fun lam => decide (good lam))
  let U : Subspace (Fin m ⊕ Fin n) (Option α) ι :=
    Sub.comp V (Sub.sum (Sub.map some Y) (Sub.ofEquiv (Equiv.refl (Fin n))))
  have hU : ∀ w y, U (Sum.elim w y) = V (Sum.elim (Sub.map some Y w) y) := by
    intro w y
    simp only [U, Sub.comp_apply, Sub.sum_apply, Sub.ofEquiv_apply]
    congr 2
  refine ⟨n, U, ?_, ?_⟩
  · intro w
    have : sec A U w = sec A V (Sub.map some Y w) := by ext y; simp [hU]
    rw [this]; exact hV _
  -- transfer of goodness
  have hgoodU : ∀ ℓ : Subspace Unit α (Fin m),
      (θ * (K + 1) ^ n ≤ ((Finset.univ.filter (fun y : Fin n → Option α =>
        ∀ a : α, U (Sum.elim (some ∘ lpt ℓ a) y) ∈ A)).card : ℝ)) ↔ good (Sub.comp Y ℓ) := by
    intro ℓ
    have : (Finset.univ.filter (fun y : Fin n → Option α =>
        ∀ a : α, U (Sum.elim (some ∘ lpt ℓ a) y) ∈ A)) =
        Finset.univ.filter (fun y : Fin n → Option α =>
          ∀ a : α, V (Sum.elim (some ∘ lpt (Sub.comp Y ℓ) a) y) ∈ A) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hU, lpt, Sub.comp_apply,
        Sub.map_apply]
    rw [this]
  -- one good line inside the first `N0` coordinates
  obtain ⟨a0⟩ := ‹Nonempty α›
  haveI : Nonempty (Fin N0) := ⟨⟨0, hN0pos⟩⟩
  let Z0 : Subspace (Fin N0) α (Fin m) := Sub.embed (Fin.castLEEmb hm) a0
  let Z' := Sub.comp Y Z0
  let P : (Fin n → Option α) → Finset (Fin N0 → α) := fun y =>
    Finset.univ.filter (fun w => V (Sum.elim (some ∘ Z' w) y) ∈ A)
  have hsum : ∑ y : Fin n → Option α, ((P y).card : ℝ) =
      ∑ w : Fin N0 → α, ((sec A V (some ∘ Z' w)).card : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    congr 1
    simp only [P, sec, Finset.card_filter]
    rw [Finset.sum_comm]
    congr! 3
  have hlow : K ^ N0 * (δ / 2 * (K + 1) ^ n) ≤
      ∑ w : Fin N0 → α, ((sec A V (some ∘ Z' w)).card : ℝ) := by
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin N0 → α))
      (fun w => ((sec A V (some ∘ Z' w)).card : ℝ)) (δ / 2 * (K + 1) ^ n) (fun w _ => by
        have h1 := hV (some ∘ Z' w)
        have h2 : δ / 2 * (K + 1) ^ n ≤ (δ - η ^ 2 / 2) * (K + 1) ^ n := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
        linarith)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    linarith
  set Bset := Finset.univ.filter (fun y : Fin n → Option α => δ / 4 * K ^ N0 ≤ ((P y).card : ℝ))
    with hBset
  have hB : δ / 4 * (K + 1) ^ n ≤ (Bset.card : ℝ) := by
    have hm' := markov (Finset.univ : Finset (Fin n → Option α)) (fun y => ((P y).card : ℝ))
      (K ^ N0) (δ / 4 * K ^ N0) (fun y _ => by
        have := card_le_pow (P y); simpa using this) (by
          have : 0 < δ := by linarith
          positivity)
    try simp only at hm'
    rw [hsum] at hm'
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_option] at hm'
    push_cast at hm'
    rw [← hBset] at hm'
    have hKN : 0 < K ^ N0 := by positivity
    nlinarith
  have hline : ∀ y ∈ Bset, ∃ lam : Subspace Unit α (Fin N0), ∀ a, lpt lam a ∈ P y := by
    intro y hy
    apply hN0 (Fin N0) (by simp) (P y)
    simp only [hBset, Finset.mem_filter] at hy
    simp only [Fintype.card_fin]
    have : δ₀ / 4 * K ^ N0 ≤ δ / 4 * K ^ N0 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    linarith [hy.2]
  choose! lf hlf using hline
  obtain ⟨lam0, hlam0⟩ := exists_large_fiber Bset lf
  have hg : good (Sub.comp Y (Sub.comp Z0 lam0)) := by
    show θ * (K + 1) ^ n ≤ _
    have hsub : Bset.filter (fun y => lf y = lam0) ⊆ Finset.univ.filter (fun y : Fin n → Option α =>
        ∀ a : α, V (Sum.elim (some ∘ lpt (Sub.comp Y (Sub.comp Z0 lam0)) a) y) ∈ A) := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro a
      have := hlf y hy.1 a
      rw [hy.2] at this
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at this
      simpa [lpt, Z'] using this
    have h1 := Finset.card_le_card hsub
    have hLpos : (0 : ℝ) < Fintype.card (Subspace Unit α (Fin N0)) :=
      Nat.cast_pos.mpr Fintype.card_pos
    have h2 : θ * (K + 1) ^ n * Fintype.card (Subspace Unit α (Fin N0)) ≤
        δ / 4 * (K + 1) ^ n := by
      have : θ * Fintype.card (Subspace Unit α (Fin N0)) ≤ δ / 4 := by linarith
      have hp : 0 < (K + 1) ^ n := by positivity
      nlinarith
    have h3 : (Bset.card : ℝ) ≤ Fintype.card (Subspace Unit α (Fin N0)) *
        ((Bset.filter (fun y => lf y = lam0)).card : ℝ) := hlam0
    have h4 := (Nat.cast_le (α := ℝ)).mpr h1
    have h5 : θ * (K + 1) ^ n * Fintype.card (Subspace Unit α (Fin N0)) ≤
        Fintype.card (Subspace Unit α (Fin N0)) *
          ((Bset.filter (fun y => lf y = lam0)).card : ℝ) := by linarith
    have h6 : θ * (K + 1) ^ n ≤ ((Bset.filter (fun y => lf y = lam0)).card : ℝ) := by
      by_contra hc
      push_neg at hc
      nlinarith
    linarith
  -- a wild coordinate of `lam0` below `N0`
  obtain ⟨j1, hj1⟩ := lam0.proper ()
  apply count_good_lines hm _ ?_ (Sub.comp Z0 lam0) ((hgoodU _).2 hg) (Fin.castLE hm j1)
    (by simp) (by
      simp only [Sub.comp, Z0]
      rw [show Fin.castLE hm j1 = Fin.castLEEmb hm j1 from rfl, Sub.embed_idxFun_self]
      simpa using hj1)
  intro ℓ ℓ' j h1 h2 h3
  rw [hgoodU, hgoodU]
  have := hY ℓ ℓ' j h1 h2 h3
  simp only [decide_eq_decide] at this
  exact this

set_option maxHeartbeats 1000000 in
/-- Lemma 8: either a density increment on an `m`-dimensional subspace, or a subspace with almost
the same density containing many lines of its `α`-part. -/
theorem lemma8 (δ₀ η θ : ℝ) (hδ₀ : 0 < δ₀) (hη : 0 < η) (N0 : ℕ) (hN0pos : 0 < N0)
    (hN0 : ∀ (ι : Type) [Fintype ι], N0 ≤ Fintype.card ι → ∀ A : Finset (ι → α),
      δ₀ / 4 * (Fintype.card α : ℝ) ^ Fintype.card ι ≤ A.card →
        ∃ ℓ : Subspace Unit α ι, ∀ a, lpt ℓ a ∈ A)
    (hθ : θ * Fintype.card (Subspace Unit α (Fin N0)) ≤ δ₀ / 4)
    (hηθ : η < θ / ((Fintype.card α : ℝ) + 1) ^ N0)
    (m : ℕ) (hm : N0 ≤ m) :
    ∃ N : ℕ, ∀ δ : ℝ, δ₀ ≤ δ → η ^ 2 ≤ δ → ∀ (ι : Type) [Fintype ι], N ≤ Fintype.card ι →
      ∀ A : Finset (ι → Option α), δ * ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι ≤ A.card →
      (∃ X : Subspace (Fin m) (Option α) ι,
        (δ + η ^ 2 / 2) * ((Fintype.card α : ℝ) + 1) ^ m ≤ (pb A X).card) ∨
      (∃ W : Subspace (Fin m) (Option α) ι,
        (δ - 2 * η) * ((Fintype.card α : ℝ) + 1) ^ m ≤ (pb A W).card ∧
        θ / ((Fintype.card α : ℝ) + 1) ^ N0 / 2 * ((Fintype.card α : ℝ) + 1) ^ m ≤
          ((Finset.univ.filter (fun ℓ : Subspace Unit α (Fin m) =>
            ∀ a : α, W (some ∘ lpt ℓ a) ∈ A)).card : ℝ)) := by
  obtain ⟨N, hN⟩ := lemma7 δ₀ η θ hδ₀ hη N0 hN0pos hN0 hθ m hm
  refine ⟨N, fun δ hδ hηδ ι _ hι A hA => ?_⟩
  by_cases hX : ∃ X : Subspace (Fin m) (Option α) ι,
      (δ + η ^ 2 / 2) * ((Fintype.card α : ℝ) + 1) ^ m ≤ (pb A X).card
  · exact Or.inl hX
  right
  push_neg at hX
  set K := (Fintype.card α : ℝ) with hK
  have hKpos : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨n, U, hUa, hUb⟩ := hN δ hδ hηδ ι hι A hA
  set θ' := θ / (K + 1) ^ N0 with hθ'
  have hKm : 0 < (K + 1) ^ m := by positivity
  have hKn : 0 < (K + 1) ^ n := by positivity
  -- fibres over `y`
  let f : (Fin n → Option α) → ℝ := fun y => ((pb A (Sub.fixRight U y)).card : ℝ)
  have hfsum : ∑ y, f y = ∑ w : Fin m → Option α, ((sec A U w).card : ℝ) := by
    simp only [f]
    rw [← Nat.cast_sum, ← Nat.cast_sum, sum_card_sec]
  have hflow : (K + 1) ^ m * ((δ - η ^ 2 / 2) * (K + 1) ^ n) ≤ ∑ y, f y := by
    rw [hfsum]
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin m → Option α))
      (fun w => ((sec A U w).card : ℝ)) ((δ - η ^ 2 / 2) * (K + 1) ^ n) (fun w _ => hUa w)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_option,
      nsmul_eq_mul] at this
    push_cast at this
    linarith
  have hfup : ∀ y, f y < (δ + η ^ 2 / 2) * (K + 1) ^ m := fun y => hX _
  set bad := Finset.univ.filter (fun y : Fin n → Option α => f y < (δ - 2 * η) * (K + 1) ^ m)
    with hbad
  have hbadcard : (bad.card : ℝ) ≤ η / 2 * (K + 1) ^ n := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n → Option α))
      (fun y => f y < (δ - 2 * η) * (K + 1) ^ m) f
    have h1 : ∑ y ∈ bad, f y ≤ bad.card * ((δ - 2 * η) * (K + 1) ^ m) := by
      have := Finset.sum_le_card_nsmul bad f ((δ - 2 * η) * (K + 1) ^ m)
        (fun y hy => le_of_lt (Finset.mem_filter.1 hy).2)
      simpa [nsmul_eq_mul] using this
    have h2 : ∑ y ∈ Finset.univ.filter (fun y => ¬ f y < (δ - 2 * η) * (K + 1) ^ m), f y ≤
        (Finset.univ.filter (fun y : Fin n → Option α =>
          ¬ f y < (δ - 2 * η) * (K + 1) ^ m)).card * ((δ + η ^ 2 / 2) * (K + 1) ^ m) := by
      have := Finset.sum_le_card_nsmul (Finset.univ.filter (fun y : Fin n → Option α =>
          ¬ f y < (δ - 2 * η) * (K + 1) ^ m)) f ((δ + η ^ 2 / 2) * (K + 1) ^ m)
        (fun y _ => le_of_lt (hfup y))
      simpa [nsmul_eq_mul] using this
    have h3 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun y : Fin n → Option α => f y < (δ - 2 * η) * (K + 1) ^ m)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_option] at h3
    have h3' : ((Finset.univ.filter (fun y : Fin n → Option α =>
        ¬ f y < (δ - 2 * η) * (K + 1) ^ m)).card : ℝ) = (K + 1) ^ n - bad.card := by
      rw [← hbad] at h3
      have : ((bad.card + (Finset.univ.filter (fun y : Fin n → Option α =>
          ¬ f y < (δ - 2 * η) * (K + 1) ^ m)).card : ℕ) : ℝ) = ((Fintype.card α + 1) ^ n : ℕ) := by
        rw [h3]
      push_cast at this
      linarith
    rw [← hbad] at hsplit
    rw [h3'] at h2
    have key : (K + 1) ^ m * ((δ - η ^ 2 / 2) * (K + 1) ^ n) ≤
        bad.card * ((δ - 2 * η) * (K + 1) ^ m) +
          ((K + 1) ^ n - bad.card) * ((δ + η ^ 2 / 2) * (K + 1) ^ m) := by linarith
    have key2 : (bad.card : ℝ) * (2 * η + η ^ 2 / 2) * (K + 1) ^ m ≤
        η ^ 2 * (K + 1) ^ n * (K + 1) ^ m := by nlinarith
    have key3 : (bad.card : ℝ) * (2 * η + η ^ 2 / 2) ≤ η ^ 2 * (K + 1) ^ n := by
      by_contra hc; push_neg at hc; nlinarith
    have hb0 : (0 : ℝ) ≤ bad.card := Nat.cast_nonneg _
    nlinarith
  -- lines
  let g : (Fin n → Option α) → ℝ := fun y =>
    ((Finset.univ.filter (fun ℓ : Subspace Unit α (Fin m) =>
      ∀ a : α, U (Sum.elim (some ∘ lpt ℓ a) y) ∈ A)).card : ℝ)
  have hLm : (Fintype.card (Subspace Unit α (Fin m)) : ℝ) ≤ (K + 1) ^ m := by
    have := Sub.card_le (η := Unit) (α := α) (ι := Fin m)
    simp only [Fintype.card_unit, Fintype.card_fin] at this
    rw [hK]; exact_mod_cast this
  have hgup : ∀ y, g y ≤ (K + 1) ^ m := by
    intro y
    have := Finset.card_le_univ (Finset.univ.filter (fun ℓ : Subspace Unit α (Fin m) =>
      ∀ a : α, U (Sum.elim (some ∘ lpt ℓ a) y) ∈ A))
    have : g y ≤ Fintype.card (Subspace Unit α (Fin m)) := by simp only [g]; exact_mod_cast this
    linarith
  have hgsum : ∑ y, g y = ∑ ℓ : Subspace Unit α (Fin m),
      ((Finset.univ.filter (fun y : Fin n → Option α =>
        ∀ a : α, U (Sum.elim (some ∘ lpt ℓ a) y) ∈ A)).card : ℝ) := by
    simp only [g]
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    congr 1
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hglow : θ' * (K + 1) ^ m * (K + 1) ^ n ≤ ∑ y, g y := by
    rw [hgsum]
    set goodL := Finset.univ.filter (fun ℓ : Subspace Unit α (Fin m) =>
      θ * (K + 1) ^ n ≤ ((Finset.univ.filter (fun y : Fin n → Option α =>
        ∀ a : α, U (Sum.elim (some ∘ lpt ℓ a) y) ∈ A)).card : ℝ)) with hgoodL
    have h1 : ∑ ℓ ∈ goodL, θ * (K + 1) ^ n ≤ ∑ ℓ : Subspace Unit α (Fin m),
        ((Finset.univ.filter (fun y : Fin n → Option α =>
          ∀ a : α, U (Sum.elim (some ∘ lpt ℓ a) y) ∈ A)).card : ℝ) := by
      calc ∑ ℓ ∈ goodL, θ * (K + 1) ^ n ≤ ∑ ℓ ∈ goodL, ((Finset.univ.filter (fun y : Fin n → Option α =>
            ∀ a : α, U (Sum.elim (some ∘ lpt ℓ a) y) ∈ A)).card : ℝ) :=
            Finset.sum_le_sum (fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.cast_nonneg _)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : θ' * (K + 1) ^ m = θ * (K + 1) ^ (m - N0) := by
      rw [hθ']
      have : (K + 1) ^ m = (K + 1) ^ (m - N0) * (K + 1) ^ N0 := by
        rw [← pow_add]; congr 1; omega
      rw [this]; field_simp
    rw [h2]
    have hθpos : 0 ≤ θ := by
      have : 0 < θ' := lt_trans hη hηθ
      rw [hθ'] at this
      have := (div_pos_iff.1 this)
      rcases this with ⟨h, _⟩ | ⟨_, h⟩
      · exact h.le
      · exfalso; have : 0 < (K + 1) ^ N0 := by positivity
        linarith
    have : θ * (K + 1) ^ (m - N0) * (K + 1) ^ n ≤ (goodL.card : ℝ) * (θ * (K + 1) ^ n) := by
      have := mul_le_mul_of_nonneg_left hUb (by positivity : 0 ≤ θ * (K + 1) ^ n)
      nlinarith
    linarith
  set H2 := Finset.univ.filter (fun y : Fin n → Option α => θ' / 2 * (K + 1) ^ m ≤ g y) with hH2
  have hH2card : θ' / 2 * (K + 1) ^ n ≤ (H2.card : ℝ) := by
    have hθ'pos : 0 < θ' := lt_trans hη hηθ
    have hm' := markov (Finset.univ : Finset (Fin n → Option α)) g ((K + 1) ^ m)
      (θ' / 2 * (K + 1) ^ m) (fun y _ => hgup y) (by positivity)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_option] at hm'
    push_cast at hm'
    rw [← hH2] at hm'
    nlinarith
  -- choose `y` in `H2` but not in `bad`
  have hexists : ∃ y ∈ H2, y ∉ bad := by
    by_contra hc
    push_neg at hc
    have : H2 ⊆ bad := fun y hy => hc y hy
    have := Finset.card_le_card this
    have : (H2.card : ℝ) ≤ bad.card := Nat.cast_le.mpr this
    have : η / 2 * (K + 1) ^ n < θ' / 2 * (K + 1) ^ n := by
      apply mul_lt_mul_of_pos_right _ hKn; linarith
    linarith
  obtain ⟨y, hyH, hybad⟩ := hexists
  refine ⟨Sub.fixRight U y, ?_, ?_⟩
  · have h := hybad
    rw [hbad, Finset.mem_filter, not_and, not_lt] at h
    exact h (Finset.mem_univ _)
  · have h := hyH
    rw [hH2, Finset.mem_filter] at h
    refine le_trans h.2 (le_of_eq ?_)
    simp only [g, Sub.fixRight_apply]

end

end Szem




/-!
# Insensitive sets

A set `D ⊆ (ι → Option α)` is `(a, none)`-insensitive on the coordinates `S` if membership in `D`
does not change when, on coordinates of `S`, the letter `none` is replaced by `some a`.
-/

open Combinatorics Finset

namespace Szem

noncomputable section

open Classical

variable {α ι η : Type*}

/-- Replace `none` by `some a` on the coordinates in `S`. -/
def colS (S : Finset ι) (a : α) (z : ι → Option α) : ι → Option α :=
  fun i => if i ∈ S then some ((z i).getD a) else z i

/-- Insensitivity on the coordinates of `S`. -/
def InsensOn (S : Finset ι) (a : α) (D : Finset (ι → Option α)) : Prop :=
  ∀ z, z ∈ D ↔ colS S a z ∈ D

/-- Full insensitivity. -/
abbrev Insens [Fintype ι] (a : α) (D : Finset (ι → Option α)) : Prop := InsensOn Finset.univ a D

theorem colS_colS_of_subset {S S' : Finset ι} (h : S' ⊆ S) (a : α) (z : ι → Option α) :
    colS S a (colS S' a z) = colS S a z := by
  funext i
  simp only [colS]
  by_cases hi : i ∈ S
  · by_cases hi' : i ∈ S' <;> simp [hi, hi']
  · have : i ∉ S' := fun h' => hi (h h')
    simp [hi, this]

theorem InsensOn.mono {S S' : Finset ι} (h : S' ⊆ S) {a : α} {D : Finset (ι → Option α)}
    (hD : InsensOn S a D) : InsensOn S' a D := by
  intro z
  rw [hD z, hD (colS S' a z), colS_colS_of_subset h]

theorem insensOn_univ_set [Fintype (ι → Option α)] (S : Finset ι) (a : α) :
    InsensOn S a (Finset.univ : Finset (ι → Option α)) := by
  intro z; simp

theorem InsensOn.compl [Fintype (ι → Option α)] [DecidableEq (ι → Option α)] {S : Finset ι} {a : α} {D : Finset (ι → Option α)}
    (hD : InsensOn S a D) : InsensOn S a (Finset.univ \ D) := by
  intro z; simp [hD z]

theorem InsensOn.inter [DecidableEq (ι → Option α)] {S : Finset ι} {a : α} {D D' : Finset (ι → Option α)}
    (hD : InsensOn S a D) (hD' : InsensOn S a D') : InsensOn S a (D ∩ D') := by
  intro z; simp [hD z, hD' z]

theorem InsensOn.sdiff [DecidableEq (ι → Option α)] {S : Finset ι} {a : α} {D D' : Finset (ι → Option α)}
    (hD : InsensOn S a D) (hD' : InsensOn S a D') : InsensOn S a (D \ D') := by
  intro z; simp [hD z, hD' z]

theorem colS_univ_apply [Fintype ι] (a : α) (z : ι → Option α) (i : ι) :
    colS Finset.univ a z i = some ((z i).getD a) := by simp [colS]

theorem colS_univ_eq [Fintype ι] (a : α) (z : ι → Option α) :
    colS Finset.univ a z = some ∘ (fun i => (z i).getD a) := by
  funext i; simp [colS]

/-- Collapsing commutes with subspaces, up to a further collapse. -/
theorem colS_univ_sub [Fintype ι] [Fintype η] (V : Subspace η (Option α) ι) (a : α)
    (x : η → Option α) :
    colS Finset.univ a (V (colS Finset.univ a x)) = colS Finset.univ a (V x) := by
  funext i
  simp only [colS_univ_apply]
  rw [Subspace.coe_apply, Subspace.coe_apply]
  cases V.idxFun i <;> simp [colS]

/-- Pullbacks of insensitive sets along subspaces are insensitive. -/
theorem Insens.pb [Fintype ι] [Fintype η] [DecidableEq η] [Fintype α] {a : α}
    {D : Finset (ι → Option α)} (hD : Insens a D) (V : Subspace η (Option α) ι) :
    Insens a (pb D V) := by
  intro x
  rw [mem_pb, mem_pb, hD (V x), hD (V (colS _ a x)), colS_univ_sub]

/-- If all `α`-points of a subspace lie in an insensitive set, the whole subspace does. -/
theorem Insens.all_of_letters [Fintype ι] [Fintype η] [DecidableEq η] [Fintype α] {a : α}
    {D : Finset (ι → Option α)} (hD : Insens a D) (V : Subspace η (Option α) ι)
    (hV : ∀ w : η → α, V (some ∘ w) ∈ D) (x : η → Option α) : V x ∈ D := by
  have := hD.pb V x
  rw [mem_pb, mem_pb, colS_univ_eq] at this
  exact this.2 (hV _)

end

end Szem




/-!
# Tiling insensitive sets by subspaces (Lemma 12 and Corollary 13 of Dodos–Kanellopoulos–Tyros)
-/

open Combinatorics Finset

namespace Szem

noncomputable section

open Classical

/-- `D` can be tiled by pairwise disjoint `d`-dimensional subspaces contained in `D`, up to an
error of `ε` times the size of the cube. -/
def Tiles {α : Type} [Fintype α] {ι : Type} [Fintype ι] (d : ℕ) (D : Finset (ι → Option α))
    (ε : ℝ) : Prop :=
  ∃ F : Finset (Subspace (Fin d) (Option α) ι), (∀ V ∈ F, Sub.img V ⊆ D) ∧
    (F : Set (Subspace (Fin d) (Option α) ι)).PairwiseDisjoint Sub.img ∧
    ((D \ F.biUnion Sub.img).card : ℝ) ≤ ε * ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι

/-- Split the coordinates into those outside `B` and those of `B`. -/
def splitB {ι : Type} (B : Finset ι) (M : ℕ) (h : B.card = M) : ι ≃ {i // i ∉ B} ⊕ Fin M :=
  (Equiv.sumCompl (· ∈ B)).symm.trans
    ((Equiv.sumComm _ _).trans (Equiv.sumCongr (Equiv.refl _) (B.equivFin.trans (finCongr h))))

theorem splitB_of_mem {ι : Type} (B : Finset ι) (M : ℕ) (h : B.card = M) {i : ι} (hi : i ∈ B) :
    splitB B M h i = Sum.inr (finCongr h (B.equivFin ⟨i, hi⟩)) := by
  simp [splitB, Equiv.sumCompl_symm_apply_of_pos hi]

theorem splitB_of_not_mem {ι : Type} (B : Finset ι) (M : ℕ) (h : B.card = M) {i : ι}
    (hi : i ∉ B) : splitB B M h i = Sum.inl ⟨i, hi⟩ := by
  simp [splitB, Equiv.sumCompl_symm_apply_of_neg hi]

variable {α : Type} [Fintype α] [Nonempty α]

/-- One round of the tiling procedure. -/
theorem tile_step (hD : DHJProp α) (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ M1 : ℕ, ∃ Θ : ℝ, 0 < Θ ∧ ∀ (ι : Type) [Fintype ι] (S : Finset ι), M1 ≤ S.card →
      ∀ (a : α) (Dc : Finset (ι → Option α)), InsensOn S a Dc →
      2 * β * ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι ≤ Dc.card →
      ∃ S' : Finset ι, S.card ≤ S'.card + M1 ∧
      ∃ Fn : Finset (Subspace (Fin d) (Option α) ι), (∀ V ∈ Fn, Sub.img V ⊆ Dc) ∧
        (Fn : Set (Subspace (Fin d) (Option α) ι)).PairwiseDisjoint Sub.img ∧
        Θ * ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι ≤ (Fn.biUnion Sub.img).card ∧
        InsensOn S' a (Dc \ Fn.biUnion Sub.img) := by
  obtain ⟨M1, hM1⟩ := mdhj_star hD d β hβ
  set K := (Fintype.card α : ℝ) with hK
  have hKpos : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  set L := (K + 1 + d) ^ M1 with hL
  have hLpos : 0 < L := by positivity
  refine ⟨M1, β / L * (K + 1) ^ d / (K + 1) ^ M1, by positivity, ?_⟩
  intro ι _ S hS a Dc hDc hcard
  obtain ⟨B, hBS, hBcard⟩ := Finset.exists_subset_card_eq hS
  set e := splitB B M1 hBcard with he
  set E : Subspace ({i // i ∉ B} ⊕ Fin M1) (Option α) ι := Sub.ofEquiv e with hEdef
  have hE : ∀ x y, E (Sum.elim x y) = (Sum.elim x y) ∘ e := fun x y => Sub.ofEquiv_apply e _
  have hDcB : InsensOn B a Dc := hDc.mono hBS
  have key1 : ∀ (x : {i // i ∉ B} → Option α) (y : Fin M1 → Option α),
      E (Sum.elim x (colS Finset.univ a y)) = colS B a (E (Sum.elim x y)) := by
    intro x y
    rw [hE, hE]
    funext i
    simp only [Function.comp_apply, colS]
    by_cases hi : i ∈ B
    · rw [he, splitB_of_mem B M1 hBcard hi]; simp [hi, colS_univ_apply]
    · rw [he, splitB_of_not_mem B M1 hBcard hi]; simp [hi]
  have hsecins : ∀ x, Insens a (sec Dc E x) := by
    intro x y
    rw [mem_sec, mem_sec, key1]
    exact hDcB _
  have hcardO : Fintype.card {i // i ∉ B} + M1 = Fintype.card ι := by
    rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin]
  set n' := Fintype.card {i // i ∉ B} with hn'
  have hsum : ∑ x : {i // i ∉ B} → Option α, ((sec Dc E x).card : ℝ) = Dc.card :=
    sum_card_sec_equiv Dc e
  set T1 := Finset.univ.filter
    (fun x : {i // i ∉ B} → Option α => β * (K + 1) ^ M1 ≤ ((sec Dc E x).card : ℝ)) with hT1def
  have hT1 : β * (K + 1) ^ n' ≤ (T1.card : ℝ) := by
    have hm := markov (Finset.univ : Finset ({i // i ∉ B} → Option α))
      (fun x => ((sec Dc E x).card : ℝ)) ((K + 1) ^ M1) (β * (K + 1) ^ M1) (fun x _ => by
        have := card_le_pow (sec Dc E x)
        simpa [Fintype.card_option, hK] using this) (by positivity)
    try simp only at hm
    rw [hsum, ← hT1def] at hm
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_option] at hm
    push_cast at hm
    rw [← hcardO, pow_add] at hcard
    have hKM : 0 < (K + 1) ^ M1 := by positivity
    have : (K + 1) ^ M1 * (β * (K + 1) ^ n') ≤ (K + 1) ^ M1 * T1.card := by nlinarith
    exact le_of_mul_le_mul_left this hKM
  have hline : ∀ x ∈ T1, ∃ V : Subspace (Fin d) (Option α) (Fin M1), ∀ y, V y ∈ sec Dc E x := by
    intro x hx
    obtain ⟨V, hV⟩ := hM1 (Fin M1) (by simp) (sec Dc E x) (by
      have := (Finset.mem_filter.1 hx).2
      simpa [Fintype.card_option, hK] using this)
    exact ⟨V, (hsecins x).all_of_letters V hV⟩
  have hT1pos : 0 < T1.card := by
    have : (0 : ℝ) < T1.card := lt_of_lt_of_le (by positivity) hT1
    exact_mod_cast this
  obtain ⟨x0, hx0⟩ := Finset.card_pos.1 hT1pos
  obtain ⟨V0, -⟩ := hline x0 hx0
  haveI : Nonempty (Subspace (Fin d) (Option α) (Fin M1)) := ⟨V0⟩
  choose! Vf hVf using hline
  obtain ⟨V1, hV1⟩ := exists_large_fiber T1 Vf
  have hY : (Fintype.card (Subspace (Fin d) (Option α) (Fin M1)) : ℝ) ≤ L := by
    have := Sub.card_le (η := Fin d) (α := Option α) (ι := Fin M1)
    simp only [Fintype.card_option, Fintype.card_fin] at this
    rw [hL, hK]
    exact_mod_cast this
  set S1 := Finset.univ.filter
    (fun x : {i // i ∉ B} → Option α => ∀ y, E (Sum.elim x (V1 y)) ∈ Dc) with hS1def
  have hfib : T1.filter (fun x => Vf x = V1) ⊆ S1 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hS1def, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun y => ?_⟩
    have := hVf x hx.1 y
    rw [hx.2, mem_sec] at this
    exact this
  have hS1 : β / L * (K + 1) ^ n' ≤ (S1.card : ℝ) := by
    have h1 : ((T1.filter (fun x => Vf x = V1)).card : ℝ) ≤ S1.card := by
      exact_mod_cast Finset.card_le_card hfib
    have h2 : (0 : ℝ) ≤ (T1.filter (fun x => Vf x = V1)).card := Nat.cast_nonneg _
    have h3 : β * (K + 1) ^ n' ≤ L * S1.card := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hLpos]
    linarith
  set tile : ({i // i ∉ B} → Option α) → Subspace (Fin d) (Option α) ι :=
    fun x => Sub.comp E (Sub.constLeft x V1) with htiledef
  have htile : ∀ x y, tile x y = E (Sum.elim x (V1 y)) := by
    intro x y
    simp only [htiledef, Sub.comp_apply, Sub.constLeft_apply]
  have hinjE : ∀ x x' y y', E (Sum.elim x y) = E (Sum.elim x' y') → x = x' ∧ y = y' := by
    intro x x' y y' h
    have := Sub.injective E h
    exact ⟨funext fun o => by simpa using congrFun this (Sum.inl o),
      funext fun j => by simpa using congrFun this (Sum.inr j)⟩
  have tile_inj : Function.Injective tile := by
    intro x x' h
    have := congrArg (fun V : Subspace (Fin d) (Option α) ι => V (fun _ => none)) h
    simp only [htile] at this
    exact (hinjE _ _ _ _ this).1
  set Fn := S1.image tile with hFndef
  have hFn2 : (Fn : Set (Subspace (Fin d) (Option α) ι)).PairwiseDisjoint Sub.img := by
    intro V hV W hW hne
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hV
    obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hW
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨y, rfl⟩ := Sub.mem_img.1 hz1
    obtain ⟨y', hy'⟩ := Sub.mem_img.1 hz2
    rw [htile, htile] at hy'
    have := (hinjE _ _ _ _ hy').1
    exact hne (by rw [this])
  set U := Fn.biUnion Sub.img with hUdef
  have memU : ∀ z, z ∈ U ↔ ∃ x ∈ S1, ∃ y, E (Sum.elim x (V1 y)) = z := by
    intro z
    constructor
    · intro h
      obtain ⟨V, hV, hz⟩ := Finset.mem_biUnion.1 h
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hV
      obtain ⟨y, rfl⟩ := Sub.mem_img.1 hz
      exact ⟨x, hx, y, (htile x y).symm⟩
    · rintro ⟨x, hx, y, rfl⟩
      exact Finset.mem_biUnion.2 ⟨tile x, Finset.mem_image_of_mem _ hx,
        Sub.mem_img.2 ⟨y, htile x y⟩⟩
  refine ⟨S \ B, ?_, Fn, ?_, hFn2, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hBS]
    omega
  · intro V hV
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hV
    intro z hz
    obtain ⟨y, rfl⟩ := Sub.mem_img.1 hz
    rw [htile]
    exact (Finset.mem_filter.1 hx).2 y
  · rw [Finset.card_biUnion hFn2]
    have : ∀ V ∈ Fn, (Sub.img V).card = (Fintype.card α + 1) ^ d := by
      intro V _
      rw [Sub.card_img, Fintype.card_option, Fintype.card_fin]
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul,
      Finset.card_image_of_injective _ tile_inj]
    push_cast
    rw [← hcardO, pow_add]
    have hKM : 0 < (K + 1) ^ M1 := by positivity
    have hKd : 0 < (K + 1) ^ d := by positivity
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hKM]
    have := mul_le_mul_of_nonneg_right hS1 hKd.le
    calc _ = β / L * (K + 1) ^ n' * (K + 1) ^ d * (K + 1) ^ M1 := by ring
      _ ≤ S1.card * (K + 1) ^ d * (K + 1) ^ M1 := by
          exact mul_le_mul_of_nonneg_right this hKM.le
      _ = _ := by ring
  · have hDc' : InsensOn (S \ B) a Dc := hDc.mono Finset.sdiff_subset
    refine hDc'.sdiff ?_
    set colO : ({i // i ∉ B} → Option α) → ({i // i ∉ B} → Option α) :=
      fun x o => if o.1 ∈ S \ B then some ((x o).getD a) else x o with hcolO
    have key2 : ∀ x y, colS (S \ B) a (E (Sum.elim x y)) = E (Sum.elim (colO x) y) := by
      intro x y
      rw [hE, hE]
      funext i
      simp only [Function.comp_apply, colS]
      by_cases hi : i ∈ B
      · rw [he, splitB_of_mem B M1 hBcard hi]
        have : i ∉ S \ B := fun h => (Finset.mem_sdiff.1 h).2 hi
        simp [this]
      · rw [he, splitB_of_not_mem B M1 hBcard hi]
        simp [hcolO]
    have hS1inv : ∀ x, x ∈ S1 ↔ colO x ∈ S1 := by
      intro x
      simp only [hS1def, Finset.mem_filter, Finset.mem_univ, true_and]
      refine forall_congr' fun y => ?_
      rw [← key2]
      exact hDc' _
    have hdec : ∀ z : ι → Option α,
        E (Sum.elim (fun o => z (e.symm (Sum.inl o))) (fun j => z (e.symm (Sum.inr j)))) = z := by
      intro z
      rw [hE]
      funext i
      simp only [Function.comp_apply]
      rcases h : e i with o | j
      · simp only [Sum.elim_inl]
        rw [e.symm_apply_eq.2 h.symm]
      · simp only [Sum.elim_inr]
        rw [e.symm_apply_eq.2 h.symm]
    intro z
    constructor
    · intro hz
      rw [memU] at hz ⊢
      obtain ⟨x, hx, y, rfl⟩ := hz
      exact ⟨colO x, (hS1inv x).1 hx, y, (key2 x (V1 y)).symm⟩
    · intro hz
      rw [memU] at hz ⊢
      obtain ⟨x, hx, y, hxy⟩ := hz
      have h' := hxy
      rw [← hdec z, key2] at h'
      obtain ⟨h1, h2⟩ := hinjE _ _ _ _ h'
      refine ⟨fun o => z (e.symm (Sum.inl o)), (hS1inv _).2 (h1 ▸ hx), y, ?_⟩
      rw [h2]
      exact hdec z

/-- Lemma 12: insensitive sets can be tiled. -/
theorem lemma12 (hD : DHJProp α) (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ F : ℕ, ∀ (ι : Type) [Fintype ι], F ≤ Fintype.card ι →
      ∀ (a : α) (D : Finset (ι → Option α)), Insens a D → Tiles d D (2 * β) := by
  obtain ⟨M1, Θ, hΘ, hstep⟩ := tile_step hD d β hβ
  set J := ⌈1 / Θ⌉₊ with hJ
  refine ⟨J * M1, fun ι _ hι a D hDins => ?_⟩
  set N := ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι with hN
  have hNpos : 0 < N := by positivity
  have aux : ∀ j : ℕ, ∀ S : Finset ι, j * M1 ≤ S.card → ∀ Dc : Finset (ι → Option α),
      InsensOn S a Dc → (Dc.card : ℝ) ≤ j * Θ * N → Tiles d Dc (2 * β) := by
    intro j
    induction j with
    | zero =>
      intro S _ Dc _ hDc
      refine ⟨∅, by simp, by simp, ?_⟩
      simp only [Finset.biUnion_empty, Finset.sdiff_empty]
      push_cast at hDc
      have : (0 : ℝ) ≤ 2 * β * N := by positivity
      linarith
    | succ j ih =>
      intro S hS Dc hDcins hDc
      by_cases hsmall : (Dc.card : ℝ) < 2 * β * N
      · refine ⟨∅, by simp, by simp, ?_⟩
        simp only [Finset.biUnion_empty, Finset.sdiff_empty]
        linarith
      push_neg at hsmall
      obtain ⟨S', hS', Fn, hFn1, hFn2, hFn3, hFn4⟩ :=
        hstep ι S (by nlinarith) a Dc hDcins hsmall
      set U := Fn.biUnion Sub.img with hU
      have hUsub : U ⊆ Dc := Finset.biUnion_subset.2 hFn1
      have hcard' : ((Dc \ U).card : ℝ) ≤ j * Θ * N := by
        rw [Finset.card_sdiff_of_subset hUsub]
        have := Finset.card_le_card hUsub
        push_cast [this]
        push_cast at hDc
        nlinarith
      obtain ⟨F', hF'1, hF'2, hF'3⟩ := ih S' (by nlinarith) (Dc \ U) hFn4 hcard'
      refine ⟨F' ∪ Fn, ?_, ?_, ?_⟩
      · intro V hV
        rcases Finset.mem_union.1 hV with hV | hV
        · exact (hF'1 V hV).trans Finset.sdiff_subset
        · exact hFn1 V hV
      · rw [Finset.coe_union, Set.pairwiseDisjoint_union]
        refine ⟨hF'2, hFn2, fun V hV W hW _ => ?_⟩
        have h1 := hF'1 V hV
        have h2 : Sub.img W ⊆ U := Finset.subset_biUnion_of_mem _ hW
        rw [Finset.disjoint_left]
        intro z hz1 hz2
        have := h1 hz1
        rw [Finset.mem_sdiff] at this
        exact this.2 (h2 hz2)
      · have : Dc \ (F' ∪ Fn).biUnion Sub.img = (Dc \ U) \ F'.biUnion Sub.img := by
          ext z
          simp only [hU, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_union, or_and_right,
            exists_or]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨⟨h1, fun h => h2 (Or.inr h)⟩, fun h => h2 (Or.inl h)⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨h1, fun h => h.elim h3 h2⟩
        rw [this]
        exact hF'3
  apply aux J Finset.univ (by simpa using hι) D hDins
  have h1 : (1 : ℝ) ≤ J * Θ := by
    have : 1 / Θ ≤ (J : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hΘ] at this
    linarith
  have h2 : (D.card : ℝ) ≤ N := by
    have := card_le_pow D
    simpa [Fintype.card_option, hN] using this
  nlinarith

/-- Corollary 13: intersections of insensitive sets can be tiled. -/
theorem cor13 (hD : DHJProp α) (β : ℝ) (hβ : 0 < β) (R : Finset α) :
    ∀ d : ℕ, ∃ F : ℕ, ∀ (ι : Type) [Fintype ι], F ≤ Fintype.card ι →
      ∀ D : α → Finset (ι → Option α), (∀ a ∈ R, Insens a (D a)) →
        Tiles d (Finset.univ.filter (fun z => ∀ a ∈ R, z ∈ D a)) (2 * (R.card + 1) * β) := by
  refine Finset.induction_on R ?_ ?_
  · intro d
    obtain ⟨F, hF⟩ := lemma12 hD d β hβ
    refine ⟨F, fun ι _ hι D _ => ?_⟩
    obtain ⟨a0⟩ := ‹Nonempty α›
    have := hF ι hι a0 Finset.univ (insensOn_univ_set _ _)
    have h : Finset.univ.filter (fun z : ι → Option α => ∀ a ∈ (∅ : Finset α), z ∈ D a) =
        Finset.univ := by ext z; simp
    rw [h]
    simpa using this
  · intro b R hb ih d
    obtain ⟨F1, hF1⟩ := lemma12 hD d β hβ
    obtain ⟨F, hF⟩ := ih F1
    refine ⟨F, fun ι _ hι D hDins => ?_⟩
    obtain ⟨Fam1, h1, h2, h3⟩ := hF ι hι D (fun a ha => hDins a (Finset.mem_insert_of_mem ha))
    have hB : ∀ V : Subspace (Fin F1) (Option α) ι, Tiles d (pb (D b) V) (2 * β) :=
      fun V => hF1 (Fin F1) (by simp) b _ ((hDins b (Finset.mem_insert_self b R)).pb V)
    choose Bf hBf1 hBf2 hBf3 using hB
    set Fam := Fam1.biUnion (fun V => (Bf V).image (Sub.comp V)) with hFam
    refine ⟨Fam, ?_, ?_, ?_⟩
    · intro W hW
      obtain ⟨V, hV, hW'⟩ := Finset.mem_biUnion.1 hW
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hW'
      intro z hz
      obtain ⟨x, rfl⟩ := Sub.mem_img.1 hz
      rw [Sub.comp_apply]
      have hUx : U x ∈ pb (D b) V := hBf1 V U hU (Sub.mem_img.2 ⟨x, rfl⟩)
      have hVx := h1 V hV (Sub.mem_img.2 ⟨U x, rfl⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        forall_eq_or_imp] at hVx ⊢
      exact ⟨mem_pb.1 hUx, hVx⟩
    · intro W1 hW1 W2 hW2 hne
      obtain ⟨V1, hV1, hW1'⟩ := Finset.mem_biUnion.1 hW1
      obtain ⟨U1, hU1, rfl⟩ := Finset.mem_image.1 hW1'
      obtain ⟨V2, hV2, hW2'⟩ := Finset.mem_biUnion.1 hW2
      obtain ⟨U2, hU2, rfl⟩ := Finset.mem_image.1 hW2'
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      obtain ⟨x1, rfl⟩ := Sub.mem_img.1 hz1
      obtain ⟨x2, hx2⟩ := Sub.mem_img.1 hz2
      rw [Sub.comp_apply, Sub.comp_apply] at hx2
      by_cases hV : V1 = V2
      · subst hV
        have hx := Sub.injective V1 hx2
        by_cases hU : U1 = U2
        · exact hne (by rw [hU])
        · have hd := hBf2 V1 hU1 hU2 hU
          simp only [Function.onFun] at hd
          rw [Finset.disjoint_left] at hd
          exact hd (Sub.mem_img.2 ⟨x1, rfl⟩) (Sub.mem_img.2 ⟨x2, hx⟩)
      · have hd := h2 hV1 hV2 hV
        simp only [Function.onFun] at hd
        rw [Finset.disjoint_left] at hd
        exact hd (Sub.mem_img.2 ⟨U1 x1, rfl⟩) (Sub.mem_img.2 ⟨U2 x2, hx2⟩)
    · set D' := Finset.univ.filter (fun z : ι → Option α => ∀ a ∈ R, z ∈ D a) with hD'
      have claim : Finset.univ.filter (fun z : ι → Option α => ∀ a ∈ insert b R, z ∈ D a) \
          Fam.biUnion Sub.img ⊆ (D' \ Fam1.biUnion Sub.img) ∪
            Fam1.biUnion (fun V => (pb (D b) V \ (Bf V).biUnion Sub.img).image V) := by
        intro z hz
        rw [Finset.mem_sdiff] at hz
        obtain ⟨hz1, hz2⟩ := hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          forall_eq_or_imp] at hz1
        by_cases hzV : z ∈ Fam1.biUnion Sub.img
        · obtain ⟨V, hV, hzV⟩ := Finset.mem_biUnion.1 hzV
          obtain ⟨x, rfl⟩ := Sub.mem_img.1 hzV
          refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨V, hV, ?_⟩)
          refine Finset.mem_image.2 ⟨x, Finset.mem_sdiff.2 ⟨mem_pb.2 hz1.1, ?_⟩, rfl⟩
          intro hx
          obtain ⟨U, hU, hxU⟩ := Finset.mem_biUnion.1 hx
          obtain ⟨y, rfl⟩ := Sub.mem_img.1 hxU
          apply hz2
          refine Finset.mem_biUnion.2 ⟨Sub.comp V U, Finset.mem_biUnion.2 ⟨V, hV,
            Finset.mem_image_of_mem _ hU⟩, Sub.mem_img.2 ⟨y, Sub.comp_apply _ _ _⟩⟩
        · refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨?_, hzV⟩)
          simp only [hD', Finset.mem_filter, Finset.mem_univ, true_and]
          exact hz1.2
      have hN : (Finset.univ.filter (fun z : ι → Option α => ∀ a ∈ insert b R, z ∈ D a) \
          Fam.biUnion Sub.img).card ≤ (D' \ Fam1.biUnion Sub.img).card +
            ∑ V ∈ Fam1, (pb (D b) V \ (Bf V).biUnion Sub.img).card :=
        (Finset.card_le_card claim).trans ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left (Finset.card_biUnion_le.trans
            (Finset.sum_le_sum fun V _ => Finset.card_image_le)) _))
      have hR := (Nat.cast_le (α := ℝ)).2 hN
      push_cast at hR
      have e2 : ∑ V ∈ Fam1, ((pb (D b) V \ (Bf V).biUnion Sub.img).card : ℝ) ≤
          ∑ V ∈ Fam1, 2 * β * ((Fintype.card α : ℝ) + 1) ^ F1 :=
        Finset.sum_le_sum fun V _ => by simpa using hBf3 V
      rw [Finset.sum_const, nsmul_eq_mul] at e2
      have e4 : (Fam1.card : ℝ) * ((Fintype.card α : ℝ) + 1) ^ F1 ≤
          ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι := by
        have hc := Finset.card_biUnion h2
        have : ∀ V ∈ Fam1, (Sub.img V).card = (Fintype.card α + 1) ^ F1 := by
          intro V _
          rw [Sub.card_img, Fintype.card_option, Fintype.card_fin]
        rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul] at hc
        have hle := Finset.card_le_univ (Fam1.biUnion Sub.img)
        rw [hc, Fintype.card_fun, Fintype.card_option] at hle
        exact_mod_cast hle
      rw [Finset.card_insert_of_notMem hb]
      push_cast
      have := mul_le_mul_of_nonneg_left e4 (by positivity : (0 : ℝ) ≤ 2 * β)
      nlinarith

end

end Szem




/-!
# Density increment, part 2 (Lemma 10 and Corollary 11 of Dodos–Kanellopoulos–Tyros)

A line-free dense set with many lines in its `α`-part correlates with an intersection of
insensitive sets.
-/

open Combinatorics Finset

namespace Szem

noncomputable section

open Classical

/-- Pigeonhole for a partition: if the relative density of `q` in `p` is at least `δ + 6η`, some
part is large and has relative density at least `δ + 3η`. -/
theorem exists_good_part {ι' : Type*} [Fintype ι'] [Nonempty ι'] (p q : ι' → ℝ) (δ η : ℝ)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hq0 : ∀ i, 0 ≤ q i) (hqp : ∀ i, q i ≤ p i)
    (h : (δ + 6 * η) * ∑ i, p i ≤ ∑ i, q i) :
    ∃ i, 3 * η / Fintype.card ι' * ∑ j, p j ≤ p i ∧ (δ + 3 * η) * p i ≤ q i := by
  by_contra hcon
  push_neg at hcon
  set K := (Fintype.card ι' : ℝ)
  have hK : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hq0 i).trans (hqp i)
  have hlt : ∀ i, q i < (δ + 3 * η) * p i + 3 * η / K * ∑ j, p j := by
    intro i
    by_cases hi : 3 * η / K * ∑ j, p j ≤ p i
    · have := hcon i hi
      have : 0 ≤ 3 * η / K * ∑ j, p j := by
        have : 0 ≤ ∑ j, p j := Finset.sum_nonneg fun j _ => hp0 j
        positivity
      linarith
    · push_neg at hi
      have : 0 ≤ (δ + 3 * η) * p i := by have := hp0 i; positivity
      linarith [hqp i]
  have hsum : ∑ i, q i < ∑ i, ((δ + 3 * η) * p i + 3 * η / K * ∑ j, p j) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hlt i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have : (K : ℝ) * (3 * η / K * ∑ j, p j) = 3 * η * ∑ j, p j := by field_simp
  rw [this] at hsum
  linarith

variable {α : Type}

/-- The word of a line of `α^m` over `Option α`, with `none` at the variable coordinates. -/
def lineWord {m : ℕ} (ℓ : Subspace Unit α (Fin m)) : Fin m → Option α :=
  fun j => (ℓ.idxFun j).elim some (fun _ => none)

theorem colS_lineWord {m : ℕ} (ℓ : Subspace Unit α (Fin m)) (i : α) :
    colS Finset.univ i (lineWord ℓ) = some ∘ lpt ℓ i := by
  funext j
  simp only [colS_univ_apply, Function.comp_apply, lpt]
  rw [Subspace.coe_apply]
  rcases h : ℓ.idxFun j with a | u <;> simp [lineWord, h]

theorem lineWord_injective {m : ℕ} : Function.Injective (lineWord (α := α) (m := m)) := by
  intro ℓ ℓ' h
  ext j : 2
  have := congrFun h j
  simp only [lineWord] at this
  cases hℓ : ℓ.idxFun j <;> cases hℓ' : ℓ'.idxFun j <;> simp_all

/-- The line over `Option α` whose variable coordinates are the `none`-coordinates of `x`. -/
def noneLine {m : ℕ} (x : Fin m → Option α) (hn : ∃ j, x j = none) :
    Subspace Unit (Option α) (Fin m) where
  idxFun j := if x j = none then Sum.inr () else Sum.inl (x j)
  proper _ := ⟨hn.choose, by simp [hn.choose_spec]⟩

theorem lpt_noneLine {m : ℕ} (x : Fin m → Option α) (hn : ∃ j, x j = none) (c : Option α) :
    lpt (noneLine x hn) c = fun j => if x j = none then c else x j := by
  funext j
  simp only [lpt]
  rw [Subspace.coe_apply]
  by_cases h : x j = none <;> simp [noneLine, h]

/-- In a line-free set, points all of whose collapses lie in the set are `α`-points. -/
theorem mem_alpha_of_lineFree {m : ℕ} (A' : Finset (Fin m → Option α))
    (hnl : ∀ ℓ : Subspace Unit (Option α) (Fin m), ∃ c, lpt ℓ c ∉ A')
    (x : Fin m → Option α) (hx : x ∈ A') (hC : ∀ i, colS Finset.univ i x ∈ A') :
    ∀ j, x j ≠ none := by
  by_contra hn
  push_neg at hn
  obtain ⟨c, hc⟩ := hnl (noneLine x hn)
  apply hc
  rw [lpt_noneLine]
  rcases c with _ | i
  · convert hx using 1
    funext j
    by_cases h : x j = none <;> simp [h]
  · convert hC i using 1
    funext j
    simp only [colS_univ_apply]
    rcases h : x j with _ | v <;> simp

/-- The pieces of the partition of the complement of `⋂ C i` along an enumeration of `α`. -/
def partPiece [Fintype α] {X : Type*} [Fintype X] (C : α → Finset X) (i : α) : Finset X :=
  Finset.univ.filter (fun x => x ∉ C i ∧ ∀ j, Fintype.equivFin α j < Fintype.equivFin α i → x ∈ C j)

theorem partPiece_disjoint [Fintype α] {X : Type*} [Fintype X] (C : α → Finset X) :
    ((Finset.univ : Finset α) : Set α).PairwiseDisjoint (partPiece C) := by
  intro i _ i' _ hne
  show Disjoint _ _
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [partPiece, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  have hne' : Fintype.equivFin α i ≠ Fintype.equivFin α i' :=
    fun h => hne ((Fintype.equivFin α).injective h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact hx.1 (hx'.2 i h)
  · exact hx'.1 (hx.2 i' h)

theorem mem_biUnion_partPiece [Fintype α] {X : Type*} [Fintype X] [DecidableEq X]
    (C : α → Finset X) (x : X) :
    x ∈ Finset.univ.biUnion (partPiece C) ↔ ∃ i, x ∉ C i := by
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, partPiece]
  constructor
  · rintro ⟨i, hi, -⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun i => x ∉ C i))
      (fun i => Fintype.equivFin α i) ⟨i, by simp [hi]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hmin
    refine ⟨j, hj, fun k hk => ?_⟩
    by_contra hk'
    exact absurd (hmin k hk') (not_le.2 hk)

variable [Fintype α] [Nonempty α]

set_option maxHeartbeats 1000000 in
/-- The combined Lemma 10 / Corollary 11 (structural part). -/
theorem struct_lemma {m : ℕ} (A' : Finset (Fin m → Option α))
    (hnl : ∀ ℓ : Subspace Unit (Option α) (Fin m), ∃ c, lpt ℓ c ∉ A')
    (δ δ₀ η θ' : ℝ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (hδ : δ₀ ≤ δ) (hθ' : 0 < θ') (hθ'1 : θ' ≤ 1)
    (hη : η = δ₀ * θ' / 48)
    (hA : (δ - 2 * η) * ((Fintype.card α : ℝ) + 1) ^ m ≤ A'.card)
    (hL : θ' / 2 * ((Fintype.card α : ℝ) + 1) ^ m ≤
      ((Finset.univ.filter (fun ℓ : Subspace Unit α (Fin m) =>
        ∀ a : α, some ∘ lpt ℓ a ∈ A')).card : ℝ))
    (hm : (Fintype.card α : ℝ) ^ m ≤ η * ((Fintype.card α : ℝ) + 1) ^ m) :
    ∃ D : α → Finset (Fin m → Option α), (∀ a, Insens a (D a)) ∧
      δ₀ * η ^ 2 / (2 * Fintype.card α) * ((Fintype.card α : ℝ) + 1) ^ m ≤
        ((Finset.univ.filter (fun z => ∀ a, z ∈ D a)).card : ℝ) ∧
      (δ + δ₀ * η ^ 2 / (2 * Fintype.card α)) *
        ((Finset.univ.filter (fun z => ∀ a, z ∈ D a)).card : ℝ) ≤
        ((A' ∩ Finset.univ.filter (fun z => ∀ a, z ∈ D a)).card : ℝ) := by
  set K := (Fintype.card α : ℝ) with hK
  have hK1 : 1 ≤ K := Nat.one_le_cast.mpr Fintype.card_pos
  set N := (K + 1) ^ m with hN
  have hNpos : 0 < N := by positivity
  have hηpos : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ δ₀ / 48 := by rw [hη]; nlinarith
  set C : α → Finset (Fin m → Option α) :=
    fun i => Finset.univ.filter (fun x => colS Finset.univ i x ∈ A') with hC
  have hCins : ∀ i, Insens i (C i) := by
    intro i x
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [colS_colS_of_subset (subset_refl _)]
  set Call := Finset.univ.filter (fun x : Fin m → Option α => ∀ i, x ∈ C i) with hCall
  set good := Finset.univ.filter (fun ℓ : Subspace Unit α (Fin m) =>
    ∀ a : α, some ∘ lpt ℓ a ∈ A') with hgood
  have hgoodC : good.image lineWord ⊆ Call := by
    intro x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hx
    simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    simp only [hCall, hC, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [colS_lineWord]
    exact hℓ i
  have hCallcard : θ' / 2 * N ≤ (Call.card : ℝ) := by
    have h1 := Finset.card_le_card hgoodC
    rw [Finset.card_image_of_injective _ lineWord_injective] at h1
    have h2 : (good.card : ℝ) ≤ Call.card := by exact_mod_cast h1
    linarith
  have hAC : A' ∩ Call ⊆ Finset.univ.image (fun w : Fin m → α => some ∘ w) := by
    intro x hx
    rw [Finset.mem_inter] at hx
    have hC' : ∀ i, colS Finset.univ i x ∈ A' := by
      intro i
      have := (Finset.mem_filter.1 hx.2).2 i
      simpa [hC] using this
    have hn := mem_alpha_of_lineFree A' hnl x hx.1 hC'
    refine Finset.mem_image.2 ⟨fun j => (x j).getD (Classical.arbitrary α), Finset.mem_univ _, ?_⟩
    funext j
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hn j)
    simp [hv]
  have hACcard : ((A' ∩ Call).card : ℝ) ≤ η * N := by
    have h1 := (Finset.card_le_card hAC).trans Finset.card_image_le
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1
    have h2 : ((A' ∩ Call).card : ℝ) ≤ K ^ m := by rw [hK]; exact_mod_cast h1
    linarith
  set U := Finset.univ.filter (fun x : Fin m → Option α => ∃ i, x ∉ C i) with hU
  have hUCall : U = Finset.univ \ Call := by
    ext x; simp [hU, hCall]
  have hUcard : (U.card : ℝ) = N - Call.card := by
    rw [hUCall, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
    have := Finset.card_le_univ Call
    rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin] at this
    push_cast [this]
    rfl
  have hAsplit : (A'.card : ℝ) = (A' ∩ Call).card + (A' ∩ U).card := by
    rw [hUCall]
    have := Finset.card_inter_add_card_sdiff A' Call
    have h2 : A' \ Call = A' ∩ (Finset.univ \ Call) := by ext x; simp
    rw [h2] at this
    exact_mod_cast this.symm
  have hAU : (δ - 3 * η) * N ≤ ((A' ∩ U).card : ℝ) := by linarith
  have hAU2 : (δ + 6 * η) * U.card ≤ ((A' ∩ U).card : ℝ) := by
    rw [hUcard]
    have hkey : (δ + 6 * η) * θ' / 2 ≥ 9 * η := by rw [hη]; nlinarith
    have : (δ + 6 * η) * (N - Call.card) ≤ (δ + 6 * η) * (N - θ' / 2 * N) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    nlinarith
  -- the partition
  set P := partPiece C with hP
  have hPdisj := partPiece_disjoint C
  have hbU : Finset.univ.biUnion P = U := by
    ext x
    rw [hP, mem_biUnion_partPiece, hU, Finset.mem_filter]
    simp
  have hsumP : ∑ i, ((P i).card : ℝ) = U.card := by
    rw [← hbU, Finset.card_biUnion hPdisj]
    push_cast
    rfl
  have hsumAP : ∑ i, ((A' ∩ P i).card : ℝ) = (A' ∩ U).card := by
    rw [← hbU, Finset.inter_biUnion, Finset.card_biUnion]
    · push_cast; rfl
    · intro i hi j hj hij
      show Disjoint _ _
      exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right (hPdisj hi hj hij))
  obtain ⟨i, hi1, hi2⟩ := exists_good_part (fun i => ((P i).card : ℝ))
    (fun i => ((A' ∩ P i).card : ℝ)) δ η hηpos.le (by linarith) (fun i => Nat.cast_nonneg _)
    (fun i => Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right))
    (by rw [hsumP, hsumAP]; exact hAU2)
  try simp only at hi1 hi2
  rw [hsumP] at hi1
  set e := Fintype.equivFin α
  refine ⟨fun j => if e j < e i then C j else if j = i then Finset.univ \ C i else Finset.univ,
    ?_, ?_⟩
  · intro j
    beta_reduce
    split_ifs with h1 h2
    · exact hCins j
    · subst h2; exact (hCins _).compl
    · exact insensOn_univ_set _ _
  have hDall : Finset.univ.filter (fun z => ∀ j, z ∈ (if e j < e i then C j else
      if j = i then Finset.univ \ C i else Finset.univ)) = P i := by
    ext x
    simp only [hP, partPiece, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨?_, fun j hj => ?_⟩
      · have := h i
        rw [if_neg (lt_irrefl _), if_pos rfl, Finset.mem_sdiff] at this
        exact this.2
      · have := h j
        rw [if_pos hj] at this
        exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : e j < e i
      · rw [if_pos hj]; exact h2 j hj
      · rw [if_neg hj]
        by_cases hj' : j = i
        · subst hj'; rw [if_pos rfl, Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, h1⟩
        · rw [if_neg hj']; exact Finset.mem_univ _
  rw [hDall]
  have hγ1 : δ₀ * η ^ 2 / (2 * K) ≤ 3 * η := by
    rw [div_le_iff₀ (by positivity)]
    have : η ≤ 1 := by linarith
    have : δ₀ ≤ 48 := by linarith
    nlinarith
  refine ⟨?_, ?_⟩
  · have hU' : (δ - 3 * η) * N ≤ U.card := hAU.trans (by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
    have h3 : 3 * η / K * ((δ - 3 * η) * N) ≤ 3 * η / K * U.card :=
      mul_le_mul_of_nonneg_left hU' (by positivity)
    have h4 : δ₀ * η ^ 2 / (2 * K) * N ≤ 3 * η / K * ((δ - 3 * η) * N) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 3 * η * ((δ - 3 * η) * N) * (2 * K) - δ₀ * η ^ 2 * N * K =
          η * N * K * (6 * δ - 18 * η - δ₀ * η) := by ring
      have h5 : 0 ≤ 6 * δ - 18 * η - δ₀ * η := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hηpos.le hNpos.le) (by linarith : (0:ℝ) ≤ K)) h5]
    linarith
  · have := mul_le_mul_of_nonneg_right (by linarith : δ + δ₀ * η ^ 2 / (2 * K) ≤ δ + 3 * η)
      (Nat.cast_nonneg (P i).card : (0 : ℝ) ≤ (P i).card)
    linarith


end

end Szem




/-!
# The density Hales–Jewett theorem

Proposition 6 of Dodos–Kanellopoulos–Tyros, the density increment iteration, and the induction on
the size of the alphabet.
-/

open Combinatorics Finset

namespace Szem

noncomputable section

open Classical

/-- The number of points of `A` in a subspace equals the size of the pullback. -/
theorem card_pb_eq {α ι η : Type*} [Fintype α] [Fintype η] [DecidableEq η]
    [DecidableEq (ι → α)] (A : Finset (ι → α)) (V : Subspace η α ι) :
    (pb A V).card = (A ∩ Sub.img V).card := by
  rw [← Finset.card_image_of_injective (pb A V) (Sub.injective V)]
  congr 1
  ext z
  simp only [Finset.mem_image, mem_pb, Finset.mem_inter, Sub.mem_img]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x, rfl⟩
  · rintro ⟨hz, x, rfl⟩
    exact ⟨x, hz, rfl⟩

/-- A line in a pullback gives a line in the set. -/
theorem line_of_pb {α ι η : Type*} [Fintype α] [Fintype η] [DecidableEq η]
    (A : Finset (ι → α)) (V : Subspace η α ι) (ℓ : Subspace Unit α η)
    (h : ∀ c, lpt ℓ c ∈ pb A V) : ∀ c, lpt (Sub.comp V ℓ) c ∈ A := by
  intro c
  have := h c
  rw [mem_pb] at this
  simpa [lpt] using this

/-- Averaging over a tiling. -/
theorem tiling_average {α : Type} [Fintype α] [Nonempty α] {ι : Type} [Fintype ι] (d : ℕ)
    (A' Dall : Finset (ι → Option α)) (δ γ ε : ℝ) (hδ : 0 ≤ δ) (hγ : 0 < γ)
    (hε : ε ≤ γ ^ 2 / 2)
    (hD1 : γ * ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι ≤ Dall.card)
    (hD2 : (δ + γ) * Dall.card ≤ (A' ∩ Dall).card)
    (hT : Tiles d Dall ε) :
    ∃ V : Subspace (Fin d) (Option α) ι,
      (δ + γ / 2) * ((Fintype.card α : ℝ) + 1) ^ d ≤ (A' ∩ Sub.img V).card := by
  obtain ⟨Fam, h1, h2, h3⟩ := hT
  set N := ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι with hN
  set Kd := ((Fintype.card α : ℝ) + 1) ^ d with hKd
  have hNpos : 0 < N := by positivity
  set T := Fam.biUnion Sub.img with hTdef
  have hTD : T ⊆ Dall := Finset.biUnion_subset.2 h1
  have hTcard : (T.card : ℝ) = Fam.card * Kd := by
    rw [Finset.card_biUnion h2]
    have : ∀ V ∈ Fam, (Sub.img V).card = (Fintype.card α + 1) ^ d := by
      intro V _
      rw [Sub.card_img, Fintype.card_option, Fintype.card_fin]
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
    push_cast
    rfl
  have hAT : ((A' ∩ T).card : ℝ) = ∑ V ∈ Fam, ((A' ∩ Sub.img V).card : ℝ) := by
    rw [Finset.inter_biUnion, Finset.card_biUnion]
    · push_cast; rfl
    · intro V hV W hW hVW
      show Disjoint _ _
      exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right (h2 hV hW hVW))
  have hsplit : ((A' ∩ Dall).card : ℝ) ≤ (A' ∩ T).card + (Dall \ T).card := by
    have : A' ∩ Dall ⊆ (A' ∩ T) ∪ (Dall \ T) := by
      intro z hz
      rw [Finset.mem_inter] at hz
      by_cases hzT : z ∈ T
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hz.1, hzT⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hz.2, hzT⟩)
    have := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
    exact_mod_cast this
  have hTle : (T.card : ℝ) ≤ Dall.card := by exact_mod_cast Finset.card_le_card hTD
  have herr : ((Dall \ T).card : ℝ) ≤ γ ^ 2 / 2 * N :=
    h3.trans (mul_le_mul_of_nonneg_right hε hNpos.le)
  have hγD : γ ^ 2 / 2 * N ≤ γ / 2 * Dall.card := by nlinarith
  have key0 : (δ + γ / 2) * Dall.card ≤ (A' ∩ T).card := by nlinarith
  have key : (δ + γ / 2) * T.card ≤ (A' ∩ T).card := by
    have : (δ + γ / 2) * T.card ≤ (δ + γ / 2) * Dall.card :=
      mul_le_mul_of_nonneg_left hTle (by positivity)
    linarith
  have hDpos : 0 < (Dall.card : ℝ) := lt_of_lt_of_le (by positivity) hD1
  have hne : Fam.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : T = ∅ := by rw [hTdef, h, Finset.biUnion_empty]
    rw [this, Finset.inter_empty, Finset.card_empty, Nat.cast_zero] at key0
    have : 0 < (δ + γ / 2) * Dall.card := by positivity
    linarith
  obtain ⟨V, -, hle⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (δ + γ / 2) * Kd) (g := fun V => ((A' ∩ Sub.img V).card : ℝ)) (by
      rw [Finset.sum_const, nsmul_eq_mul, ← hAT]
      rw [hTcard] at key
      linarith)
  exact ⟨V, hle⟩

section Opt

variable {α : Type} [Fintype α] [Nonempty α]

set_option maxHeartbeats 1000000 in
/-- Proposition 6: the density increment dichotomy. -/
theorem prop6 (hD : DHJProp α) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ d : ℕ, ∃ N : ℕ, ∀ δ : ℝ, δ₀ ≤ δ → ∀ (ι : Type) [Fintype ι],
      N ≤ Fintype.card ι → ∀ A : Finset (ι → Option α),
        δ * ((Fintype.card α : ℝ) + 1) ^ Fintype.card ι ≤ A.card →
        (∃ ℓ : Subspace Unit (Option α) ι, ∀ c, lpt ℓ c ∈ A) ∨
        ∃ V : Subspace (Fin d) (Option α) ι,
          (δ + γ / 2) * ((Fintype.card α : ℝ) + 1) ^ d ≤ (pb A V).card := by
  set K := (Fintype.card α : ℝ) with hK
  have hK1 : 1 ≤ K := Nat.one_le_cast.mpr Fintype.card_pos
  obtain ⟨N0', hN0'⟩ := hD (δ₀ / 4) (by positivity)
  set N0 := max N0' 1 with hN0def
  have hN0pos : 0 < N0 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hN0 : ∀ (ι : Type) [Fintype ι], N0 ≤ Fintype.card ι → ∀ A : Finset (ι → α),
      δ₀ / 4 * K ^ Fintype.card ι ≤ A.card → ∃ ℓ : Subspace Unit α ι, ∀ a, lpt ℓ a ∈ A :=
    fun ι _ h A hA => hN0' ι (le_trans (le_max_left _ _) h) A hA
  haveI : Nonempty (Fin N0) := ⟨⟨0, hN0pos⟩⟩
  set L0 := (Fintype.card (Subspace Unit α (Fin N0)) : ℝ) with hL0
  have hL01 : 1 ≤ L0 := Nat.one_le_cast.mpr Fintype.card_pos
  have hL0pos : 0 < L0 := by linarith
  set θ := δ₀ / 4 / L0 with hθdef
  have hθpos : 0 < θ := by positivity
  have hθ : θ * L0 ≤ δ₀ / 4 := by rw [hθdef, div_mul_cancel₀ _ hL0pos.ne']
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one hL0pos]
    linarith
  have hKN0 : 1 ≤ (K + 1) ^ N0 := one_le_pow₀ (by linarith)
  set θ' := θ / (K + 1) ^ N0 with hθ'def
  have hθ'pos : 0 < θ' := by positivity
  have hθ'1 : θ' ≤ 1 := by
    rw [hθ'def, div_le_one (by positivity)]
    linarith
  set η := δ₀ * θ' / 48 with hηdef
  have hηpos : 0 < η := by positivity
  have hηθ : η < θ' := by rw [hηdef]; nlinarith
  have hη1 : η ≤ 1 / 48 := by rw [hηdef]; nlinarith
  set γ := δ₀ * η ^ 2 / (2 * K) with hγdef
  have hγpos : 0 < γ := by positivity
  have hγ1 : γ ≤ η ^ 2 / 2 := by
    rw [hγdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ η ^ 2 := sq_nonneg η
    nlinarith
  refine ⟨γ, hγpos, fun d => ?_⟩
  set β := γ ^ 2 / (4 * (K + 1)) with hβdef
  have hβpos : 0 < β := by positivity
  obtain ⟨F, hF⟩ := cor13 hD β hβpos Finset.univ d
  obtain ⟨m1, hm1⟩ := exists_pow_lt_of_lt_one hηpos
    (show K / (K + 1) < 1 by rw [div_lt_one (by positivity)]; linarith)
  set m := max (max N0 F) m1 with hmdef
  have hmN0 : N0 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hmF : F ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmK : K ^ m ≤ η * (K + 1) ^ m := by
    have h1 : (K / (K + 1)) ^ m ≤ (K / (K + 1)) ^ m1 :=
      pow_le_pow_of_le_one (by positivity) (by rw [div_le_one (by positivity)]; linarith)
        (le_max_right _ _)
    have h2 : K ^ m / (K + 1) ^ m ≤ η := by
      rw [← div_pow]
      exact h1.trans hm1.le
    rwa [div_le_iff₀ (by positivity)] at h2
  obtain ⟨N, hN⟩ := lemma8 δ₀ η θ hδ₀ hηpos N0 hN0pos hN0 hθ hηθ m hmN0
  refine ⟨N, fun δ hδ ι _ hι A hA => ?_⟩
  by_cases hline : ∃ ℓ : Subspace Unit (Option α) ι, ∀ c, lpt ℓ c ∈ A
  · exact Or.inl hline
  right
  push_neg at hline
  have hη2 : η ^ 2 ≤ δ := by nlinarith
  obtain ⟨W, D, hDins, hD1, hD2⟩ : ∃ (W : Subspace (Fin m) (Option α) ι)
      (D : α → Finset (Fin m → Option α)), (∀ a, Insens a (D a)) ∧
      γ * (K + 1) ^ m ≤ ((Finset.univ.filter (fun z => ∀ a, z ∈ D a)).card : ℝ) ∧
      (δ + γ) * ((Finset.univ.filter (fun z => ∀ a, z ∈ D a)).card : ℝ) ≤
        ((pb A W ∩ Finset.univ.filter (fun z => ∀ a, z ∈ D a)).card : ℝ) := by
    rcases hN δ hδ hη2 ι hι A hA with ⟨X, hX⟩ | ⟨W, hW1, hW2⟩
    · have hfu : Finset.univ.filter (fun z : Fin m → Option α =>
          ∀ a : α, z ∈ (Finset.univ : Finset (Fin m → Option α))) = Finset.univ := by
        ext z; simp
      refine ⟨X, fun _ => Finset.univ, fun a => insensOn_univ_set _ _, ?_, ?_⟩
      · rw [hfu, Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
        push_cast
        have hη21 : η ^ 2 ≤ 1 := by
          have : η ^ 2 ≤ η * 1 := by rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) hηpos.le
          linarith
        have hγ' : γ ≤ 1 := by linarith
        have : 0 < (K + 1) ^ m := by positivity
        linarith [mul_le_mul_of_nonneg_right hγ' this.le]
      · rw [hfu, Finset.inter_univ, Finset.card_univ, Fintype.card_fun, Fintype.card_option,
          Fintype.card_fin]
        push_cast
        have : (δ + γ) * (K + 1) ^ m ≤ (δ + η ^ 2 / 2) * (K + 1) ^ m :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
    · have hnl : ∀ ℓ : Subspace Unit (Option α) (Fin m), ∃ c, lpt ℓ c ∉ pb A W := by
        intro ℓ
        by_contra hc
        push_neg at hc
        obtain ⟨c, hc'⟩ := hline (Sub.comp W ℓ)
        exact hc' (line_of_pb A W ℓ hc c)
      have hfl : Finset.univ.filter (fun ℓ : Subspace Unit α (Fin m) =>
          ∀ a : α, some ∘ lpt ℓ a ∈ pb A W) = Finset.univ.filter (fun ℓ : Subspace Unit α (Fin m) =>
          ∀ a : α, W (some ∘ lpt ℓ a) ∈ A) := by
        ext ℓ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_pb]
      obtain ⟨D, h1, h2, h3⟩ := struct_lemma (pb A W) hnl δ δ₀ η θ' hδ₀ hδ₀1 hδ hθ'pos hθ'1
        rfl hW1 (by rw [hfl]; exact hW2) hmK
      exact ⟨W, D, h1, h2, h3⟩
  have hT := hF (Fin m) (by simpa using hmF) D (fun a _ => hDins a)
  replace hT : Tiles d (Finset.univ.filter (fun z : Fin m → Option α => ∀ a, z ∈ D a))
      (2 * ((Finset.univ : Finset α).card + 1) * β) := by
    convert hT using 2 <;> ext z <;> simp
  have hε : 2 * ((Finset.univ : Finset α).card + 1) * β ≤ γ ^ 2 / 2 := by
    rw [Finset.card_univ, hβdef]
    rw [← hK]
    have : (0 : ℝ) < K + 1 := by positivity
    apply le_of_eq
    field_simp
    try ring
  obtain ⟨V, hV⟩ := tiling_average d (pb A W) _ δ γ _ (by linarith) hγpos hε
    (by simpa using hD1) hD2 hT
  refine ⟨Sub.comp W V, ?_⟩
  rw [pb_comp, card_pb_eq]
  exact hV

/-- The induction step: DHJ for `α` implies DHJ for `Option α`. -/
theorem dhj_option (hD : DHJProp α) : DHJProp (Option α) := by
  intro δ hδ
  set δ₀ := min δ 1 with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min hδ one_pos
  have hδ₀1 : δ₀ ≤ 1 := min_le_right _ _
  obtain ⟨γ, hγ, hP⟩ := prop6 hD δ₀ hδ₀ hδ₀1
  choose Nf hNf using hP
  set K := (Fintype.card α : ℝ) with hK
  let Ns : ℕ → ℕ := fun j => Nat.rec (motive := fun _ => ℕ) 0 (fun _ n => Nf n) j
  have claim : ∀ j : ℕ, ∀ δ' : ℝ, δ₀ ≤ δ' → 1 < δ' + j * (γ / 2) → ∀ (ι : Type) [Fintype ι],
      Ns j ≤ Fintype.card ι → ∀ A : Finset (ι → Option α),
        δ' * (K + 1) ^ Fintype.card ι ≤ A.card →
        ∃ ℓ : Subspace Unit (Option α) ι, ∀ c, lpt ℓ c ∈ A := by
    intro j
    induction j with
    | zero =>
      intro δ' _ h1 ι _ _ A hA
      exfalso
      have := card_le_pow A
      rw [Fintype.card_option] at this
      push_cast at this
      simp only [CharP.cast_eq_zero, zero_mul, add_zero] at h1
      have hp : 0 < (K + 1) ^ Fintype.card ι := by positivity
      nlinarith
    | succ j ih =>
      intro δ' hδ' h1 ι _ hι A hA
      rcases hNf (Ns j) δ' hδ' ι hι A hA with h | ⟨V, hV⟩
      · exact h
      · obtain ⟨ℓ, hℓ⟩ := ih (δ' + γ / 2) (by linarith) (by push_cast at h1; linarith)
          (Fin (Ns j)) (by simp) (pb A V) (by simpa using hV)
        exact ⟨Sub.comp V ℓ, line_of_pb A V ℓ hℓ⟩
  set J := ⌈2 / γ⌉₊ + 1 with hJ
  refine ⟨Ns J, fun ι _ hι A hA => ?_⟩
  refine claim J δ₀ le_rfl ?_ ι hι A ?_
  · have h1 : 2 / γ ≤ (⌈2 / γ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (J : ℝ) = ⌈2 / γ⌉₊ + 1 := by rw [hJ]; push_cast; ring
    have h3 : 2 / γ * (γ / 2) = 1 := by field_simp
    rw [h2]
    nlinarith
  · rw [Fintype.card_option] at hA
    push_cast at hA
    have : δ₀ ≤ δ := min_le_left _ _
    have hp : 0 < (K + 1) ^ Fintype.card ι := by positivity
    nlinarith

end Opt

/-- Transfer of DHJ along an equivalence of alphabets. -/
theorem dhj_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (hD : DHJProp α) :
    DHJProp β := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hD δ hδ
  refine ⟨N, fun ι _ hι A hA => ?_⟩
  have hinj : Function.Injective (fun x : ι → β => e.symm ∘ x) := fun x y h => by
    funext i
    have := congrFun h i
    simpa using this
  obtain ⟨ℓ, hℓ⟩ := hN ι hι (A.image (fun x => e.symm ∘ x)) (by
    rw [Finset.card_image_of_injective _ hinj, Fintype.card_congr e]
    exact hA)
  refine ⟨Sub.map e ℓ, fun b => ?_⟩
  obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 (hℓ (e.symm b))
  have h1 : lpt (Sub.map e ℓ) b = e ∘ lpt ℓ (e.symm b) := by
    show Sub.map e ℓ (fun _ => b) = _
    rw [show (fun _ : Unit => b) = e ∘ (fun _ => e.symm b) by funext; simp, Sub.map_apply]
  have : lpt (Sub.map e ℓ) b = x := by
    rw [h1, ← hxe]
    funext i
    simp
  rw [this]
  exact hx

/-- DHJ for a one-letter alphabet. -/
theorem dhj_fin_one : DHJProp (Fin 1) := by
  intro δ hδ
  refine ⟨1, fun ι _ hι A hA => ?_⟩
  haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hpos : 0 < A.card := by
    have : (0 : ℝ) < δ * (Fintype.card (Fin 1) : ℝ) ^ Fintype.card ι := by positivity
    exact_mod_cast this.trans_le hA
  obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
  refine ⟨diagLine (Fin 1) ι, fun a => ?_⟩
  have : lpt (diagLine (Fin 1) ι) a = x := Subsingleton.elim _ _
  rw [this]
  exact hx

/-- The density Hales–Jewett theorem for the alphabets `Fin (n + 1)`. -/
theorem dhj_fin (n : ℕ) : DHJProp (Fin (n + 1)) := by
  induction n with
  | zero => exact dhj_fin_one
  | succ n ih => exact dhj_equiv (finSuccEquiv (n + 1)).symm (dhj_option ih)

end

end Szem




/-!
# Szemerédi's theorem

Szemerédi's theorem is deduced from the density Hales–Jewett theorem for the alphabet `Fin k`:
the map sending a word to the sum of its letters sends combinatorial lines to `k`-term
arithmetic progressions, and an averaging argument over translates transfers density.
-/

open Combinatorics Finset

namespace Szem

noncomputable section

open Classical

/-- The sum of the letters of a word. -/
def wsum {n k : ℕ} (w : Fin n → Fin k) : ℕ := ∑ j, (w j : ℕ)

theorem wsum_le {n k : ℕ} (w : Fin n → Fin k) : wsum w ≤ n * k := by
  unfold wsum
  calc ∑ j, (w j : ℕ) ≤ ∑ _j : Fin n, k := Finset.sum_le_sum fun j _ => (w j).isLt.le
    _ = n * k := by simp

/-- Along a combinatorial line, the letter sum is an affine function of the letter. -/
theorem wsum_lpt {n k : ℕ} (ℓ : Subspace Unit (Fin k) (Fin n)) (a : Fin k) :
    wsum (lpt ℓ a) = (∑ j, Sum.elim (fun c : Fin k => (c : ℕ)) (fun _ : Unit => 0) (ℓ.idxFun j)) +
      (Finset.univ.filter (fun j => ℓ.idxFun j = Sum.inr ())).card * a := by
  unfold wsum
  have h : ∀ j, ((lpt ℓ a j : Fin k) : ℕ) =
      Sum.elim (fun c : Fin k => (c : ℕ)) (fun _ : Unit => 0) (ℓ.idxFun j) +
      (if ℓ.idxFun j = Sum.inr () then (a : ℕ) else 0) := by
    intro j
    simp only [lpt]
    rw [Subspace.coe_apply]
    rcases hj : ℓ.idxFun j with c | u <;> simp
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]

/-- Szemerédi's theorem, combinatorial form: dense subsets of `{1, …, N}` contain `k`-term
arithmetic progressions with positive common difference. -/
theorem szemeredi_ap (k : ℕ) (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → δ * N ≤ A.card →
      ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n, hn⟩ := dhj_fin k' (δ / 4) (by positivity)
  set M := n * (k' + 1) with hM
  refine ⟨⌈2 * M / δ⌉₊ + 1, fun N hN A hA hAcard => ?_⟩
  have hNpos : 0 < N := by omega
  have hMN : (M : ℝ) ≤ δ / 2 * N := by
    have h1 : 2 * (M : ℝ) / δ ≤ (⌈2 * (M : ℝ) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 * (M : ℝ) / δ⌉₊ : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hN
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  set B : ℕ → Finset (Fin n → Fin (k' + 1)) :=
    fun x => Finset.univ.filter (fun w => x + wsum w ∈ A) with hB
  have hcount : ∀ w : Fin n → Fin (k' + 1),
      (A.card : ℝ) - M ≤ ((Finset.range (N + 1)).filter (fun x => x + wsum w ∈ A)).card := by
    intro w
    have h1 : (A.filter (fun a => wsum w ≤ a)).image (fun a => a - wsum w) ⊆
        (Finset.range (N + 1)).filter (fun x => x + wsum w ∈ A) := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_filter] at ha ⊢
      have := Finset.mem_Icc.1 (hA ha.1)
      refine ⟨Finset.mem_range.2 (by omega), ?_⟩
      rw [Nat.sub_add_cancel ha.2]
      exact ha.1
    have h2 : ((A.filter (fun a => wsum w ≤ a)).image (fun a => a - wsum w)).card =
        (A.filter (fun a => wsum w ≤ a)).card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      simp only at hab
      omega
    have h3 : A.card ≤ (A.filter (fun a => wsum w ≤ a)).card + M := by
      have h5 := Finset.card_filter_add_card_filter_not (s := A) (fun a => wsum w ≤ a)
      have h4 : (A.filter (fun a => ¬ wsum w ≤ a)).card ≤ M := by
        calc (A.filter (fun a => ¬ wsum w ≤ a)).card ≤ (Finset.range (wsum w)).card :=
              Finset.card_le_card (fun a ha => by
                rw [Finset.mem_filter] at ha
                rw [Finset.mem_range]
                omega)
          _ = wsum w := Finset.card_range _
          _ ≤ M := wsum_le w
      omega
    have h6 := Finset.card_le_card h1
    rw [h2] at h6
    have h7 : A.card ≤ ((Finset.range (N + 1)).filter (fun x => x + wsum w ∈ A)).card + M := by omega
    have h8 : (A.card : ℝ) ≤ ((Finset.range (N + 1)).filter (fun x => x + wsum w ∈ A)).card + M := by
      exact_mod_cast h7
    linarith
  have hsum : ∑ x ∈ Finset.range (N + 1), ((B x).card : ℝ) = ∑ w : Fin n → Fin (k' + 1),
      (((Finset.range (N + 1)).filter (fun x => x + wsum w ∈ A)).card : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    congr 1
    simp only [hB, Finset.card_filter]
    rw [Finset.sum_comm]
  have hlow : (δ / 4 * ((k' : ℝ) + 1) ^ n) * (N + 1) ≤ ∑ x ∈ Finset.range (N + 1), ((B x).card : ℝ) := by
    rw [hsum]
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin n → Fin (k' + 1)))
      (fun w => (((Finset.range (N + 1)).filter (fun x => x + wsum w ∈ A)).card : ℝ))
      ((A.card : ℝ) - M) (fun w _ => hcount w)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul] at this
    push_cast at this
    have hp : (0 : ℝ) < ((k' : ℝ) + 1) ^ n := by positivity
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have h1 : δ / 4 * (N + 1) ≤ (A.card : ℝ) - M := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hp.le
    nlinarith
  obtain ⟨x, -, hxB⟩ := Finset.exists_le_of_sum_le (s := Finset.range (N + 1))
    ⟨0, Finset.mem_range.2 (by omega)⟩ (f := fun _ => δ / 4 * ((k' : ℝ) + 1) ^ n)
    (g := fun x => ((B x).card : ℝ)) (by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      linarith)
  obtain ⟨ℓ, hℓ⟩ := hn (Fin n) (by simp) (B x) (by simpa using hxB)
  obtain ⟨j0, hj0⟩ := ℓ.proper ()
  refine ⟨x + wsum (lpt ℓ 0), (Finset.univ.filter (fun j => ℓ.idxFun j = Sum.inr ())).card,
    Finset.card_pos.2 ⟨j0, by simp [hj0]⟩, fun i hi => ?_⟩
  have h := hℓ ⟨i, hi⟩
  simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rw [wsum_lpt] at h ⊢
  convert h using 1
  simp only [Fin.val_zero, mul_zero, add_zero]
  ring

/-- A progression with positive difference and `k > 1` terms is a progression in the sense of
`Erdos142.IsAPOfLength`. -/
theorem not_isAPOfLengthFree_of_ap (k : ℕ) (hk : 1 < k) (S : Finset ℕ) (a d : ℕ) (hd : 0 < d)
    (h : ∀ i < k, a + i * d ∈ S) : ¬ Erdos142.IsAPOfLengthFree (S : Set ℕ) k := by
  intro hfree
  have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro x y hxy
    simp only at hxy
    have := Nat.eq_of_mul_eq_mul_right hd (by omega : x * d = y * d)
    exact this
  refine absurd (hfree _ ?_ ⟨a, d, ?_, rfl⟩) ?_
  · rintro x ⟨n, hn, rfl⟩
    rw [smul_eq_mul]
    exact h n (by exact_mod_cast hn)
  · rw [ENat.card_coe_set_eq]
    have : {x | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), a + n • d = x} =
        (((Finset.range k).image (fun n : ℕ => a + n * d) : Finset ℕ) : Set ℕ) := by
      ext x
      simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
        Set.mem_Iio, smul_eq_mul, Nat.cast_lt, exists_prop]
    rw [this, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
      Finset.card_range]
  · intro hle
    have : k ≤ 1 := by exact_mod_cast hle
    omega

/-- If every subset of `{1, …, N}` of size at least `c` contains a `k`-term progression, then
`r k N < c`. -/
theorem r_lt_of (k N : ℕ) (hk : 1 < k) (c : ℝ)
    (h : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → c ≤ S.card →
      ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) : (Erdos142.r k N : ℝ) < c := by
  have hne : {x | ∃ (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : Erdos142.IsAPOfLengthFree (S : Set ℕ) k), S.card = x}.Nonempty :=
    ⟨0, ∅, by simp, by simpa using Erdos142.isAPOfLengthFree_empty (α := ℕ) k, rfl⟩
  have hbdd : BddAbove {x | ∃ (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : Erdos142.IsAPOfLengthFree (S : Set ℕ) k), S.card = x} := by
    refine ⟨N, ?_⟩
    rintro m ⟨T, hT, -, rfl⟩
    simpa using (Finset.card_le_card hT).trans_eq (by simp)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hne hbdd
  by_contra hc
  push_neg at hc
  have hr : Erdos142.r k N = S.card := by
    rw [Erdos142.r, ← hcard]
  rw [hr] at hc
  obtain ⟨a, d, hd, hap⟩ := h S hS hc
  exact not_isAPOfLengthFree_of_ap k hk S a d hd hap hfree

end

end Szem

open scoped Topology

namespace Erdos142

/-- **Szemerédi's theorem** (Erdős Problem #139): `r_k(N) = o(N)` for every `k > 1`. -/
theorem erdos_139_szemeredi (k : ℕ) (hk : 1 < k) :
    Filter.Tendsto (fun N => (r k N / N : ℝ)) Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := Szem.szemeredi_ap k (by omega) (ε / 2) (by positivity)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr : (r k N : ℝ) < ε / 2 * N :=
    Szem.r_lt_of k N hk _ (fun S hS hc => hN0 N (by omega) S hS hc)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hNpos]
  nlinarith

end Erdos142

open scoped Topology

theorem solution (k : ℕ) (hk : 1 < k) :
    Filter.Tendsto (fun N => (Erdos142.r k N / N : ℝ)) Filter.atTop (𝓝 0) :=
  Erdos142.erdos_139_szemeredi k hk
