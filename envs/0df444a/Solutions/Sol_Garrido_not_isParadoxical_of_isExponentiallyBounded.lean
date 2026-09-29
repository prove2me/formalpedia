-- Prove2me | solution 1 for Garrido.not_isParadoxical_of_isExponentiallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T19:45:17.659837+00:00
-- url     : https://prove2.me/submissions/98fbcf5b-58b2-4afe-bdb5-5facfdc4985d

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Foelner
import Definitions.Def_Chou_Growth

namespace Garrido.Lib

open scoped ENNReal Pointwise Topology
open Filter Set Garrido

end Garrido.Lib

/-!
# Closure properties of amenability (Garrido, Example 2.1, Proposition 2.2(1),(3),
Corollary 2.4, and EG ⊆ AG)

Everything is proved from one pushforward lemma: if `f : G → K` satisfies, for every `k : K`,
some `g : G` with `f (g * x) = k * f x` for all `x`, then an invariant finitely additive
probability on `G` pushes forward along `f` to one on `K`. Quotient maps, isomorphisms and the
"`H`-component" map `G → H` of a right transversal all have this shape.
-/

namespace Garrido.Lib

open Garrido
open scoped ENNReal Pointwise

universe u

/-! ### Pushforward -/

/-! ### Example 2.1 -/

/-! ### Proposition 2.2(1) -/

/-! ### Proposition 2.2(3) -/


/-! ### Corollary 2.4, from Propositions 2.3 and 2.2(2) taken as hypotheses -/

section Hyp

variable (h23 : ∀ (K : Type u) [CommGroup K], IsAmenable K)
  (h222 : ∀ (K : Type u) [Group K] (N : Subgroup K) [N.Normal],
    IsAmenable N → IsAmenable (K ⧸ N) → IsAmenable K)
include h23 h222

end Hyp

end Garrido.Lib

/-!
# Means versus finitely additive measures (Garrido, Theorem 1.15 and Proposition 2.2(2))

From a finitely additive probability measure `m` on `X` we build the integral
`mean_integral m : ℓ∞(X) →ₗ[ℝ] ℝ`. It is the upper Darboux integral
`f ↦ inf { ∫ s dm : s finitely valued, f ≤ s }`, which is sublinear; Hahn–Banach gives a linear
functional below it, and uniform approximation by finitely valued functions shows that functional
equals the upper integral, so the upper integral is linear.
-/

namespace Garrido.Lib

open scoped ENNReal Pointwise
open Set


section Integral

variable {X : Type*} (m : Set X → ℝ≥0∞)

variable {m}

/-! ### The upper integral on `ℓ∞` -/

local notation "E" X => lp (fun _ : X => ℝ) ∞

/-- A finitely valued function as an element of `ℓ∞`. -/
noncomputable def meanOfFin (s : X → ℝ) (hs : (range s).Finite) : E X :=
  ⟨s, memℓp_infty_iff.2 (by
    have : (range fun i => ‖s i‖) = (fun v => ‖v‖) '' range s := by
      rw [← Set.range_comp]; rfl
    rw [this]
    exact (hs.image _).bddAbove)⟩

@[simp] theorem meanOfFin_apply (s : X → ℝ) (hs : (range s).Finite) (x : X) :
    (meanOfFin s hs : X → ℝ) x = s x := rfl

theorem mean_range_indicator (A : Set X) : (range (A.indicator (1 : X → ℝ))).Finite :=
  (Set.toFinite ({0, 1} : Set ℝ)).subset (by
    rintro _ ⟨x, rfl⟩; by_cases h : x ∈ A <;> simp [h])

/-- The indicator function of `A` as an element of `ℓ∞`. -/
noncomputable def mean_ind (A : Set X) : E X := meanOfFin _ (mean_range_indicator A)

@[simp] theorem mean_ind_apply (A : Set X) (x : X) :
    (mean_ind A : X → ℝ) x = A.indicator 1 x := rfl

end Integral

/-! ### From a mean to a measure -/

section MeanToMeasure

/-- A bounded function with values in `[0, 1]`, as an element of `ℓ∞`. -/
noncomputable def mean_ofUnit {X : Type*} (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    lp (fun _ : X => ℝ) ∞ :=
  ⟨f, memℓp_infty_iff.2 ⟨1, by
    rintro _ ⟨x, rfl⟩
    simp only [Real.norm_eq_abs, abs_of_nonneg (hf x).1]
    exact (hf x).2⟩⟩

@[simp] theorem mean_ofUnit_apply {X : Type*} (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (x : X) : (mean_ofUnit f hf : X → ℝ) x = f x := rfl

end MeanToMeasure

/-! ### Theorem 1.15 -/


/-! ### The easy half of Tarski's theorem (Theorem 1.11, ⇒) -/

/-! ### Proposition 2.2(2) -/

end Garrido.Lib

/-!
# Garrido, Theorems 2.6 and 2.7 (invariant extension property)

Construction for 2.6 (`HasInvariantMean G → HasInvariantExtensionProperty G`): with `m` a
left-invariant mean, for `b : Set X` put `f_b g := ν (g⁻¹ • b)` and
`μbar b := ofReal (m (toReal ∘ f_b))` when `f_b` is bounded by a finite constant, `∞` otherwise.
* additivity: `f_{b ∪ c} = f_b + f_c` for disjoint `b, c`; the sum is bounded iff both are,
  and otherwise both sides are `∞`;
* invariance: `f_{h • b} g = f_b (h⁻¹ * g)`, i.e. `toReal ∘ f_{h • b} = lshift h (toReal ∘ f_b)`
  (matching `lshift h f g = f (h⁻¹ * g)`);
* extension: for `s ∈ R`, `f_s` is the constant `μ s` (finite: the mean of a constant;
  infinite: unbounded, so `∞`).
-/

namespace Garrido.Lib

open Garrido
open scoped ENNReal Pointwise

universe v

/-- A function `G → ℝ≥0∞` bounded by a finite constant. -/
def ext_Bdd {G : Type*} (f : G → ℝ≥0∞) : Prop := ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g, f g ≤ C

/-- The real-valued bounded function `toReal ∘ f`, as an element of `ℓ∞(G)`. -/
noncomputable def ext_toLp {G : Type*} (f : G → ℝ≥0∞) (hf : ext_Bdd f) :
    lp (fun _ : G => ℝ) ∞ :=
  ⟨fun g => (f g).toReal, by
    obtain ⟨C, hC, hle⟩ := hf
    refine memℓp_infty_iff.2 ⟨C.toReal, ?_⟩
    rintro _ ⟨g, rfl⟩
    simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hC (hle g)⟩

@[simp] theorem ext_toLp_apply {G : Type*} (f : G → ℝ≥0∞) (hf : ext_Bdd f) (g : G) :
    (ext_toLp f hf : G → ℝ) g = (f g).toReal := rfl

end Garrido.Lib

namespace Garrido.Lib

open scoped ENNReal Pointwise symmDiff Topology
open MeasureTheory Filter Set


section Growth

variable {G : Type*} [Group G]

end Growth

end Garrido.Lib

namespace Garrido.Lib

open scoped Pointwise symmDiff ENNReal
open Finset

section Layer

variable {G : Type*} [Group G] [DecidableEq G]

end Layer

section Mean

variable {G : Type*} [Group G]

end Mean


end Garrido.Lib

namespace Garrido.Lib

open scoped ENNReal Pointwise
open Set

end Garrido.Lib

namespace Garrido.Lib

open scoped ENNReal Pointwise
open Set

theorem eq_wordBall_mono {G : Type*} [Group G] (S : Set G) {a b : ℕ} (h : a ≤ b) :
    Chou.wordBall S a ⊆ Chou.wordBall S b := by
  rintro g ⟨l, hl, hS, rfl⟩
  exact ⟨l, hl.trans h, hS, rfl⟩

theorem eq_wordBall_mul {G : Type*} [Group G] (S : Set G) {a b : ℕ} {x y : G}
    (hx : x ∈ Chou.wordBall S a) (hy : y ∈ Chou.wordBall S b) :
    x * y ∈ Chou.wordBall S (a + b) := by
  obtain ⟨l, hl, hS, rfl⟩ := hx
  obtain ⟨l', hl', hS', rfl⟩ := hy
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro z hz
  rcases List.mem_append.1 hz with h | h
  · exact hS z h
  · exact hS' z h

theorem eq_wordBall_finite {G : Type*} [Group G] (S : Finset G) (n : ℕ) :
    (Chou.wordBall (S : Set G) n).Finite := by
  have hT : ((S : Set G) ∪ (S : Set G)⁻¹).Finite := S.finite_toSet.union S.finite_toSet.inv
  induction n with
  | zero =>
    apply (Set.finite_singleton (1 : G)).subset
    rintro g ⟨l, hl, -, rfl⟩
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp
  | succ n ih =>
    apply ((Set.finite_singleton (1 : G)).union (hT.mul ih)).subset
    rintro g ⟨l, hl, hS, rfl⟩
    cases l with
    | nil => left; simp
    | cons x l =>
      right
      refine ⟨x, ?_, l.prod, ⟨l, by simp at hl; omega, fun z hz => hS z (by simp [hz]), rfl⟩,
        by simp⟩
      rcases hS x (by simp) with h | h
      · exact Or.inl h
      · exact Or.inr h

theorem eq_exists_wordBall {G : Type*} [Group G] {S : Set G}
    (hS : Subgroup.closure S = ⊤) (g : G) : ∃ k, g ∈ Chou.wordBall S k := by
  have hg : g ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨1, [x], by simp, by simp [hx], by simp⟩
  | one => exact ⟨0, [], by simp, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, eq_wordBall_mul S ha hb⟩
  | inv x _ hx =>
    obtain ⟨a, l, hl, hS', rfl⟩ := hx
    refine ⟨a, (l.map fun x => x⁻¹).reverse, by simpa using hl, ?_, (List.prod_inv_reverse l).symm⟩
    intro z hz
    simp only [List.mem_reverse, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rcases hS' y hy with h | h
    · right; simpa using h
    · left; exact h

theorem not_isParadoxical_of_isExponentiallyBounded' {G : Type*} [Group G]
    (hG : Chou.IsExponentiallyBounded G) {X : Type*} [MulAction G X]
    (A : Set X) (hA : A.Nonempty) :
    ¬ IsParadoxical G A := by
  classical
  obtain ⟨S, hS, hgrowth⟩ := hG
  rintro ⟨A1, A2, hA1, hA2, -, -, hdisj, ⟨e1, hs1, ht1⟩, ⟨e2, hs2, ht2⟩⟩
  obtain ⟨a, ha⟩ := hA
  -- the two piecewise translations `A → A` with disjoint images
  let φ : Bool → PartialEquiv X X := fun b => cond b e1.symm.toPartialEquiv e2.symm.toPartialEquiv
  let W : Finset G := e1.symm.witness ∪ e2.symm.witness
  let Ab : Bool → Set X := fun b => cond b A1 A2
  have hφs : ∀ b, (φ b).source = A := by
    intro b; cases b
    · exact ht2
    · exact ht1
  have hφt : ∀ b, (φ b).target = Ab b := by
    intro b; cases b
    · exact hs2
    · exact hs1
  have hAb : ∀ b, Ab b ⊆ A := by
    intro b; cases b
    · exact hA2
    · exact hA1
  have hmaps : ∀ b, ∀ x ∈ A, φ b x ∈ Ab b := by
    intro b x hx
    rw [← hφt b]; exact (φ b).map_source (hφs b ▸ hx)
  have hinj : ∀ b, ∀ x ∈ A, ∀ y ∈ A, φ b x = φ b y → x = y := by
    intro b x hx y hy h
    exact (φ b).injOn (hφs b ▸ hx) (hφs b ▸ hy) h
  have hdec : ∀ b, ∀ x ∈ A, ∃ g ∈ W, φ b x = g • x := by
    intro b x hx
    cases b
    · obtain ⟨g, hg, h⟩ := e2.symm.isDecompOn x (by rw [← ht2] at hx; exact hx)
      exact ⟨g, Finset.mem_union_right _ hg, h⟩
    · obtain ⟨g, hg, h⟩ := e1.symm.isDecompOn x (by rw [← ht1] at hx; exact hx)
      exact ⟨g, Finset.mem_union_left _ hg, h⟩
  -- word length bound for the multipliers
  choose k hk using eq_exists_wordBall hS
  let C : ℕ := W.sup k + 1
  have hW : ∀ g ∈ W, g ∈ Chou.wordBall (S : Set G) C :=
    fun g hg => eq_wordBall_mono _ ((Finset.le_sup hg).trans (Nat.le_succ _)) (hk g)
  -- compositions
  let F : List Bool → X := fun l => l.foldr (fun b y => φ b y) a
  have hFA : ∀ l, F l ∈ A := by
    intro l; induction l with
    | nil => exact ha
    | cons b l ih => exact hAb b (hmaps b _ ih)
  have hFw : ∀ l, ∃ w ∈ Chou.wordBall (S : Set G) (C * l.length), F l = w • a := by
    intro l; induction l with
    | nil => exact ⟨1, ⟨[], by simp, by simp, by simp⟩, by simp [F]⟩
    | cons b l ih =>
      obtain ⟨w, hw, hFl⟩ := ih
      obtain ⟨g, hg, hgx⟩ := hdec b _ (hFA l)
      refine ⟨g * w, ?_, ?_⟩
      · have := eq_wordBall_mul _ (hW g hg) hw
        simpa [Nat.mul_succ, Nat.add_comm] using this
      · change φ b (F l) = _
        rw [hgx, hFl, mul_smul]
  have hFinj : ∀ l l' : List Bool, l.length = l'.length → F l = F l' → l = l' := by
    intro l
    induction l with
    | nil => intro l' hl _; exact (List.length_eq_zero_iff.1 hl.symm).symm
    | cons b l ih =>
      intro l' hl h
      cases l' with
      | nil => simp at hl
      | cons b' l' =>
        have h' : φ b (F l) = φ b' (F l') := h
        have hbb : b = b' := by
          by_contra hne
          have h1 := hmaps b _ (hFA l)
          have h2 := hmaps b' _ (hFA l')
          rw [h'] at h1
          cases b <;> cases b'
          · exact hne rfl
          · exact Set.disjoint_left.1 hdisj h2 h1
          · exact Set.disjoint_left.1 hdisj h1 h2
          · exact hne rfl
        subst hbb
        rw [ih l' (by simpa using hl) (hinj b _ (hFA l) _ (hFA l') h')]
  choose w hw hFw' using hFw
  have hcount : ∀ n, 2 ^ n ≤ Nat.card (Chou.wordBall (S : Set G) (C * n)) := by
    intro n
    have hfin := (eq_wordBall_finite S (C * n)).to_subtype
    let ψ : (Fin n → Bool) → Chou.wordBall (S : Set G) (C * n) := fun σ =>
      ⟨w (List.ofFn σ), by simpa using hw (List.ofFn σ)⟩
    have hψ : Function.Injective ψ := by
      intro σ τ h
      have h1 : w (List.ofFn σ) = w (List.ofFn τ) := congrArg Subtype.val h
      have h2 : F (List.ofFn σ) = F (List.ofFn τ) := by rw [hFw', hFw', h1]
      exact List.ofFn_injective (hFinj _ _ (by simp) h2)
    have := Nat.card_le_card_of_injective ψ hψ
    simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using this
  -- the growth contradiction
  have hCpos : (0 : ℝ) < C := by positivity
  set c : ℝ := (2 : ℝ) ^ ((1 : ℝ) / (2 * C)) with hc
  have hc1 : 1 < c := Real.one_lt_rpow (by norm_num) (by positivity)
  obtain ⟨N, hN⟩ := hgrowth c hc1
  let n := max N 1
  have hn1 : 1 ≤ n := le_max_right _ _
  have hCn : N ≤ C * n := (le_max_left N 1).trans (Nat.le_mul_of_pos_left n (by omega))
  have h1 := hN (C * n) hCn
  have h2 : ((2 : ℝ) ^ n) ≤ (Nat.card (Chou.wordBall (S : Set G) (C * n)) : ℝ) := by
    exact_mod_cast hcount n
  have h3 : c ^ (C * n) = (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    field_simp
  have h4 : (2 : ℝ) ^ (n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [Real.rpow_natCast]; linarith
  rw [Real.rpow_le_rpow_left_iff (by norm_num)] at h4
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  linarith

end Garrido.Lib

namespace Garrido.Lib

open Garrido MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise

section Extension

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

open Classical

/-- The filter "eventually the list contains any given set". -/
noncomputable def leb_filter (X : Type*) : Filter (List (Set X)) :=
  Filter.map Finset.toList atTop

instance leb_filter_neBot : (leb_filter X).NeBot := by
  unfold leb_filter; infer_instance

end Extension

end Garrido.Lib

namespace Garrido.Lib

open Garrido MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise

section Isometry

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

end Isometry

end Garrido.Lib

namespace Garrido.Lib

open Garrido MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise

section Corollary25

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-- Isometries act on the space by application. -/
@[reducible] noncomputable def leb_mulAction : MulAction ((E n) ≃ᵢ (E n)) (E n) where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] leb_mulAction

end Corollary25

end Garrido.Lib

/-!
# Tarski's theorem (Garrido, Theorem 1.11) and Theorem 3.10(2)

Route (see `NOTES-TAR.md`): infinite Hall ⇒ "doubling ⇒ paradox"; iteration ⇒ Følner sets
inside `E` for a non-paradoxical `E`; ultrafilter limit of normalised counting measures on those
sets ⇒ a finitely additive `ν` with `ν E = 1` that is invariant for partial translations inside
`E`; a supremum over finite families of translated pieces extends `ν` to a `G`-invariant
finitely additive measure `m` with `m E = 1`.
-/

namespace Garrido.Lib

open scoped ENNReal Pointwise Classical
open Garrido Set

section Tarski

variable {G X : Type*} [Group G] [MulAction G X]

/-! ### Step 1: doubling inside `E` gives a paradoxical decomposition -/

/-! ### Step 2: expansion by a factor `(k+2)/(k+1)` gives doubling -/

/-! ### Step 3: a non-paradoxical set has Følner sets inside it -/

/-! ### Step 4: normalised counting measures on Følner sets -/

/-! ### Step 5: the limit measure -/

/-! ### Step 6: extension to a `G`-invariant measure on all of `X` -/

/-! ### The easy direction -/

end Tarski

-- Theorem 1.11 (p. 3), Tarski.

end Garrido.Lib

/-!
# Composition of the clusters

Each target below is stated exactly as published and assembled from results proved in the
cluster modules (`AB_`, `CLO_`, `MEAN_`, `EXT_`, `FOL_`, `NAM_`, `EQ_`, `LEB_`, `TAR_`).
-/

namespace Garrido.Lib

open Garrido

end Garrido.Lib

open Garrido
open scoped ENNReal Pointwise
universe u

theorem solution {G : Type*} [Group G]
    (hG : Chou.IsExponentiallyBounded G) {X : Type*} [MulAction G X]
    (A : Set X) (hA : A.Nonempty) :
    ¬ IsParadoxical G A := by
  apply Garrido.Lib.not_isParadoxical_of_isExponentiallyBounded' <;> assumption
