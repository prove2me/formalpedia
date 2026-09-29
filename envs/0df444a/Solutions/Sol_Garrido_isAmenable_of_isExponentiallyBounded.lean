-- Prove2me | solution 1 for Garrido.isAmenable_of_isExponentiallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T08:19:49.091034+00:00
-- url     : https://prove2.me/submissions/462d0b37-31b3-4145-9f4f-17f1b2d2c920

import Mathlib
import Theorems.Thm_Garrido_satisfiesFoelnerCondition_iff_isAmenable
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Foelner
import Definitions.Def_Chou_Growth

universe u v

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

theorem fol_isAmenable_of_satisfiesFoelnerCondition {G : Type*} [Group G]
    (h : SatisfiesFoelnerCondition G) : IsAmenable G :=
  (Garrido.satisfiesFoelnerCondition_iff_isAmenable G).mp h


section Growth

variable {G : Type*} [Group G]

theorem fol_one_mem_wordBall (S : Set G) (k : ℕ) : (1 : G) ∈ Chou.wordBall S k :=
  ⟨[], by simp, by simp, by simp⟩

theorem fol_wordBall_mono (S : Set G) {k k' : ℕ} (h : k ≤ k') :
    Chou.wordBall S k ⊆ Chou.wordBall S k' := by
  rintro g ⟨l, hl, hS, rfl⟩
  exact ⟨l, hl.trans h, hS, rfl⟩

theorem fol_mul_mem_wordBall (S : Set G) {k : ℕ} {x g : G} (hx : x ∈ S ∨ x⁻¹ ∈ S)
    (hg : g ∈ Chou.wordBall S k) : x * g ∈ Chou.wordBall S (k + 1) := by
  obtain ⟨l, hl, hS, rfl⟩ := hg
  refine ⟨x :: l, by simpa using hl, ?_, by simp⟩
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact hS y hy

theorem fol_wordBall_finite (S : Set G) (hS : S.Finite) (k : ℕ) :
    (Chou.wordBall S k).Finite := by
  induction k with
  | zero =>
    refine (Set.finite_singleton (1 : G)).subset ?_
    rintro g ⟨l, hl, -, rfl⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)]
    simp
  | succ k ih =>
    refine (ih.union ((hS.union hS.inv).biUnion fun x _ => ih.smul_set (a := x))).subset ?_
    rintro g ⟨l, hl, hlS, rfl⟩
    cases l with
    | nil => exact Or.inl (fol_one_mem_wordBall S k)
    | cons x l =>
      right
      simp only [Set.mem_iUnion]
      refine ⟨x, ?_, ?_⟩
      · rcases hlS x (by simp) with h | h
        · exact Or.inl h
        · exact Or.inr (by simpa using h)
      · refine ⟨l.prod, ⟨l, by simpa using hl, fun y hy => hlS y (by simp [hy]), rfl⟩, ?_⟩
        simp

theorem fol_mem_wordBall_of_closure (S : Set G) (hS : Subgroup.closure S = ⊤) (g : G) :
    ∃ r, g ∈ Chou.wordBall S r := by
  have hg : g ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨1, [x], by simp, by simp [hx], by simp⟩
  | one => exact ⟨0, fol_one_mem_wordBall S 0⟩
  | mul x y _ _ hx hy =>
    obtain ⟨r, l, hl, hlS, rfl⟩ := hx
    obtain ⟨r', l', hl', hlS', rfl⟩ := hy
    refine ⟨r + r', l ++ l', by simp; omega, ?_, by simp⟩
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact hlS z hz
    · exact hlS' z hz
  | inv x _ hx =>
    obtain ⟨r, l, hl, hlS, rfl⟩ := hx
    refine ⟨r, (l.map (·⁻¹)).reverse, by simpa using hl, ?_, by simp [List.prod_inv_reverse]⟩
    intro z hz
    simp only [List.mem_reverse, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rcases hlS y hy with h | h
    · exact Or.inr (by simpa using h)
    · exact Or.inl h

/-- For a letter `x`, `|x B(k) Δ B(k)| ≤ 2 (|B(k+1)| - |B(k)|)`. -/
theorem fol_ncard_symmDiff_letter (S : Set G) (hS : S.Finite) (k : ℕ) {x : G}
    (hx : x ∈ S ∨ x⁻¹ ∈ S) :
    ((x • Chou.wordBall S k) ∆ Chou.wordBall S k).ncard ≤
      2 * ((Chou.wordBall S (k + 1)).ncard - (Chou.wordBall S k).ncard) := by
  set B := Chou.wordBall S k
  set B' := Chou.wordBall S (k + 1)
  have hB' : B'.Finite := fol_wordBall_finite S hS (k + 1)
  have hsub : B ⊆ B' := fol_wordBall_mono S (Nat.le_succ k)
  have hdiff : (B' \ B).ncard = B'.ncard - B.ncard := Set.ncard_sdiff hsub (hB'.subset hsub)
  have hstep : ∀ y : G, (y ∈ S ∨ y⁻¹ ∈ S) → ((y • B) \ B).ncard ≤ (B' \ B).ncard := by
    intro y hy
    refine Set.ncard_le_ncard ?_ (hB'.sdiff)
    refine Set.sdiff_subset_sdiff_left ?_
    rintro _ ⟨g, hg, rfl⟩
    exact fol_mul_mem_wordBall S hy hg
  have hxinv : x⁻¹ ∈ S ∨ x⁻¹⁻¹ ∈ S := by rw [inv_inv]; exact hx.symm
  have h2 : (B \ (x • B)).ncard = ((x⁻¹ • B) \ B).ncard := by
    rw [← Set.ncard_smul_set x⁻¹ (B \ (x • B)), Set.smul_set_sdiff, inv_smul_smul]
  rw [symmDiff_def]
  calc ((x • B \ B) ∪ (B \ x • B)).ncard ≤ (x • B \ B).ncard + (B \ x • B).ncard :=
        Set.ncard_union_le _ _
    _ ≤ (B' \ B).ncard + (B' \ B).ncard := by
        rw [h2]; exact Nat.add_le_add (hstep x hx) (hstep x⁻¹ hxinv)
    _ = 2 * (B'.ncard - B.ncard) := by rw [hdiff]; ring

/-- Triangle inequality along a word. -/
theorem fol_ncard_symmDiff_prod (S : Set G) (F : Set G) (hF : F.Finite) (D : ℕ)
    (hD : ∀ x : G, (x ∈ S ∨ x⁻¹ ∈ S) → ((x • F) ∆ F).ncard ≤ D) :
    ∀ l : List G, (∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S) → ((l.prod • F) ∆ F).ncard ≤ l.length * D := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hl
    have hx := hl x (by simp)
    have hl' := ih (fun y hy => hl y (by simp [hy]))
    have hfin : ∀ g : G, ((g • F) ∆ F).Finite := fun g => (hF.smul_set).symmDiff hF
    rw [List.prod_cons, List.length_cons, mul_smul]
    calc ((x • l.prod • F) ∆ F).ncard
        ≤ ((x • l.prod • F) ∆ (x • F) ∪ (x • F) ∆ F).ncard :=
          Set.ncard_le_ncard (symmDiff_triangle _ _ _)
            (((hfin _).smul_set (a := x) |>.subset (by rw [Set.smul_set_symmDiff])).union
              (hfin x))
      _ ≤ ((x • l.prod • F) ∆ (x • F)).ncard + ((x • F) ∆ F).ncard := Set.ncard_union_le _ _
      _ = ((l.prod • F) ∆ F).ncard + ((x • F) ∆ F).ncard := by
          rw [← Set.smul_set_symmDiff, Set.ncard_smul_set]
      _ ≤ l.length * D + D := Nat.add_le_add hl' (hD x hx)
      _ = (l.length + 1) * D := by ring

/-- Subexponential growth gives a radius at which the ball grows by a factor at most `1 + δ`. -/
theorem fol_exists_slow_step (S : Set G)
    (hG : ∀ c : ℝ, 1 < c → ∃ N : ℕ, ∀ n ≥ N, ((Chou.wordBall S n).ncard : ℝ) ≤ c ^ n)
    (hfin : ∀ k, (Chou.wordBall S k).Finite)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k, ((Chou.wordBall S (k + 1)).ncard : ℝ) ≤ (1 + δ) * (Chou.wordBall S k).ncard := by
  by_contra hcon
  push Not at hcon
  have hgrow : ∀ k, (1 + δ) ^ k ≤ ((Chou.wordBall S k).ncard : ℝ) := by
    intro k
    induction k with
    | zero =>
      have : 1 ≤ (Chou.wordBall S 0).ncard :=
        (Set.ncard_pos (hfin 0)).2 ⟨1, fol_one_mem_wordBall S 0⟩
      simpa using (show (1 : ℝ) ≤ (Chou.wordBall S 0).ncard by exact_mod_cast this)
    | succ k ih =>
      rw [pow_succ]
      calc (1 + δ) ^ k * (1 + δ) ≤ (1 + δ) * (Chou.wordBall S k).ncard := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ _ := (hcon k).le
  obtain ⟨N, hN⟩ := hG (1 + δ / 2) (by linarith)
  have h1 := hN (N + 1) (by omega)
  have h2 := hgrow (N + 1)
  have h3 : (1 + δ / 2) ^ (N + 1) < (1 + δ) ^ (N + 1) :=
    pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)
  linarith

theorem fol_satisfiesFoelnerCondition_of_isExponentiallyBounded
    (hG : Chou.IsExponentiallyBounded G) : SatisfiesFoelnerCondition G := by
  obtain ⟨S, hS, hgrowth⟩ := hG
  set T : Set G := (S : Set G)
  have hT : T.Finite := S.finite_toSet
  have hfin : ∀ k, (Chou.wordBall T k).Finite := fol_wordBall_finite T hT
  have hG' : ∀ c : ℝ, 1 < c → ∃ N : ℕ, ∀ n ≥ N, ((Chou.wordBall T n).ncard : ℝ) ≤ c ^ n := by
    intro c hc
    obtain ⟨N, hN⟩ := hgrowth c hc
    exact ⟨N, fun n hn => by rw [← Nat.card_coe_set_eq]; exact hN n hn⟩
  intro A hA ε hε
  have hev : ∀ᶠ r in atTop, ∀ a ∈ A, a ∈ Chou.wordBall T r := by
    rw [eventually_all_finite hA]
    intro a _
    obtain ⟨r, hr⟩ := fol_mem_wordBall_of_closure T hS a
    filter_upwards [eventually_ge_atTop r] with r' hr'
    exact fol_wordBall_mono T hr' hr
  obtain ⟨R, hR⟩ := hev.exists
  have hδ : 0 < ε / (2 * ((R : ℝ) + 1)) := by positivity
  obtain ⟨k, hk⟩ := fol_exists_slow_step T hG' hfin _ hδ
  set B := Chou.wordBall T k
  set B' := Chou.wordBall T (k + 1)
  have hsub : B ⊆ B' := fol_wordBall_mono T (Nat.le_succ k)
  have hle : B.ncard ≤ B'.ncard := Set.ncard_le_ncard hsub (hfin _)
  have hBpos : (0 : ℝ) < B.ncard := by
    exact_mod_cast (Set.ncard_pos (hfin k)).2 ⟨1, fol_one_mem_wordBall T k⟩
  refine ⟨B, hfin k, ⟨1, fol_one_mem_wordBall T k⟩, fun a ha => ?_⟩
  obtain ⟨l, hl, hlS, rfl⟩ := hR a ha
  have hbound := fol_ncard_symmDiff_prod T B (hfin k) _
    (fun x hx => fol_ncard_symmDiff_letter T hT k hx) l hlS
  have hbound' : (((l.prod • B) ∆ B).ncard : ℝ) ≤
      (R : ℝ) * (2 * ((B'.ncard : ℝ) - B.ncard)) := by
    have : (((l.prod • B) ∆ B).ncard : ℝ) ≤ (l.length : ℝ) * (2 * ((B'.ncard - B.ncard : ℕ) : ℝ)) := by
      exact_mod_cast hbound
    rw [Nat.cast_sub hle] at this
    refine this.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) ?_)
    have : (B.ncard : ℝ) ≤ B'.ncard := by exact_mod_cast hle
    linarith
  rw [div_le_iff₀ hBpos]
  have hR0 : (0 : ℝ) ≤ R := by positivity
  have hkey : (B'.ncard : ℝ) - B.ncard ≤ ε / (2 * ((R : ℝ) + 1)) * B.ncard := by linarith
  calc (((l.prod • B) ∆ B).ncard : ℝ) ≤ (R : ℝ) * (2 * ((B'.ncard : ℝ) - B.ncard)) := hbound'
    _ ≤ (R : ℝ) * (2 * (ε / (2 * ((R : ℝ) + 1)) * B.ncard)) := by gcongr
    _ = ε * B.ncard * ((R : ℝ) / ((R : ℝ) + 1)) := by field_simp
    _ ≤ ε * B.ncard * 1 := by
        gcongr
        rw [div_le_one (by positivity)]; linarith
    _ = ε * B.ncard := mul_one _

end Growth

/-- Theorem 3.8. -/
theorem isAmenable_of_isExponentiallyBounded' (G : Type*) [Group G]
    (hG : Chou.IsExponentiallyBounded G) :
    IsAmenable G :=
  fol_isAmenable_of_satisfiesFoelnerCondition
    (fol_satisfiesFoelnerCondition_of_isExponentiallyBounded hG)

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

theorem solution (G : Type*) [Group G]
    (hG : Chou.IsExponentiallyBounded G) :
    IsAmenable G := by
  apply Garrido.Lib.isAmenable_of_isExponentiallyBounded' <;> assumption
