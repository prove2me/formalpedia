-- Prove2me | solution 1 for Garrido.exists_invariant_measure_and_not_isParadoxical_of_isAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T19:10:46.310119+00:00
-- url     : https://prove2.me/submissions/18b36f95-fa49-4b95-b932-e2aad9f009d0

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

theorem eq_measure_image {G X : Type*} [Group G] [MulAction G X] {m : Set X → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) (hinv : IsInvariant G m) (e : Equidecomp X G) :
    ∀ (W : Finset G) (S : Set X), S ⊆ e.source → Equidecomp.IsDecompOn e S W →
      m S = m (e '' S) := by
  classical
  intro W
  induction W using Finset.induction_on with
  | empty =>
    intro S _ hd
    have : S = ∅ := by
      ext a; simp only [mem_empty_iff_false, iff_false]
      intro ha; obtain ⟨g, hg, -⟩ := hd a ha; simp at hg
    subst this; simp
  | insert w W _ ih =>
    intro S hS hd
    let P := {a ∈ S | e a = w • a}
    let R := S \ P
    have hPS : P ⊆ S := sep_subset _ _
    have hSPR : S = P ∪ R := (union_sdiff_cancel hPS).symm
    have hR : Equidecomp.IsDecompOn e R W := by
      intro a ha
      obtain ⟨g, hg, hga⟩ := hd a ha.1
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact absurd ⟨ha.1, hga⟩ ha.2
      · exact ⟨g, hg, hga⟩
    have hmR := ih R (sdiff_subset.trans hS) hR
    have hPimg : e '' P = w • P := by
      rw [← Set.image_smul]
      exact Set.image_congr (fun a ha => ha.2)
    have hdisj : Disjoint (e '' P) (e '' R) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have : b = a := e.toPartialEquiv.injOn (hS hb.1) (hS ha.1) hab
      exact hb.2 (this ▸ ha)
    rw [hSPR, image_union, hm.2 _ _ disjoint_sdiff_right, hm.2 _ _ hdisj, hmR, hPimg,
      hinv]

theorem eq_measure_eq {G X : Type*} [Group G] [MulAction G X] {m : Set X → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) (hinv : IsInvariant G m) {A B : Set X}
    (h : Equidecomposable G A B) : m A = m B := by
  obtain ⟨e, rfl, rfl⟩ := h
  rw [eq_measure_image hm hinv e e.witness _ subset_rfl e.isDecompOn]
  exact congrArg m e.toPartialEquiv.image_source_eq_target

theorem eq_measure_mono {X : Type*} {m : Set X → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) {s t : Set X} (h : s ⊆ t) : m s ≤ m t := by
  rw [← union_sdiff_cancel h, hm.2 _ _ disjoint_sdiff_right]
  exact le_self_add

/-- The easy half of Tarski's theorem: a set of invariant finitely additive measure `1` is not
paradoxical. -/
theorem eq_not_isParadoxical_of_measure_eq_one {G X : Type*} [Group G] [MulAction G X]
    {m : Set X → ℝ≥0∞} (hm : IsFinitelyAdditiveMeasure m) (hinv : IsInvariant G m)
    {E : Set X} (hE : m E = 1) : ¬ IsParadoxical G E := by
  rintro ⟨A, B, hA, hB, -, -, hAB, hAE, hBE⟩
  have h1 := eq_measure_eq hm hinv hAE
  have h2 := eq_measure_eq hm hinv hBE
  have h3 := eq_measure_mono hm (union_subset hA hB)
  rw [hm.2 _ _ hAB, h1, h2, hE] at h3
  norm_num at h3

theorem exists_invariant_measure_and_not_isParadoxical_of_isAmenable'
    {G : Type*} [Group G] (hG : IsAmenable G)
    (X : Type*) [MulAction G X] [Nonempty X] :
    (∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
        IsInvariant G m) ∧
      ¬ IsParadoxical G (Set.univ : Set X) := by
  obtain ⟨m, ⟨hm0, hmadd⟩, hm1, hinv⟩ := hG
  obtain ⟨x⟩ := ‹Nonempty X›
  let μ : Set X → ℝ≥0∞ := fun s => m {g : G | g • x ∈ s}
  have hμ : IsFinitelyAdditiveMeasure μ := by
    refine ⟨by simpa [μ] using hm0, fun s t hst => ?_⟩
    have : {g : G | g • x ∈ s ∪ t} = {g : G | g • x ∈ s} ∪ {g : G | g • x ∈ t} := rfl
    simp only [μ]
    rw [this, hmadd]
    exact hst.preimage (fun g : G => g • x)
  have hμ1 : μ Set.univ = 1 := by simpa [μ] using hm1
  have hμinv : IsInvariant G μ := by
    intro h s
    simp only [μ]
    have : {g : G | g • x ∈ h • s} = h • {g : G | g • x ∈ s} := by
      ext g
      simp only [mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mul_smul]
    rw [this, hinv]
  exact ⟨⟨μ, hμ, hμ1, hμinv⟩, eq_not_isParadoxical_of_measure_eq_one hμ hμinv hμ1⟩

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

theorem solution
    {G : Type*} [Group G] (hG : IsAmenable G)
    (X : Type*) [MulAction G X] [Nonempty X] :
    (∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
        IsInvariant G m) ∧
      ¬ IsParadoxical G (Set.univ : Set X) := by
  apply Garrido.Lib.exists_invariant_measure_and_not_isParadoxical_of_isAmenable' <;> assumption
