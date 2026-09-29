-- Prove2me | solution 1 for Garrido.isAmenable_of_commGroup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T19:41:02.416788+00:00
-- url     : https://prove2.me/submissions/403d3afe-bc1f-49ee-aeb4-b7a9f7a21c70

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Foelner
import Definitions.Def_Chou_Growth

namespace Garrido.Lib

open scoped ENNReal Pointwise Topology
open Filter Set Garrido

/-- Compactness: almost-invariant finitely additive probability measures for every finite set and
every tolerance give an invariant one (ultrafilter limit). -/
theorem ab_isAmenable_of_almostInvariant (G : Type*) [Group G]
    (h : ∀ (A : Finset G) (ε : ℝ≥0∞), 0 < ε → ∃ m : Set G → ℝ≥0∞,
      IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧ ∀ a ∈ A, ∀ s : Set G, m (a • s) ≤ m s + ε) :
    IsAmenable G := by
  classical
  choose m hm using fun i : Finset G × ℕ => h i.1 ((i.2 : ℝ≥0∞)⁻¹)
    (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _))
  let U : Ultrafilter (Finset G × ℕ) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset G × ℕ)) ≤ atTop := Ultrafilter.of_le _
  let M : Set G → ℝ≥0∞ := fun s => limUnder U (fun i => m i s)
  have hM : ∀ s, Tendsto (fun i => m i s) U (𝓝 (M s)) := by
    intro s
    obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (U.map (fun i => m i s))
      (by simp)
    exact tendsto_nhds_limUnder ⟨x, hx⟩
  have hε : Tendsto (fun i : Finset G × ℕ => ((i.2 : ℝ≥0∞)⁻¹)) U (𝓝 0) := by
    refine Tendsto.mono_left ?_ hU
    rw [← prod_atTop_atTop_eq]
    exact ENNReal.tendsto_inv_nat_nhds_zero.comp tendsto_snd
  have hle : ∀ (a : G) (s : Set G), M (a • s) ≤ M s := by
    intro a s
    have h2 : Tendsto (fun i : Finset G × ℕ => m i s + (i.2 : ℝ≥0∞)⁻¹) U (𝓝 (M s + 0)) :=
      (hM s).add hε
    rw [add_zero] at h2
    refine le_of_tendsto_of_tendsto (hM (a • s)) h2 ?_
    have hev : ∀ᶠ i : Finset G × ℕ in atTop, a ∈ i.1 := by
      filter_upwards [eventually_ge_atTop (({a} : Finset G), 0)] with i hi
      exact hi.1 (Finset.mem_singleton_self a)
    filter_upwards [hU hev] with i hi
    exact (hm i).2.2 a hi s
  refine ⟨M, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact tendsto_nhds_unique (hM ∅) (by simp only [(hm _).1.1]; exact tendsto_const_nhds)
  · intro s t hst
    refine tendsto_nhds_unique (hM (s ∪ t)) ?_
    simp only [(hm _).1.2 s t hst]
    exact (hM s).add (hM t)
  · exact tendsto_nhds_unique (hM univ) (by simp only [(hm _).2.1]; exact tendsto_const_nhds)
  · intro a s
    refine le_antisymm (hle a s) ?_
    calc M s = M (a⁻¹ • a • s) := by rw [inv_smul_smul]
      _ ≤ M (a • s) := hle _ _

/-- Monotonicity of a finitely additive measure. -/
theorem ab_mono {X : Type*} {m : Set X → ℝ≥0∞} (hm : IsFinitelyAdditiveMeasure m)
    {s t : Set X} (hst : s ⊆ t) : m s ≤ m t := by
  have : t = s ∪ (t \ s) := (Set.union_sdiff_cancel hst).symm
  rw [this, hm.2 s (t \ s) Set.disjoint_sdiff_right]
  exact le_self_add

/-- Averaging a measure along `1, g, …, g^(N-1)`. -/
noncomputable def ab_avg {G : Type*} [Group G] (g : G) (N : ℕ) (m : Set G → ℝ≥0∞) :
    Set G → ℝ≥0∞ :=
  fun s => (∑ c ∈ Finset.range N, m (g ^ c • s)) * (N : ℝ≥0∞)⁻¹

theorem ab_avg_fa {G : Type*} [Group G] (g : G) (N : ℕ) {m : Set G → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) : IsFinitelyAdditiveMeasure (ab_avg g N m) := by
  refine ⟨?_, ?_⟩
  · simp [ab_avg, Set.smul_set_empty, hm.1]
  · intro s t hst
    simp only [ab_avg, Set.smul_set_union]
    rw [← add_mul, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    exact hm.2 _ _ ((Set.disjoint_smul_set).2 hst)

theorem ab_avg_univ {G : Type*} [Group G] (g : G) {N : ℕ} (hN : N ≠ 0) {m : Set G → ℝ≥0∞}
    (h1 : m Set.univ = 1) : ab_avg g N m Set.univ = 1 := by
  simp only [ab_avg, Set.smul_set_univ, h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hN) (ENNReal.natCast_ne_top N)

theorem ab_avg_shift {G : Type*} [Group G] (g : G) (N : ℕ) {m : Set G → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (s : Set G) :
    ab_avg g N m (g • s) ≤ ab_avg g N m s + (N : ℝ≥0∞)⁻¹ := by
  simp only [ab_avg]
  have hs : ∀ c : ℕ, g ^ c • g • s = g ^ (c + 1) • s := by
    intro c; rw [smul_smul, pow_succ]
  simp only [hs]
  have key : ∑ c ∈ Finset.range N, m (g ^ (c + 1) • s)
      ≤ ∑ c ∈ Finset.range N, m (g ^ c • s) + 1 := by
    have e := Finset.sum_range_succ' (fun c => m (g ^ c • s)) N
    rw [Finset.sum_range_succ] at e
    calc ∑ c ∈ Finset.range N, m (g ^ (c + 1) • s)
        ≤ ∑ c ∈ Finset.range N, m (g ^ (c + 1) • s) + m (g ^ 0 • s) := le_self_add
      _ = ∑ c ∈ Finset.range N, m (g ^ c • s) + m (g ^ N • s) := e.symm
      _ ≤ _ := by
        gcongr
        rw [← h1]; exact ab_mono hm (Set.subset_univ _)
  calc (∑ c ∈ Finset.range N, m (g ^ (c + 1) • s)) * (N : ℝ≥0∞)⁻¹
      ≤ (∑ c ∈ Finset.range N, m (g ^ c • s) + 1) * (N : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := by rw [add_mul, one_mul]

theorem ab_avg_comm {G : Type*} [CommGroup G] (g h : G) (N : ℕ) {m : Set G → ℝ≥0∞}
    {ε : ℝ≥0∞} (hh : ∀ s : Set G, m (h • s) ≤ m s + ε) (hN : N ≠ 0) (s : Set G) :
    ab_avg g N m (h • s) ≤ ab_avg g N m s + ε := by
  simp only [ab_avg]
  have hs : ∀ c : ℕ, g ^ c • h • s = h • g ^ c • s := by
    intro c; rw [smul_smul, smul_smul, mul_comm]
  simp only [hs]
  calc (∑ c ∈ Finset.range N, m (h • g ^ c • s)) * (N : ℝ≥0∞)⁻¹
      ≤ (∑ c ∈ Finset.range N, (m (g ^ c • s) + ε)) * (N : ℝ≥0∞)⁻¹ := by
        gcongr with c; exact hh _
    _ = (∑ c ∈ Finset.range N, m (g ^ c • s)) * (N : ℝ≥0∞)⁻¹ + ε := by
        rw [Finset.sum_add_distrib, add_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_comm (N : ℝ≥0∞) ε, mul_assoc,
          ENNReal.mul_inv_cancel (by exact_mod_cast hN) (ENNReal.natCast_ne_top N), mul_one]

theorem ab_almostInvariant_comm {G : Type*} [CommGroup G] (A : Finset G) {N : ℕ} (hN : N ≠ 0) :
    ∃ m : Set G → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
      ∀ a ∈ A, ∀ s : Set G, m (a • s) ≤ m s + (N : ℝ≥0∞)⁻¹ := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨fun s => if (1 : G) ∈ s then 1 else 0, ⟨by simp, ?_⟩, by simp, by simp⟩
    intro s t hst
    by_cases hs : (1 : G) ∈ s
    · have ht : (1 : G) ∉ t := Set.disjoint_left.1 hst hs
      simp [hs, ht]
    · by_cases ht : (1 : G) ∈ t <;> simp [hs, ht]
  | insert a A _ ih =>
    obtain ⟨m, hm, h1, hA⟩ := ih
    refine ⟨ab_avg a N m, ab_avg_fa a N hm, ab_avg_univ a hN h1, ?_⟩
    intro b hb s
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact ab_avg_shift b N hm h1 s
    · exact ab_avg_comm a b N (hA b hb) hN s

theorem isAmenable_of_commGroup' (G : Type*) [CommGroup G] : IsAmenable G := by
  refine ab_isAmenable_of_almostInvariant G fun A ε hε => ?_
  obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  obtain ⟨m, hm, h1, hA⟩ := ab_almostInvariant_comm A hN0
  exact ⟨m, hm, h1, fun a ha s => (hA a ha s).trans (by gcongr)⟩

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

theorem solution (G : Type*) [CommGroup G] : IsAmenable G := by
  apply Garrido.Lib.isAmenable_of_commGroup' <;> assumption
