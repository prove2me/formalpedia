-- Prove2me | solution 1 for Garrido.isAmenable_of_isAmenable_of_isAmenable_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T08:19:48.390152+00:00
-- url     : https://prove2.me/submissions/73decedd-0477-45a5-a4ea-3412eb1e27e5

import Mathlib
import Theorems.Thm_Garrido_isAmenable_tfae
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

theorem mean_mono (hm : IsFinitelyAdditiveMeasure m) {s t : Set X} (h : s ⊆ t) : m s ≤ m t := by
  have : t = s ∪ (t \ s) := (Set.union_sdiff_cancel h).symm
  rw [this, hm.2 _ _ Set.disjoint_sdiff_right]
  exact le_self_add

theorem mean_ne_top (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : Set X) :
    m s ≠ ∞ :=
  ne_top_of_le_ne_top (by rw [h1]; exact ENNReal.one_ne_top) (mean_mono m hm (subset_univ s))

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

/-- The general pull-back: an invariant mean on `Q`, a homomorphism `φ : G →* Q`, and a
`[0,1]`-valued finitely additive assignment `A ↦ F A` of bounded functions on `Q`, equivariant
along `φ`, give an invariant finitely additive probability measure on `G`,
namely `A ↦ ofReal (M (F A))`. -/
theorem mean_isAmenable_of_mean {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    (M : lp (fun _ : Q => ℝ) ∞ →ₗ[ℝ] ℝ) (hM : IsInvariantMean Q M)
    (F : Set G → lp (fun _ : Q => ℝ) ∞)
    (hF0 : ∀ A q, 0 ≤ (F A : Q → ℝ) q) (hFe : ∀ q, (F ∅ : Q → ℝ) q = 0)
    (hFu : ∀ q, (F univ : Q → ℝ) q = 1)
    (hFadd : ∀ A B, Disjoint A B → ∀ q, (F (A ∪ B) : Q → ℝ) q = (F A : Q → ℝ) q + (F B : Q → ℝ) q)
    (hFinv : ∀ (g : G) A q, (F (g • A) : Q → ℝ) q = (F A : Q → ℝ) ((φ g)⁻¹ * q)) :
    IsAmenable G := by
  refine ⟨fun A => ENNReal.ofReal (M (F A)), ⟨?_, fun A B hAB => ?_⟩, ?_, fun g A => ?_⟩
  · have : F ∅ = 0 := by ext q; simp [hFe]
    simp [this]
  · have : F (A ∪ B) = F A + F B := by ext q; simp [hFadd A B hAB]
    simp only [this, map_add]
    exact ENNReal.ofReal_add (hM.1 _ (hF0 A)) (hM.1 _ (hF0 B))
  · simp [hM.2.1 _ hFu]
  · have : F (g • A) = lshift (φ g) (F A) := by ext q; exact hFinv g A q
    simp only [this, hM.2.2]

/-- **(1) ⇒ (2) of Theorem 1.15**: integrating against an invariant finitely additive
probability measure is a left-invariant mean. -/
theorem mean_hasInvariantMean_of_isAmenable {G : Type*} [Group G] (h : IsAmenable G) :
    HasInvariantMean G :=
  ((Garrido.isAmenable_tfae G).out 0 1).mp h

end MeanToMeasure

/-! ### Theorem 1.15 -/


/-! ### The easy half of Tarski's theorem (Theorem 1.11, ⇒) -/

/-! ### Proposition 2.2(2) -/

theorem isAmenable_of_isAmenable_of_isAmenable_quotient' {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (hN : IsAmenable N) (hQ : IsAmenable (G ⧸ N)) :
    IsAmenable G := by
  obtain ⟨ν, hν, hν1, hνinv⟩ := hN
  obtain ⟨M, hM⟩ := mean_hasInvariantMean_of_isAmenable hQ
  have hbd : ∀ (A : Set G) (q : G ⧸ N),
      0 ≤ (ν {n : N | q.out * n ∈ A}).toReal ∧ (ν {n : N | q.out * n ∈ A}).toReal ≤ 1 := by
    intro A q
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have := mean_mono ν hν (subset_univ {n : N | q.out * n ∈ A})
    rw [hν1] at this
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
  refine mean_isAmenable_of_mean (QuotientGroup.mk' N) M hM
    (fun A => mean_ofUnit _ (hbd A)) (fun A q => (hbd A q).1) (fun q => ?_) (fun q => ?_)
    (fun A B hAB q => ?_) (fun g A q => ?_)
  · simp [hν.1]
  · simp [hν1]
  · simp only [mean_ofUnit_apply]
    have e : {n : N | q.out * n ∈ A ∪ B} = {n : N | q.out * n ∈ A} ∪ {n : N | q.out * n ∈ B} := by
      ext n; simp
    rw [e, hν.2 _ _ ?_, ENNReal.toReal_add (mean_ne_top ν hν hν1 _) (mean_ne_top ν hν hν1 _)]
    exact Set.disjoint_left.2 fun n h1 h2 => Set.disjoint_left.1 hAB h1 h2
  · simp only [mean_ofUnit_apply]
    -- the representative of `(gN)⁻¹ q` is `g⁻¹ * q.out * k` for some `k ∈ N`
    set a := g⁻¹ * q.out with ha
    have hmk : ((QuotientGroup.mk' N g)⁻¹ * q : G ⧸ N) = (a : G ⧸ N) := by
      rw [ha, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq']; rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N a
    rw [hmk, hk]
    have e1 : {n : N | q.out * n ∈ g • A} = {n : N | a * n ∈ A} := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, ha, mul_assoc]
    have e2 : {n : N | a * k * n ∈ A} = k⁻¹ • {n : N | a * n ∈ A} := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, smul_eq_mul,
        Subgroup.coe_mul, mul_assoc]
    rw [e1, e2, hνinv]

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

theorem solution {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (hN : IsAmenable N) (hQ : IsAmenable (G ⧸ N)) :
    IsAmenable G := by
  exact Garrido.Lib.isAmenable_of_isAmenable_of_isAmenable_quotient' N hN hQ
