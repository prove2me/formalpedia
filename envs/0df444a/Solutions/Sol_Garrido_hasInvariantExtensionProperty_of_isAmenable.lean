-- Prove2me | solution 1 for Garrido.hasInvariantExtensionProperty_of_isAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T08:19:46.458308+00:00
-- url     : https://prove2.me/submissions/b4f2e33f-8b82-498b-a88c-221c7875d7a9

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

/-- **(1) ⇒ (2) of Theorem 1.15**: integrating against an invariant finitely additive
probability measure is a left-invariant mean. -/
theorem mean_hasInvariantMean_of_isAmenable {G : Type*} [Group G] (h : IsAmenable G) :
    HasInvariantMean G :=
  ((Garrido.isAmenable_tfae G).out 0 1).mp h

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

open Classical in
/-- The "integral" of `f` against the mean `m`, `∞` when `f` is unbounded. -/
noncomputable def ext_int {G : Type*} (m : lp (fun _ : G => ℝ) ∞ →ₗ[ℝ] ℝ)
    (f : G → ℝ≥0∞) : ℝ≥0∞ :=
  if h : ext_Bdd f then ENNReal.ofReal (m (ext_toLp f h)) else ∞

theorem ext_bdd_add_iff {G : Type*} (f₁ f₂ : G → ℝ≥0∞) :
    ext_Bdd (f₁ + f₂) ↔ ext_Bdd f₁ ∧ ext_Bdd f₂ := by
  constructor
  · rintro ⟨C, hC, hle⟩
    exact ⟨⟨C, hC, fun g => le_trans le_self_add (hle g)⟩,
      ⟨C, hC, fun g => le_trans le_add_self (hle g)⟩⟩
  · rintro ⟨⟨C₁, hC₁, h₁⟩, ⟨C₂, hC₂, h₂⟩⟩
    exact ⟨C₁ + C₂, ENNReal.add_ne_top.2 ⟨hC₁, hC₂⟩, fun g => add_le_add (h₁ g) (h₂ g)⟩

theorem ext_ne_top_of_bdd {G : Type*} {f : G → ℝ≥0∞} (hf : ext_Bdd f) (g : G) : f g ≠ ∞ := by
  obtain ⟨C, hC, hle⟩ := hf
  exact ne_top_of_le_ne_top hC (hle g)

theorem ext_int_add {G : Type*} [Group G] {m : lp (fun _ : G => ℝ) ∞ →ₗ[ℝ] ℝ}
    (hm : IsInvariantMean G m) (f₁ f₂ : G → ℝ≥0∞) :
    ext_int m (f₁ + f₂) = ext_int m f₁ + ext_int m f₂ := by
  unfold ext_int
  by_cases h₁ : ext_Bdd f₁
  · by_cases h₂ : ext_Bdd f₂
    · have h : ext_Bdd (f₁ + f₂) := (ext_bdd_add_iff f₁ f₂).2 ⟨h₁, h₂⟩
      rw [dif_pos h, dif_pos h₁, dif_pos h₂]
      have hsplit : ext_toLp (f₁ + f₂) h = ext_toLp f₁ h₁ + ext_toLp f₂ h₂ := by
        apply lp.ext
        funext g
        simp only [ext_toLp_apply, Pi.add_apply, lp.coeFn_add]
        exact ENNReal.toReal_add (ext_ne_top_of_bdd h₁ g) (ext_ne_top_of_bdd h₂ g)
      rw [hsplit, map_add]
      exact ENNReal.ofReal_add (hm.1 _ fun g => ENNReal.toReal_nonneg)
        (hm.1 _ fun g => ENNReal.toReal_nonneg)
    · have h : ¬ ext_Bdd (f₁ + f₂) := fun h => h₂ ((ext_bdd_add_iff f₁ f₂).1 h).2
      rw [dif_neg h, dif_neg h₂, add_top]
  · have h : ¬ ext_Bdd (f₁ + f₂) := fun h => h₁ ((ext_bdd_add_iff f₁ f₂).1 h).1
    rw [dif_neg h, dif_neg h₁, top_add]

theorem ext_bdd_shift_iff {G : Type*} [Group G] (f : G → ℝ≥0∞) (h : G) :
    ext_Bdd (fun g => f (h⁻¹ * g)) ↔ ext_Bdd f := by
  constructor
  · rintro ⟨C, hC, hle⟩
    refine ⟨C, hC, fun g => ?_⟩
    have := hle (h * g)
    simpa only [inv_mul_cancel_left] using this
  · rintro ⟨C, hC, hle⟩
    exact ⟨C, hC, fun g => hle _⟩

theorem ext_int_shift {G : Type*} [Group G] {m : lp (fun _ : G => ℝ) ∞ →ₗ[ℝ] ℝ}
    (hm : IsInvariantMean G m) (f : G → ℝ≥0∞) (h : G) :
    ext_int m (fun g => f (h⁻¹ * g)) = ext_int m f := by
  unfold ext_int
  by_cases hf : ext_Bdd f
  · have hs : ext_Bdd (fun g => f (h⁻¹ * g)) := (ext_bdd_shift_iff f h).2 hf
    rw [dif_pos hf, dif_pos hs]
    have : ext_toLp (fun g => f (h⁻¹ * g)) hs = lshift h (ext_toLp f hf) := by
      apply lp.ext
      funext g
      rfl
    rw [this, hm.2.2]
  · have hs : ¬ ext_Bdd (fun g => f (h⁻¹ * g)) := fun hs => hf ((ext_bdd_shift_iff f h).1 hs)
    rw [dif_neg hf, dif_neg hs]

theorem ext_int_const {G : Type*} [Group G] {m : lp (fun _ : G => ℝ) ∞ →ₗ[ℝ] ℝ}
    (hm : IsInvariantMean G m) (c : ℝ≥0∞) :
    ext_int m (fun _ => c) = c := by
  unfold ext_int
  by_cases hc : c = ∞
  · have : ¬ ext_Bdd (fun _ : G => c) := by
      rintro ⟨C, hC, hle⟩
      exact hC (top_le_iff.1 (hc ▸ hle 1))
    rw [dif_neg this, hc]
  · have h1 : ext_Bdd (fun _ : G => (1 : ℝ≥0∞)) := ⟨1, ENNReal.one_ne_top, fun _ => le_rfl⟩
    have hb : ext_Bdd (fun _ : G => c) := ⟨c, hc, fun _ => le_rfl⟩
    rw [dif_pos hb]
    have : ext_toLp (fun _ : G => c) hb = c.toReal • ext_toLp (fun _ => 1) h1 := by
      apply lp.ext
      funext g
      simp
    rw [this, map_smul, hm.2.1 _ (fun g => by simp), smul_eq_mul, mul_one,
      ENNReal.ofReal_toReal hc]

/-- Theorem 2.6 from a left-invariant mean. -/
theorem ext_of_hasInvariantMean {G : Type u} [Group G] (hmean : HasInvariantMean G) :
    HasInvariantExtensionProperty.{u, v} G := by
  obtain ⟨m, hm⟩ := hmean
  intro X _ R μ ν hR hμ hext hν
  refine ⟨fun b => ext_int m (fun g => ν (g⁻¹ • b)), ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Set.smul_set_empty, hν.1]
    exact ext_int_const hm 0
  · intro s t hst
    have : (fun g : G => ν (g⁻¹ • (s ∪ t))) =
        (fun g => ν (g⁻¹ • s)) + (fun g => ν (g⁻¹ • t)) := by
      funext g
      rw [Set.smul_set_union, Pi.add_apply, hν.2 _ _ ((Set.disjoint_smul_set).2 hst)]
    simp only
    rw [this, ext_int_add hm]
  · intro s hs
    have : (fun g : G => ν (g⁻¹ • s)) = fun _ => μ s := by
      funext g
      rw [hext _ (hR _ _ hs), hμ _ _ hs]
    simp only
    rw [this, ext_int_const hm]
  · intro h b
    have : (fun g : G => ν (g⁻¹ • h • b)) = fun g => ν ((h⁻¹ * g)⁻¹ • b) := by
      funext g
      rw [smul_smul, mul_inv_rev, inv_inv]
    simp only
    rw [this, ext_int_shift hm (fun g => ν (g⁻¹ • b)) h]

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

/-- Theorem 2.6: `EXT`'s construction from an invariant mean, which `MEAN` supplies. -/
theorem hasInvariantExtensionProperty_of_isAmenable' {G : Type*} [Group G]
    (hG : IsAmenable G) :
    HasInvariantExtensionProperty G :=
  ext_of_hasInvariantMean (mean_hasInvariantMean_of_isAmenable hG)

end Garrido.Lib

open Garrido
open scoped ENNReal Pointwise

theorem solution {G : Type*} [Group G]
    (hG : IsAmenable G) :
    HasInvariantExtensionProperty G := by
  apply Garrido.Lib.hasInvariantExtensionProperty_of_isAmenable' <;> assumption
