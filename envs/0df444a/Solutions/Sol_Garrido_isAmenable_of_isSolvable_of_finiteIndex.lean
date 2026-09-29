-- Prove2me | solution 1 for Garrido.isAmenable_of_isSolvable_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T08:19:49.780796+00:00
-- url     : https://prove2.me/submissions/4beb6b34-e522-4e89-872e-76d9c875151b

import Mathlib
import Theorems.Thm_Garrido_isAmenable_of_commGroup
import Theorems.Thm_Garrido_isAmenable_of_finite
import Theorems.Thm_Garrido_isAmenable_of_isAmenable_of_isAmenable_quotient
import Theorems.Thm_Garrido_isAmenable_subgroup
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Foelner
import Definitions.Def_Chou_Growth

universe u v

namespace Garrido.Lib

open scoped ENNReal Pointwise Topology
open Filter Set Garrido

alias isAmenable_of_commGroup' := Garrido.isAmenable_of_commGroup

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

theorem clo_preimage_smul {G K : Type*} [Group G] [Group K] (f : G → K) (k : K) (g : G)
    (hf : ∀ x, f (g * x) = k * f x) (A : Set K) :
    f ⁻¹' (k • A) = g • (f ⁻¹' A) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have : f x = k * f (g⁻¹ * x) := by rw [← hf, mul_inv_cancel_left]
  rw [this, inv_mul_cancel_left]

theorem clo_isAmenable_of_push {G K : Type*} [Group G] [Group K] (hG : IsAmenable G)
    (f : G → K) (hf : ∀ k : K, ∃ g : G, ∀ x, f (g * x) = k * f x) : IsAmenable K := by
  obtain ⟨m, ⟨h0, hadd⟩, h1, hinv⟩ := hG
  refine ⟨fun A => m (f ⁻¹' A), ⟨by simpa using h0, fun s t hst => ?_⟩, by simpa using h1, ?_⟩
  · simp only [Set.preimage_union]
    exact hadd _ _ (hst.preimage f)
  · intro k A
    obtain ⟨g, hg⟩ := hf k
    simp only
    rw [clo_preimage_smul f k g hg A]
    exact hinv g _

theorem clo_isAmenable_of_surjective {G K : Type*} [Group G] [Group K] (hG : IsAmenable G)
    (f : G →* K) (hf : Function.Surjective f) : IsAmenable K :=
  clo_isAmenable_of_push hG f fun k => by
    obtain ⟨g, rfl⟩ := hf k
    exact ⟨g, fun x => map_mul f g x⟩

theorem clo_isAmenable_of_mulEquiv {G K : Type*} [Group G] [Group K] (hG : IsAmenable G)
    (e : G ≃* K) : IsAmenable K :=
  clo_isAmenable_of_surjective hG e.toMonoidHom e.surjective

/-! ### Example 2.1 -/

alias isAmenable_of_finite' := Garrido.isAmenable_of_finite

/-! ### Proposition 2.2(1) -/

alias isAmenable_subgroup' := Garrido.isAmenable_subgroup

/-! ### Proposition 2.2(3) -/


/-! ### Corollary 2.4, from Propositions 2.3 and 2.2(2) taken as hypotheses -/

section Hyp

variable (h23 : ∀ (K : Type u) [CommGroup K], IsAmenable K)
  (h222 : ∀ (K : Type u) [Group K] (N : Subgroup K) [N.Normal],
    IsAmenable N → IsAmenable (K ⧸ N) → IsAmenable K)
include h23 h222

/-- One step of the derived series: if `D_{k+1}` is amenable then so is `D_k`. -/
theorem clo_derived_step {K : Type u} [Group K] (k : ℕ)
    (ih : IsAmenable (derivedSeries K (k + 1))) : IsAmenable (derivedSeries K k) := by
  set D := derivedSeries K k
  set D' := derivedSeries K (k + 1)
  have hle : D' ≤ D := derivedSeries_antitone K (Nat.le_succ k)
  have : D'.Normal := derivedSeries_normal K (k + 1)
  set N : Subgroup D := D'.subgroupOf D
  have hN : IsAmenable N := clo_isAmenable_of_mulEquiv ih (Subgroup.subgroupOfEquivOfLe hle).symm
  have hcomm : commutator D ≤ N.comap (MonoidHom.id D) := by
    rw [commutator, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    simp only [Subgroup.comap_id, N, Subgroup.mem_subgroupOf]
    rw [show D' = ⁅D, D⁆ from derivedSeries_succ K k]
    convert Subgroup.commutator_mem_commutator g₁.2 g₂.2 using 1
    simp [commutatorElement_def]
  have hQ : IsAmenable (D ⧸ N) := by
    refine clo_isAmenable_of_surjective (h23 (Abelianization D))
      (QuotientGroup.map (commutator D) N (MonoidHom.id D) hcomm) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H a => exact ⟨Abelianization.of a, rfl⟩
  exact h222 D N hN hQ

theorem clo_isAmenable_of_isSolvable {K : Type u} [Group K] (hK : Group.IsSolvable K) :
    IsAmenable K := by
  obtain ⟨n, hn⟩ := hK.solvable
  have key : ∀ j k, k + j = n → IsAmenable (derivedSeries K k) := by
    intro j
    induction j with
    | zero =>
      intro k hk
      simp only [add_zero] at hk
      subst hk
      have : Subsingleton (derivedSeries K k) := by
        refine ⟨fun a b => Subtype.ext ?_⟩
        have ha : (a : K) ∈ (⊥ : Subgroup K) := hn ▸ a.2
        have hb : (b : K) ∈ (⊥ : Subgroup K) := hn ▸ b.2
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      have : Finite (derivedSeries K k) := Finite.of_subsingleton
      exact isAmenable_of_finite' _
    | succ j ihj =>
      intro k hk
      exact clo_derived_step h23 h222 k (ihj (k + 1) (by omega))
  have h0 := key n 0 (by omega)
  rw [derivedSeries_zero] at h0
  exact clo_isAmenable_of_mulEquiv h0 Subgroup.topEquiv

/-- Corollary 2.4, with Propositions 2.3 and 2.2(2) as hypotheses. -/
theorem clo_isAmenable_of_isSolvable_of_finiteIndex {G : Type u} [Group G]
    (H : Subgroup G) [H.FiniteIndex] (hH : Group.IsSolvable H) :
    IsAmenable G := by
  have hHa : IsAmenable H := clo_isAmenable_of_isSolvable h23 h222 hH
  set C := H.normalCore
  have hCa : IsAmenable C :=
    clo_isAmenable_of_mulEquiv (isAmenable_subgroup' hHa (C.subgroupOf H))
      (Subgroup.subgroupOfEquivOfLe (Subgroup.normalCore_le H))
  have : Finite (G ⧸ C) := inferInstance
  exact h222 G C hCa (isAmenable_of_finite' _)

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

alias isAmenable_of_isAmenable_of_isAmenable_quotient' := Garrido.isAmenable_of_isAmenable_of_isAmenable_quotient

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


/-- Corollary 2.4: `CLO` reduced it to Propositions 2.3 (`AB`) and 2.2(2) (`MEAN`). -/
theorem isAmenable_of_isSolvable_of_finiteIndex' {G : Type*} [Group G]
    (H : Subgroup G) [H.FiniteIndex] (hH : Group.IsSolvable H) :
    IsAmenable G :=
  clo_isAmenable_of_isSolvable_of_finiteIndex (fun K _ => isAmenable_of_commGroup' K)
    (fun _ _ N _ => isAmenable_of_isAmenable_of_isAmenable_quotient' N) H hH

end Garrido.Lib

open Garrido
open scoped ENNReal Pointwise

theorem solution {G : Type*} [Group G]
    (H : Subgroup G) [H.FiniteIndex] (hH : Group.IsSolvable H) :
    IsAmenable G := by
  exact Garrido.Lib.isAmenable_of_isSolvable_of_finiteIndex' H hH
