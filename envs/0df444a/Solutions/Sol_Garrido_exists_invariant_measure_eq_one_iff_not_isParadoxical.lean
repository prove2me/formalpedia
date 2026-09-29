-- Prove2me | solution 1 for Garrido.exists_invariant_measure_eq_one_iff_not_isParadoxical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T19:10:13.786685+00:00
-- url     : https://prove2.me/submissions/da2a8af9-01a9-44df-9224-fe68f3e64386

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

/-- `(K • F) ∩ E` as a finset. -/
noncomputable def tarN (E : Set X) (K : Finset G) (F : Finset X) : Finset X :=
  (K • F).filter (· ∈ E)

theorem tar_mem_N {E : Set X} {K : Finset G} {F : Finset X} {y : X} :
    y ∈ tarN E K F ↔ y ∈ E ∧ ∃ k ∈ K, ∃ x ∈ F, k • x = y := by
  unfold tarN
  rw [Finset.mem_filter, Finset.mem_smul]
  tauto

theorem tar_equidecomposable_image [Nonempty X] (E : Set X) (f : X → X) (L : Finset G)
    (hinj : InjOn f E) (hdec : ∀ a ∈ E, ∃ l ∈ L, f a = l • a) :
    Equidecomposable G E (f '' E) :=
  ⟨{ toPartialEquiv := hinj.toPartialEquiv f E
     isDecompOn' := ⟨L, fun a ha => hdec a ha⟩ }, rfl, rfl⟩

theorem tar_equidecomposable_symm {A B : Set X} (h : Equidecomposable G A B) :
    Equidecomposable G B A := by
  obtain ⟨f, hs, ht⟩ := h
  exact ⟨f.symm, by simp [ht], by simp [hs]⟩

theorem tar_paradoxical_of_doubling (E : Set X) (hE : E.Nonempty) (L : Finset G)
    (hL : ∀ F : Finset X, (↑F : Set X) ⊆ E → 2 * F.card ≤ (tarN E L F).card) :
    IsParadoxical G E := by
  have : Nonempty X := ⟨hE.some⟩
  let t : (E × Bool) → Finset X := fun p => tarN E L {p.1.1}
  have hall : ∀ s : Finset (E × Bool), s.card ≤ (s.biUnion t).card := by
    intro s
    set F : Finset X := s.image (fun p => p.1.1) with hF
    have h1 : s.card ≤ 2 * F.card := by
      apply Finset.card_le_mul_card_image
      intro a _
      calc (s.filter fun p => p.1.1 = a).card ≤ (Finset.univ : Finset Bool).card := by
            apply Finset.card_le_card_of_injOn (fun p => p.2)
            · intro _ _; simp
            · intro p hp q hq hpq
              simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
              exact Prod.ext (Subtype.ext (hp.2.trans hq.2.symm)) hpq
        _ = 2 := rfl
    have h2 : s.biUnion t = tarN E L F := by
      ext y
      simp only [Finset.mem_biUnion, t, tar_mem_N, hF, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨p, hp, hyE, l, hl, x, rfl, rfl⟩
        exact ⟨hyE, l, hl, p.1.1, ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨hyE, l, hl, x, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p, hp, hyE, l, hl, p.1.1, rfl, rfl⟩
    have h3 : (↑F : Set X) ⊆ E := by
      intro x hx
      rw [hF, Finset.coe_image] at hx
      obtain ⟨p, -, rfl⟩ := hx
      exact p.1.2
    rw [h2]; exact h1.trans (hL F h3)
  obtain ⟨φ, hφinj, hφ⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  let f : Bool → X → X := fun b x => if hx : x ∈ E then φ (⟨x, hx⟩, b) else x
  have hfE : ∀ b, ∀ x (hx : x ∈ E), f b x = φ (⟨x, hx⟩, b) := fun b x hx => dif_pos hx
  have hfmem : ∀ b, ∀ x ∈ E, f b x ∈ E ∧ ∃ l ∈ L, f b x = l • x := by
    intro b x hx
    have := hφ (⟨x, hx⟩, b)
    simp only [t, tar_mem_N, Finset.mem_singleton] at this
    obtain ⟨hyE, l, hl, x', hx'x, hx'⟩ := this
    rw [hx'x] at hx'
    rw [hfE b x hx]
    exact ⟨hyE, l, hl, hx'.symm⟩
  have hfinj : ∀ b b', ∀ x ∈ E, ∀ y ∈ E, f b x = f b' y → b = b' ∧ x = y := by
    intro b b' x hx y hy hxy
    rw [hfE b x hx, hfE b' y hy] at hxy
    have := hφinj hxy
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
    exact ⟨this.2, this.1⟩
  have hinj : ∀ b, InjOn (f b) E := fun b x hx y hy hxy => (hfinj b b x hx y hy hxy).2
  have hsub : ∀ b, f b '' E ⊆ E := by
    rintro b _ ⟨x, hx, rfl⟩; exact (hfmem b x hx).1
  have hdisj : Disjoint (f false '' E) (f true '' E) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact absurd (hfinj true false y hy x hx hxy).1 (by decide)
  have hne : ∀ b, (f b '' E).Nonempty := fun b => hE.image _
  have hequi : ∀ b, Equidecomposable G (f b '' E) E := fun b =>
    tar_equidecomposable_symm
      (tar_equidecomposable_image E (f b) L (hinj b) fun a ha => (hfmem b a ha).2)
  refine ⟨f false '' E, f true '' E, hsub false, hsub true, ?_, ?_, hdisj, hequi false,
    hequi true⟩
  · intro h
    obtain ⟨y, hy⟩ := hne true
    have hyE : y ∈ f false '' E := by rw [h]; exact hsub true hy
    exact Set.disjoint_left.1 hdisj hyE hy
  · intro h
    obtain ⟨y, hy⟩ := hne false
    have hyE : y ∈ f true '' E := by rw [h]; exact hsub false hy
    exact Set.disjoint_left.1 hdisj hy hyE

/-! ### Step 2: expansion by a factor `(k+2)/(k+1)` gives doubling -/

theorem tar_N_one (E : Set X) (F : Finset X) (hF : (↑F : Set X) ⊆ E) :
    F ⊆ tarN E (1 : Finset G) F := by
  intro x hx
  rw [tar_mem_N]
  exact ⟨hF hx, 1, Finset.mem_one.2 rfl, x, hx, one_smul _ _⟩

theorem tar_N_comp (E : Set X) (K L : Finset G) (F : Finset X) :
    tarN E K (tarN E L F) ⊆ tarN E (K * L) F := by
  intro y hy
  rw [tar_mem_N] at hy ⊢
  obtain ⟨hyE, k, hk, x, hx, rfl⟩ := hy
  rw [tar_mem_N] at hx
  obtain ⟨-, l, hl, z, hz, rfl⟩ := hx
  exact ⟨hyE, k * l, Finset.mul_mem_mul hk hl, z, hz, mul_smul _ _ _⟩

theorem tar_numeric (k j : ℕ) : (k + 1) ^ j * (k + 1 + j) ≤ (k + 2) ^ j * (k + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (k + 1) ^ j ≤ (k + 2) ^ j := Nat.pow_le_pow_left (by omega) _
    rw [pow_succ, pow_succ]
    nlinarith [Nat.zero_le ((k + 1) ^ j), Nat.zero_le j]

theorem tar_doubling_of_expansion (E : Set X) (K : Finset G) (k : ℕ)
    (hK : ∀ F : Finset X, F.Nonempty → (↑F : Set X) ⊆ E →
      (k + 2) * F.card ≤ (k + 1) * (tarN E K F).card) :
    ∃ L : Finset G, ∀ F : Finset X, (↑F : Set X) ⊆ E → 2 * F.card ≤ (tarN E L F).card := by
  have hind : ∀ j : ℕ, ∀ F : Finset X, (↑F : Set X) ⊆ E →
      (k + 2) ^ j * F.card ≤ (k + 1) ^ j * (tarN E (K ^ j) F).card := by
    intro j
    induction j with
    | zero =>
      intro F hF
      simpa using Finset.card_le_card (tar_N_one (G := G) E F hF)
    | succ j ih =>
      intro F hF
      set F' := tarN E (K ^ j) F with hF'
      have hF'E : (↑F' : Set X) ⊆ E := fun y hy => (tar_mem_N.1 (Finset.mem_coe.1 hy)).1
      have hsub : tarN E K F' ⊆ tarN E (K ^ (j + 1)) F := by
        rw [pow_succ']; exact tar_N_comp E K (K ^ j) F
      have hc := Finset.card_le_card hsub
      rcases F'.eq_empty_or_nonempty with h0 | hne
      · have := ih F hF
        rw [← hF', h0, Finset.card_empty, mul_zero] at this
        have hF0 : F.card = 0 := by
          rcases Nat.mul_eq_zero.1 (Nat.eq_zero_of_le_zero this) with h | h
          · exact absurd h (by positivity)
          · exact h
        simp [hF0]
      · have h2 := hK F' hne hF'E
        have h3 := ih F hF
        rw [pow_succ, pow_succ]
        calc (k + 2) ^ j * (k + 2) * F.card = (k + 2) * ((k + 2) ^ j * F.card) := by ring
          _ ≤ (k + 2) * ((k + 1) ^ j * F'.card) := Nat.mul_le_mul_left _ h3
          _ = (k + 1) ^ j * ((k + 2) * F'.card) := by ring
          _ ≤ (k + 1) ^ j * ((k + 1) * (tarN E K F').card) := Nat.mul_le_mul_left _ h2
          _ ≤ (k + 1) ^ j * ((k + 1) * (tarN E (K ^ (j + 1)) F).card) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc)
          _ = (k + 1) ^ j * (k + 1) * (tarN E (K ^ (j + 1)) F).card := by ring
  refine ⟨K ^ (k + 1), fun F hF => ?_⟩
  have h1 := hind (k + 1) F hF
  have h2 := tar_numeric k (k + 1)
  have hpos : 0 < (k + 1) ^ (k + 1) := by positivity
  have : (k + 1) ^ (k + 1) * (2 * F.card) ≤ (k + 1) ^ (k + 1) * (tarN E (K ^ (k + 1)) F).card := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left this hpos

/-! ### Step 3: a non-paradoxical set has Følner sets inside it -/

theorem tar_folner (E : Set X) (hE : E.Nonempty) (hnp : ¬ IsParadoxical G E)
    (K : Finset G) (k : ℕ) :
    ∃ F : Finset X, F.Nonempty ∧ (↑F : Set X) ⊆ E ∧
      (k + 1) * (tarN E K F).card < (k + 2) * F.card := by
  by_contra h
  push Not at h
  obtain ⟨L, hL⟩ := tar_doubling_of_expansion E K k h
  exact hnp (tar_paradoxical_of_doubling E hE L hL)

/-! ### Step 4: normalised counting measures on Følner sets -/

/-- Normalised counting measure of a finset. -/
noncomputable def tarμ (F : Finset X) (A : Set X) : ℝ≥0∞ :=
  ((F.filter (· ∈ A)).card : ℝ≥0∞) / F.card

theorem tarμ_empty (F : Finset X) : tarμ F ∅ = 0 := by
  simp [tarμ]

theorem tarμ_union (F : Finset X) {s t : Set X} (hst : Disjoint s t) :
    tarμ F (s ∪ t) = tarμ F s + tarμ F t := by
  unfold tarμ
  rw [← ENNReal.add_div, ← Nat.cast_add, ← Finset.card_union_of_disjoint]
  · congr 3
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union]
    tauto
  · rw [Finset.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.1 hst (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hx').2

theorem tarμ_self {F : Finset X} {E : Set X} (hne : F.Nonempty) (hFE : (↑F : Set X) ⊆ E) :
    tarμ F E = 1 := by
  unfold tarμ
  have h : F.filter (· ∈ E) = F := Finset.filter_true_of_mem fun x hx => hFE hx
  rw [h]
  exact ENNReal.div_self (by simpa using hne.ne_empty) (by simp)

theorem tarμ_smul_le (E : Set X) (K : Finset G) (k : ℕ) (F : Finset X) (hne : F.Nonempty)
    (hN : (k + 1) * (tarN E K F).card < (k + 2) * F.card) (g : G) (h1 : (1 : G) ∈ K)
    (hg : g⁻¹ ∈ K) (hFE : (↑F : Set X) ⊆ E) (A : Set X) (hA : A ⊆ E) :
    tarμ F (g • A) ≤ tarμ F A + ((k : ℝ≥0∞) + 1)⁻¹ := by
  set N := tarN E K F with hNdef
  have hFN : F ⊆ N := by
    intro x hx
    rw [hNdef, tar_mem_N]
    exact ⟨hFE hx, 1, h1, x, hx, one_smul _ _⟩
  -- the counting inequality
  have hcount : (F.filter (· ∈ g • A)).card ≤ (F.filter (· ∈ A)).card + (N \ F).card := by
    refine le_trans ?_ (Finset.card_union_le _ _)
    apply Finset.card_le_card_of_injOn (fun y => g⁻¹ • y)
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_filter] at hy
      have hyA : g⁻¹ • y ∈ A := Set.mem_smul_set_iff_inv_smul_mem.1 hy.2
      rw [Finset.mem_coe, Finset.mem_union]
      by_cases hyF : g⁻¹ • y ∈ F
      · exact Or.inl (Finset.mem_filter.2 ⟨hyF, hyA⟩)
      · refine Or.inr (Finset.mem_sdiff.2 ⟨?_, hyF⟩)
        rw [hNdef, tar_mem_N]
        exact ⟨hA hyA, g⁻¹, hg, y, hy.1, rfl⟩
    · intro y _ z _ hyz
      exact smul_left_cancel _ hyz
  have hd : N.card = (N \ F).card + F.card := (Finset.card_sdiff_add_card_eq_card hFN).symm
  have hdk : (k + 1) * (N \ F).card ≤ F.card := by
    rw [hd] at hN; nlinarith
  have hF0 : (F.card : ℝ≥0∞) ≠ 0 := by simpa using hne.ne_empty
  have hk0 : ((k : ℝ≥0∞) + 1) ≠ 0 := by simp
  have hktop : ((k : ℝ≥0∞) + 1) ≠ ∞ := by simp
  unfold tarμ
  calc ((F.filter (· ∈ g • A)).card : ℝ≥0∞) / F.card
      ≤ (((F.filter (· ∈ A)).card : ℝ≥0∞) + (N \ F).card) / F.card := by
        gcongr; exact_mod_cast hcount
    _ = ((F.filter (· ∈ A)).card : ℝ≥0∞) / F.card + ((N \ F).card : ℝ≥0∞) / F.card :=
        ENNReal.add_div
    _ ≤ ((F.filter (· ∈ A)).card : ℝ≥0∞) / F.card + ((k : ℝ≥0∞) + 1)⁻¹ := by
        gcongr
        rw [ENNReal.div_le_iff hF0 (by simp)]
        calc ((N \ F).card : ℝ≥0∞) = ((k : ℝ≥0∞) + 1)⁻¹ * (((k : ℝ≥0∞) + 1) * (N \ F).card) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hk0 hktop, one_mul]
          _ ≤ ((k : ℝ≥0∞) + 1)⁻¹ * F.card := by
              gcongr; exact_mod_cast hdk

/-! ### Step 5: the limit measure -/

theorem tar_exists_pseudo (E : Set X) (hE : E.Nonempty) (hnp : ¬ IsParadoxical G E) :
    ∃ ν : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure ν ∧ ν E = 1 ∧
      ∀ (g : G) (A : Set X), A ⊆ E → ν (g • A) ≤ ν A := by
  have hex : ∀ i : Finset G × ℕ, ∃ F : Finset X, F.Nonempty ∧ (↑F : Set X) ⊆ E ∧
      (i.2 + 1) * (tarN E (i.1 ∪ {1} ∪ i.1⁻¹) F).card < (i.2 + 2) * F.card :=
    fun i => tar_folner E hE hnp _ _
  choose F hFne hFE hFN using hex
  let U : Ultrafilter (Finset G × ℕ) := Ultrafilter.of Filter.atTop
  have hU : (U : Filter (Finset G × ℕ)) ≤ Filter.atTop := Ultrafilter.of_le _
  have hlim : ∀ A : Set X, ∃ x, Filter.Tendsto (fun i => tarμ (F i) A) U (nhds x) := by
    intro A
    obtain ⟨x, -, hx⟩ :=
      isCompact_univ.ultrafilter_le_nhds (U.map (fun i => tarμ (F i) A)) (by simp)
    exact ⟨x, hx⟩
  choose ν hν using hlim
  refine ⟨ν, ⟨?_, ?_⟩, ?_, ?_⟩
  · have h0 : Filter.Tendsto (fun i => tarμ (F i) ∅) U (nhds 0) := by
      simp only [tarμ_empty]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (hν ∅) h0
  · intro s t hst
    have h' : Filter.Tendsto (fun i => tarμ (F i) (s ∪ t)) U (nhds (ν s + ν t)) := by
      simp only [tarμ_union _ hst]; exact (hν s).add (hν t)
    exact tendsto_nhds_unique (hν _) h'
  · have h1 : Filter.Tendsto (fun i => tarμ (F i) E) U (nhds 1) := by
      simp only [tarμ_self (hFne _) (hFE _)]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (hν E) h1
  · intro g A hA
    have key : ∀ k : ℕ, ν (g • A) ≤ ν A + ((k : ℝ≥0∞) + 1)⁻¹ := by
      intro k
      have hev : ∀ᶠ i in (U : Filter (Finset G × ℕ)),
          tarμ (F i) (g • A) ≤ tarμ (F i) A + ((k : ℝ≥0∞) + 1)⁻¹ := by
        apply hU
        filter_upwards [Filter.eventually_ge_atTop (({g} : Finset G), k)] with i hi
        have hg : g ∈ i.1 := hi.1 (Finset.mem_singleton_self g)
        refine (tarμ_smul_le E _ i.2 (F i) (hFne i) (hFN i) g ?_ ?_ (hFE i) A hA).trans ?_
        · simp
        · exact Finset.mem_union_right _ (Finset.inv_mem_inv hg)
        · gcongr
          exact_mod_cast hi.2
      exact le_of_tendsto_of_tendsto (hν _) ((hν A).add tendsto_const_nhds) hev
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by simpa using hε.ne')
    calc ν (g • A) ≤ ν A + ((n : ℝ≥0∞) + 1)⁻¹ := key n
      _ ≤ ν A + ε := by
        gcongr
        exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

/-! ### Step 6: extension to a `G`-invariant measure on all of `X` -/

/-- Admissible families for the extension: finitely supported, pairwise disjoint pieces of `A`. -/
def TarAdm (A : Set X) (p : Finset G × (G → Set X)) : Prop :=
  Pairwise (fun g h => Disjoint (p.2 g) (p.2 h)) ∧ (∀ g, p.2 g ⊆ A) ∧ (∀ g ∉ p.1, p.2 g = ∅)

variable (G) in
/-- The extension of `ν`. -/
noncomputable def tarExt (ν : Set X → ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨆ p : {p : Finset G × (G → Set X) // TarAdm A p}, ∑ g ∈ p.1.1, ν (g⁻¹ • p.1.2 g)

theorem tar_mono {ν : Set X → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure ν) {s t : Set X}
    (h : s ⊆ t) : ν s ≤ ν t := by
  have : ν t = ν s + ν (t \ s) := by
    conv_lhs => rw [← Set.union_sdiff_cancel h]
    exact hν.2 _ _ Set.disjoint_sdiff_right
  rw [this]; exact le_self_add

theorem tar_biUnion {ν : Set X → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure ν) (Φ : G → Set X)
    (hdisj : Pairwise (fun g h => Disjoint (Φ g) (Φ h))) (S : Finset G) :
    ν (⋃ g ∈ S, Φ g) = ∑ g ∈ S, ν (Φ g) := by
  induction S using Finset.induction_on with
  | empty => simp [hν.1]
  | insert a S ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha, ← ih]
    apply hν.2
    rw [Set.disjoint_iUnion₂_right]
    intro g hg
    exact hdisj (fun e => ha (e ▸ hg))

theorem tarAdm_nonempty (A : Set X) : Nonempty {p : Finset G × (G → Set X) // TarAdm A p} :=
  ⟨⟨(∅, fun _ => ∅), fun _ _ _ => by simp, fun _ => Set.empty_subset _, fun _ _ => rfl⟩⟩

theorem tarExt_smul_le {ν : Set X → ℝ≥0∞} (h : G) (A : Set X) :
    tarExt G ν (h • A) ≤ tarExt G ν A := by
  unfold tarExt
  refine iSup_le fun p => ?_
  obtain ⟨⟨S, Φ⟩, hdisj, hsub, hsupp⟩ := p
  dsimp only at hdisj hsub hsupp
  let S' := S.image (fun g => h⁻¹ * g)
  let Φ' : G → Set X := fun g => h⁻¹ • Φ (h * g)
  have hadm : TarAdm A (S', Φ') := by
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      exact Set.disjoint_smul_set.2 (hdisj (fun e => hab (mul_left_cancel e)))
    · intro g x hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, rfl⟩ := hsub _ hy
      simpa using hz
    · intro g hg
      have : h * g ∉ S := fun hmem =>
        hg (Finset.mem_image.2 ⟨h * g, hmem, by simp⟩)
      simp [Φ', hsupp _ this]
  refine le_trans (le_of_eq ?_) (le_iSup_of_le (⟨(S', Φ'), hadm⟩ :
    {p : Finset G × (G → Set X) // TarAdm A p}) le_rfl)
  simp only [S', Φ']
  rw [Finset.sum_image (fun a _ b _ e => mul_left_cancel e)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [smul_smul, mul_assoc]

theorem tarExt_union {ν : Set X → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure ν) {B C : Set X}
    (hBC : Disjoint B C) : tarExt G ν (B ∪ C) = tarExt G ν B + tarExt G ν C := by
  apply le_antisymm
  · unfold tarExt
    refine iSup_le fun p => ?_
    obtain ⟨⟨S, Φ⟩, hdisj, hsub, hsupp⟩ := p
    dsimp only at hdisj hsub hsupp
    have hB : TarAdm B (S, fun g => Φ g ∩ B) :=
      ⟨fun a b hab => (hdisj hab).mono Set.inter_subset_left Set.inter_subset_left,
        fun g => Set.inter_subset_right, fun g hg => by simp [hsupp g hg]⟩
    have hC : TarAdm C (S, fun g => Φ g ∩ C) :=
      ⟨fun a b hab => (hdisj hab).mono Set.inter_subset_left Set.inter_subset_left,
        fun g => Set.inter_subset_right, fun g hg => by simp [hsupp g hg]⟩
    calc ∑ g ∈ S, ν (g⁻¹ • Φ g)
        = ∑ g ∈ S, ν (g⁻¹ • (Φ g ∩ B)) + ∑ g ∈ S, ν (g⁻¹ • (Φ g ∩ C)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [← hν.2 _ _ (Set.disjoint_smul_set.2
            (hBC.mono Set.inter_subset_right Set.inter_subset_right)),
            ← Set.smul_set_union, ← Set.inter_union_distrib_left,
            Set.inter_eq_left.2 (hsub g)]
      _ ≤ _ := add_le_add
          (le_iSup_of_le (⟨_, hB⟩ : {p : Finset G × (G → Set X) // TarAdm B p}) le_rfl)
          (le_iSup_of_le (⟨_, hC⟩ : {p : Finset G × (G → Set X) // TarAdm C p}) le_rfl)
  · unfold tarExt
    have := tarAdm_nonempty (G := G) B
    have := tarAdm_nonempty (G := G) C
    refine ENNReal.iSup_add_iSup_le fun p q => ?_
    obtain ⟨⟨S, Φ⟩, hdΦ, hsΦ, hpΦ⟩ := p
    obtain ⟨⟨T, Ψ⟩, hdΨ, hsΨ, hpΨ⟩ := q
    dsimp only at hdΦ hsΦ hpΦ hdΨ hsΨ hpΨ
    have hadm : TarAdm (B ∪ C) (S ∪ T, fun g => Φ g ∪ Ψ g) := by
      refine ⟨fun a b hab => ?_, fun g => Set.union_subset_union (hsΦ g) (hsΨ g),
        fun g hg => ?_⟩
      · exact Set.disjoint_union_left.2
          ⟨Set.disjoint_union_right.2 ⟨hdΦ hab, hBC.mono (hsΦ a) (hsΨ b)⟩,
            Set.disjoint_union_right.2 ⟨hBC.symm.mono (hsΨ a) (hsΦ b), hdΨ hab⟩⟩
      · simp only [Finset.mem_union, not_or] at hg
        simp [hpΦ g hg.1, hpΨ g hg.2]
    refine le_trans (le_of_eq ?_) (le_iSup_of_le (⟨_, hadm⟩ :
      {p : Finset G × (G → Set X) // TarAdm (B ∪ C) p}) le_rfl)
    dsimp only
    rw [Finset.sum_subset (Finset.subset_union_left : S ⊆ S ∪ T)
        (fun g _ hg => by simp [hpΦ g hg, hν.1]),
      Finset.sum_subset (Finset.subset_union_right : T ⊆ S ∪ T)
        (fun g _ hg => by simp [hpΨ g hg, hν.1]),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Set.smul_set_union, hν.2 _ _ (Set.disjoint_smul_set.2 (hBC.mono (hsΦ g) (hsΨ g)))]

theorem tarExt_empty {ν : Set X → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure ν) :
    tarExt G ν ∅ = 0 := by
  unfold tarExt
  refine le_antisymm (iSup_le fun p => ?_) bot_le
  obtain ⟨⟨S, Φ⟩, -, hsub, -⟩ := p
  dsimp only at hsub
  refine le_of_eq (Finset.sum_eq_zero fun g _ => ?_)
  simp [Set.subset_empty_iff.1 (hsub g), hν.1]

theorem tar_extension (E : Set X) (ν : Set X → ℝ≥0∞) (hν : IsFinitelyAdditiveMeasure ν)
    (hνE : ν E = 1) (hps : ∀ (g : G) (A : Set X), A ⊆ E → ν (g • A) ≤ ν A) :
    IsFinitelyAdditiveMeasure (tarExt G ν) ∧ tarExt G ν E = 1 ∧ IsInvariant G (tarExt G ν) := by
  refine ⟨⟨tarExt_empty hν, fun s t hst => tarExt_union hν hst⟩, ?_, ?_⟩
  · apply le_antisymm
    · unfold tarExt
      refine iSup_le fun p => ?_
      obtain ⟨⟨S, Φ⟩, hdisj, hsub, -⟩ := p
      dsimp only at hdisj hsub
      calc ∑ g ∈ S, ν (g⁻¹ • Φ g) ≤ ∑ g ∈ S, ν (Φ g) :=
            Finset.sum_le_sum fun g _ => hps g⁻¹ (Φ g) (hsub g)
        _ = ν (⋃ g ∈ S, Φ g) := (tar_biUnion hν Φ hdisj S).symm
        _ ≤ ν E := tar_mono hν (Set.iUnion₂_subset fun g _ => hsub g)
        _ = 1 := hνE
    · unfold tarExt
      have hadm : TarAdm E (({1} : Finset G), fun g => if g = 1 then E else ∅) := by
        refine ⟨fun a b hab => ?_, fun g => ?_, fun g hg => ?_⟩
        · by_cases ha : a = 1 <;> by_cases hb : b = 1 <;> simp_all
        · dsimp only; split_ifs <;> simp
        · simp only [Finset.mem_singleton] at hg; simp [hg]
      refine le_trans (le_of_eq ?_) (le_iSup_of_le (⟨_, hadm⟩ :
        {p : Finset G × (G → Set X) // TarAdm E p}) le_rfl)
      simp [hνE]
  · intro g s
    apply le_antisymm (tarExt_smul_le g s)
    have := tarExt_smul_le (ν := ν) g⁻¹ (g • s)
    rwa [inv_smul_smul] at this

/-! ### The easy direction -/

theorem tar_measure_image (m : Set X → ℝ≥0∞) (hm : IsFinitelyAdditiveMeasure m)
    (hinv : IsInvariant G m) (S : Finset G) :
    ∀ (f : X → X) (A : Set X), InjOn f A → (∀ a ∈ A, ∃ g ∈ S, f a = g • a) →
      m (f '' A) = m A := by
  induction S using Finset.induction_on with
  | empty =>
    intro f A _ hdec
    have hA : A = ∅ := Set.eq_empty_of_forall_notMem fun a ha => by
      obtain ⟨g, hg, -⟩ := hdec a ha
      simp at hg
    subst hA
    simp
  | insert g T hgT ih =>
    intro f A hinj hdec
    set A₁ := {a ∈ A | f a = g • a} with hA₁
    set A₂ := {a ∈ A | f a ≠ g • a} with hA₂
    have hA : A = A₁ ∪ A₂ := by
      ext a; simp only [hA₁, hA₂, Set.mem_union, Set.mem_ofPred_eq]; tauto
    have hdisjA : Disjoint A₁ A₂ := by
      rw [Set.disjoint_left]; intro a h1 h2; exact h2.2 h1.2
    have hsub₁ : A₁ ⊆ A := fun a ha => ha.1
    have hsub₂ : A₂ ⊆ A := fun a ha => ha.1
    have himg₁ : f '' A₁ = g • A₁ := by
      rw [← Set.image_smul]
      exact Set.image_congr fun a ha => ha.2
    have h₂ : m (f '' A₂) = m A₂ := by
      refine ih f A₂ (hinj.mono hsub₂) fun a ha => ?_
      obtain ⟨g', hg', he⟩ := hdec a ha.1
      rcases Finset.mem_insert.1 hg' with rfl | hT
      · exact absurd he ha.2
      · exact ⟨g', hT, he⟩
    have hdisjI : Disjoint (f '' A₁) (f '' A₂) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have := hinj (hsub₂ hb) (hsub₁ ha) hab
      subst this
      exact Set.disjoint_left.1 hdisjA ha hb
    calc m (f '' A) = m (f '' A₁ ∪ f '' A₂) := by rw [hA, Set.image_union]
      _ = m (f '' A₁) + m (f '' A₂) := hm.2 _ _ hdisjI
      _ = m A₁ + m A₂ := by rw [himg₁, hinv, h₂]
      _ = m A := by rw [← hm.2 _ _ hdisjA, ← hA]

theorem tar_not_paradoxical_of_measure (E : Set X) (m : Set X → ℝ≥0∞)
    (hm : IsFinitelyAdditiveMeasure m) (hmE : m E = 1) (hinv : IsInvariant G m) :
    ¬ IsParadoxical G E := by
  have key : ∀ A : Set X, Equidecomposable G A E → m A = 1 := by
    rintro A ⟨f, hs, ht⟩
    have h := tar_measure_image m hm hinv f.witness f f.source f.toPartialEquiv.injOn
      f.isDecompOn
    rw [f.toPartialEquiv.image_source_eq_target] at h
    rw [← hs, ← h, ht, hmE]
  rintro ⟨A, B, hAE, hBE, -, -, hAB, hA, hB⟩
  have h1 := key A hA
  have h2 := key B hB
  have hle := tar_mono hm (Set.union_subset hAE hBE)
  rw [hm.2 _ _ hAB, h1, h2, hmE] at hle
  exact absurd hle (by norm_num)

end Tarski

-- Theorem 1.11 (p. 3), Tarski.
theorem exists_invariant_measure_eq_one_iff_not_isParadoxical'
    {G X : Type*} [Group G] [MulAction G X] (E : Set X) (hE : E.Nonempty) :
    (∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m E = 1 ∧
        IsInvariant G m) ↔ ¬ IsParadoxical G E := by
  constructor
  · rintro ⟨m, hm, hmE, hinv⟩
    exact tar_not_paradoxical_of_measure E m hm hmE hinv
  · intro hnp
    obtain ⟨ν, hν, hνE, hps⟩ := tar_exists_pseudo E hE hnp
    obtain ⟨h1, h2, h3⟩ := tar_extension E ν hν hνE hps
    exact ⟨tarExt G ν, h1, h2, h3⟩

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
    {G X : Type*} [Group G] [MulAction G X] (E : Set X) (hE : E.Nonempty) :
    (∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m E = 1 ∧
        IsInvariant G m) ↔ ¬ IsParadoxical G E := by
  apply Garrido.Lib.exists_invariant_measure_eq_one_iff_not_isParadoxical' <;> assumption
