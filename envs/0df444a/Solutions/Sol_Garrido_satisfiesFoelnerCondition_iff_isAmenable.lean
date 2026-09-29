-- Prove2me | solution 1 for Garrido.satisfiesFoelnerCondition_iff_isAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T08:19:51.569799+00:00
-- url     : https://prove2.me/submissions/b1149389-d94f-4c3c-9b9e-8301aa6b30a8

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

end Garrido.Lib

namespace Garrido.Lib

open scoped ENNReal Pointwise symmDiff Topology
open MeasureTheory Filter Set

theorem fol_count_div {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    (T F : Set G) (hT : T.Finite) (hF : F.Finite) (hFne : F.Nonempty) :
    Measure.count T / Measure.count F = ENNReal.ofReal ((T.ncard : ℝ) / (F.ncard : ℝ)) := by
  rw [Measure.count_apply_finite T hT, Measure.count_apply_finite F hF]
  have hpos : (0 : ℝ) < F.ncard := by
    exact_mod_cast (Set.ncard_pos hF).2 hFne
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    Set.ncard_eq_toFinset_card T hT, Set.ncard_eq_toFinset_card F hF]

theorem fol_isAmenable_of_satisfiesFoelnerCondition {G : Type*} [Group G]
    (h : SatisfiesFoelnerCondition G) : IsAmenable G := by
  let _ : MeasurableSpace G := ⊤
  have hmeas : ∀ s : Set G, MeasurableSet s := fun _ => trivial
  have _ : MeasurableSingletonClass G := ⟨fun _ => trivial⟩
  have _ : SMulInvariantMeasure G G (Measure.count : Measure G) := ⟨fun c s _ => by
    rw [Measure.count_apply (hmeas _), Measure.count_apply (hmeas _)]
    exact (MulAction.injective c⁻¹).encard_image s ▸ by
      rw [Set.image_smul, Set.preimage_smul]⟩
  have _ : NeBot (maxFoelner G (Measure.count : Measure G)) := by
    rw [maxFoelner, inf_comm, inf_principal_neBot_iff]
    intro U hU
    obtain ⟨I, hI, V, hV, -, hUV, -⟩ := mem_iInf'.1 hU
    have hε : ∀ g ∈ I, ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ s : Set G,
        Measure.count ((g • s) ∆ s) / Measure.count s < ε → s ∈ V g := by
      intro g _
      obtain ⟨W, hW, hWV⟩ := mem_comap.1 (hV g)
      obtain ⟨ε, hε, hεW⟩ := ENNReal.nhds_zero_basis.mem_iff.1 hW
      exact ⟨ε, hε, fun s hs => hWV (hεW hs)⟩
    choose ε hεpos hεV using hε
    have hev : ∀ᶠ n : ℕ in atTop, ∀ g ∈ I, ∀ hg : g ∈ I, ((n : ℝ≥0∞))⁻¹ < ε g hg := by
      rw [eventually_all_finite hI]
      intro g hg
      filter_upwards [ENNReal.tendsto_inv_nat_nhds_zero.eventually (gt_mem_nhds (hεpos g hg))]
        with n hn _
      exact hn
    obtain ⟨n, hn, hn1⟩ := (hev.and (eventually_ge_atTop 1)).exists
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    obtain ⟨F, hF, hFne, hFA⟩ := h I hI (1 / (n : ℝ)) (by positivity)
    refine ⟨F, ?_, hmeas F, ?_, ?_⟩
    · rw [hUV, mem_iInter₂]
      intro g hg
      apply hεV g hg
      refine lt_of_le_of_lt ?_ (hn g hg hg)
      rw [fol_count_div _ _ ((hF.smul_set).symmDiff hF) hF hFne]
      calc ENNReal.ofReal _ ≤ ENNReal.ofReal (1 / (n : ℝ)) := ENNReal.ofReal_le_ofReal (hFA g hg)
        _ = (n : ℝ≥0∞)⁻¹ := by
          rw [one_div, ENNReal.ofReal_inv_of_pos hnpos, ENNReal.ofReal_natCast]
    · rw [Ne, Measure.count_eq_zero_iff]; exact hFne.ne_empty
    · exact (Measure.count_apply_lt_top.2 hF).ne
  obtain ⟨m, h1, h2, h3⟩ :=
    IsFoelner.amenable (isFoelner_maxFoelner G (Measure.count : Measure G))
  have h0 : m ∅ = 0 := by
    have := h2 Set.univ ∅ (hmeas _) (Set.disjoint_empty _)
    rw [Set.union_empty, h1] at this
    have h' : (1 : ℝ≥0∞) + m ∅ = 1 + 0 := by rw [add_zero]; exact this.symm
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h'
  exact ⟨m, ⟨h0, fun s t hst => h2 s t (hmeas t) hst⟩, h1, h3⟩


section Growth

variable {G : Type*} [Group G]

end Growth

end Garrido.Lib

namespace Garrido.Lib

open scoped Pointwise symmDiff ENNReal
open Finset

section Layer

variable {G : Type*} [Group G] [DecidableEq G]

/-- The indicator function of a finite set, as a real-valued function. -/
noncomputable def namInd (S : Finset G) (x : G) : ℝ := if x ∈ S then 1 else 0

omit [Group G] in
lemma nam_abs_split {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) (S : Finset G)
    (hS : ∀ x, x ∈ S ↔ 0 < f x) (m : ℝ) (hm : ∀ x ∈ S, m ≤ f x) (x y : G) :
    |f x - f y| = m * |namInd S x - namInd S y|
      + |(f x - m * namInd S x) - (f y - m * namInd S y)| := by
  have h0 : ∀ z, z ∉ S → f z = 0 := fun z hz =>
    le_antisymm (not_lt.1 (fun h => hz ((hS z).2 h))) (hf z)
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp [namInd, hx, hy]
  · have := hm x hx
    rw [h0 y hy]; simp only [namInd, hx, hy, if_true, if_false]
    have h2 : 0 ≤ f x - m := by linarith
    norm_num [abs_of_nonneg (hf x), abs_of_nonneg h2]
  · have := hm y hy
    rw [h0 x hx]; simp only [namInd, hx, hy, if_true, if_false]
    have h2 : m - f y ≤ 0 := by linarith
    norm_num [abs_of_nonneg (hf y), abs_of_nonpos h2]
  · simp [namInd, hx, hy, h0 x hx, h0 y hy]

omit [Group G] in
lemma nam_sum_ind {S T : Finset G} (h : S ⊆ T) : ∑ x ∈ T, namInd S x = S.card := by
  unfold namInd
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 h]; simp

lemma nam_layer (A S0 T : Finset G) (hS0T : S0 ⊆ T) (ε : ℝ) :
    ∀ n : ℕ, ∀ f : G → ℝ, (∀ x, 0 ≤ f x) → (∀ x, 0 < f x → x ∈ S0) →
      (S0.filter (fun x => 0 < f x)).card ≤ n → (∃ x, 0 < f x) →
      ∑ a ∈ A, ∑ x ∈ T, |f x - f (a⁻¹ * x)| ≤ ε * ∑ x ∈ T, f x →
      ∃ F : Finset G, F.Nonempty ∧ F ⊆ S0 ∧
        ∑ a ∈ A, ∑ x ∈ T, |namInd F x - namInd F (a⁻¹ * x)| ≤ ε * F.card := by
  intro n
  induction n with
  | zero =>
    intro f _ hsupp hcard hex _
    obtain ⟨x, hx⟩ := hex
    have : x ∈ S0.filter (fun x => 0 < f x) := Finset.mem_filter.2 ⟨hsupp x hx, hx⟩
    have := Finset.card_pos.2 ⟨x, this⟩
    omega
  | succ n ih =>
    intro f hf hsupp hcard hex hD
    set S := S0.filter (fun x => 0 < f x) with hSdef
    have hSmem : ∀ x, x ∈ S ↔ 0 < f x := fun x =>
      ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨hsupp x h, h⟩⟩
    have hSne : S.Nonempty := by
      obtain ⟨x, hx⟩ := hex; exact ⟨x, (hSmem x).2 hx⟩
    set m := S.inf' hSne f with hmdef
    have hm : ∀ x ∈ S, m ≤ f x := fun x hx => Finset.inf'_le f hx
    obtain ⟨x0, hx0S, hx0⟩ := Finset.exists_mem_eq_inf' hSne f
    have hm0 : 0 < m := by rw [hmdef, hx0]; exact (hSmem x0).1 hx0S
    set g : G → ℝ := fun x => f x - m * namInd S x with hgdef
    have hSsub : S ⊆ S0 := Finset.filter_subset _ _
    have hsplit : ∑ a ∈ A, ∑ x ∈ T, |f x - f (a⁻¹ * x)| =
        m * ∑ a ∈ A, ∑ x ∈ T, |namInd S x - namInd S (a⁻¹ * x)| +
          ∑ a ∈ A, ∑ x ∈ T, |g x - g (a⁻¹ * x)| := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact nam_abs_split hf S hSmem m hm x (a⁻¹ * x)
    by_cases hcase : ∑ a ∈ A, ∑ x ∈ T, |namInd S x - namInd S (a⁻¹ * x)| ≤ ε * S.card
    · exact ⟨S, hSne, hSsub, hcase⟩
    push Not at hcase
    have hST : S ⊆ T := hSsub.trans hS0T
    have hN : ∑ x ∈ T, f x = m * S.card + ∑ x ∈ T, g x := by
      rw [← nam_sum_ind hST, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [hgdef]
    have hg0 : ∀ x, 0 ≤ g x := by
      intro x
      by_cases hx : x ∈ S
      · simp [hgdef, namInd, hx, hm x hx]
      · simp [hgdef, namInd, hx, hf x]
    have hgf : ∀ x, g x ≤ f x := by
      intro x; simp only [hgdef, namInd]; split_ifs <;> linarith
    by_cases hgex : ∃ x, 0 < g x
    · refine ih g hg0 (fun x hx => hsupp x ((lt_of_lt_of_le hx (hgf x)))) ?_ hgex ?_
      · have hsub : S0.filter (fun x => 0 < g x) ⊆ S.erase x0 := by
          intro x hx
          have hx' := (Finset.mem_filter.1 hx).2
          refine Finset.mem_erase.2 ⟨?_, (hSmem x).2 (lt_of_lt_of_le hx' (hgf x))⟩
          rintro rfl
          have : g x = 0 := by
            simp only [hgdef, namInd, if_pos hx0S]; rw [hmdef, hx0]; ring
          linarith
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hx0S] at this
        omega
      · have := mul_lt_mul_of_pos_left hcase hm0
        have e : ε * (m * S.card) = m * (ε * S.card) := by ring
        rw [hsplit, hN, mul_add] at hD
        linarith
    · push Not at hgex
      have hgz : ∀ x, g x = 0 := fun x => le_antisymm (hgex x) (hg0 x)
      have := mul_lt_mul_of_pos_left hcase hm0
      simp only [hgz, sub_self, abs_zero, Finset.sum_const_zero, add_zero] at hsplit hN
      have e : ε * (m * S.card) = m * (ε * S.card) := by ring
      rw [hsplit, hN] at hD
      linarith

lemma nam_card_symmDiff (F T : Finset G) (a : G) (hF : F ⊆ T) (haF : ∀ x ∈ F, a * x ∈ T) :
    (((a • (F : Set G)) ∆ (F : Set G)).ncard : ℝ) =
      ∑ x ∈ T, |namInd F x - namInd F (a⁻¹ * x)| := by
  have hcoe : (a • (F : Set G)) ∆ (F : Set G) = ((a • F) ∆ F : Finset G) := by
    push_cast; rfl
  have hmem : ∀ x, x ∈ a • F ↔ a⁻¹ * x ∈ F := by
    intro x
    rw [Finset.mem_smul_finset]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa [smul_eq_mul] using hy
    · intro h; exact ⟨a⁻¹ * x, h, by simp [smul_eq_mul]⟩
  have hsub : (a • F) ∆ F ⊆ T := by
    intro x hx
    rcases Finset.mem_symmDiff.1 hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · have := haF _ ((hmem x).1 h1); simpa using this
    · exact hF h1
  rw [hcoe, Set.ncard_coe_finset, Finset.card_eq_sum_ones, Nat.cast_sum,
    ← Finset.inter_eq_right.2 hsub, ← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h1 : x ∈ F <;> by_cases h2 : a⁻¹ * x ∈ F <;>
    simp [namInd, Finset.mem_symmDiff, hmem, h1, h2]

end Layer

section Mean

variable {G : Type*} [Group G]

/-- A finitely supported function as an element of `ℓ¹(G)`. -/
noncomputable def namι : (G →₀ ℝ) →ₗ[ℝ] lp (fun _ : G => ℝ) 1 where
  toFun f := ⟨⇑f, (memℓp_zero (f.support.finite_toSet.subset
    (fun i hi => by simpa using hi))).of_exponent_ge zero_le⟩
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

omit [Group G] in
lemma nam_ι_apply (f : G →₀ ℝ) (x : G) : (namι f : G → ℝ) x = f x := rfl

omit [Group G] in
lemma nam_sum_le_norm (v : lp (fun _ : G => ℝ) 1) (T : Finset G) :
    ∑ x ∈ T, |(v : G → ℝ) x| ≤ ‖v‖ := by
  have := lp.sum_rpow_le_norm_rpow (p := 1) (by norm_num) v T
  simpa using this

lemma nam_step1 (hmean : HasInvariantMean G) (A : Finset G) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : G →₀ ℝ, (∀ x, 0 ≤ f x) ∧ (f.sum fun _ r => r) = 1 ∧
      ∀ a ∈ A, ‖namι (f - Finsupp.lmapDomain ℝ ℝ (fun x => a * x) f)‖ < δ := by
  classical
  obtain ⟨M, hpos, hone, hinv⟩ := hmean
  by_contra hcon
  push Not at hcon
  let E := A → lp (fun _ : G => ℝ) 1
  let L : (G →₀ ℝ) →ₗ[ℝ] E := LinearMap.pi fun a =>
    namι ∘ₗ (LinearMap.id - Finsupp.lmapDomain ℝ ℝ (fun x => (a : G) * x))
  let Φ : Set (G →₀ ℝ) := {f | (∀ x, 0 ≤ f x) ∧ (f.sum fun _ r => r) = 1}
  have hΦ : Convex ℝ Φ := by
    intro f hf g hg s t hs ht hst
    refine ⟨fun x => ?_, ?_⟩
    · have := hf.1 x; have := hg.1 x
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      positivity
    · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_smul_index' (fun _ => rfl), Finsupp.sum_smul_index' (fun _ => rfl)]
      simp only [smul_eq_mul]
      rw [← Finsupp.mul_sum, ← Finsupp.mul_sum, hf.2, hg.2]
      linarith
  have hC : Convex ℝ (L '' Φ) := hΦ.linear_image L
  have hdisj : Disjoint (Metric.ball (0 : E) δ) (L '' Φ) := by
    rw [Set.disjoint_left]
    rintro v hv ⟨f, hf, rfl⟩
    obtain ⟨a, ha, hle⟩ := hcon f hf.1 hf.2
    have h1 : ‖L f‖ < δ := by rwa [Metric.mem_ball, dist_zero_right] at hv
    have h2 := lt_of_le_of_lt (norm_le_pi_norm (L f) ⟨a, ha⟩) h1
    exact absurd h2 (not_lt.2 hle)
  obtain ⟨φ, u, hball, hΦu⟩ :=
    geometric_hahn_banach_open (convex_ball 0 δ) Metric.isOpen_ball hC hdisj
  have hu : 0 < u := by simpa using hball 0 (Metric.mem_ball_self hδ)
  let e1 : G → lp (fun _ : G => ℝ) 1 := fun y => lp.single 1 y (1 : ℝ)
  let b : A → G → ℝ := fun a y => φ (Pi.single a (e1 y) : E)
  have hb : ∀ a y, |b a y| ≤ ‖φ‖ := fun a y => by
    have := φ.le_opNorm (Pi.single a (e1 y) : E)
    have e : ‖(Pi.single a (e1 y) : E)‖ = 1 := by
      rw [Pi.norm_single, lp.norm_single (by norm_num)]; simp
    rw [e, mul_one] at this
    exact this
  let β : A → lp (fun _ : G => ℝ) ∞ := fun a =>
    ⟨b a, memℓp_infty_iff.2 ⟨‖φ‖, by rintro _ ⟨y, rfl⟩; simpa [Real.norm_eq_abs] using hb a y⟩⟩
  have key : ∀ y, u ≤ ∑ a : A, (b a y - b a (a * y)) := by
    intro y
    have hy : Finsupp.single y (1 : ℝ) ∈ Φ := by
      refine ⟨fun x => ?_, by simp⟩
      rw [Finsupp.single_apply]; split_ifs <;> norm_num
    have h := hΦu _ ⟨_, hy, rfl⟩
    have hL : L (Finsupp.single y 1) =
        ∑ a : A, (Pi.single a (e1 y - e1 ((a : G) * y)) : E) := by
      rw [Finset.univ_sum_single]
      funext a; ext x
      show (namι (Finsupp.single y 1 - Finsupp.lmapDomain ℝ ℝ (fun x => (a : G) * x)
        (Finsupp.single y 1)) : G → ℝ) x = _
      rw [nam_ι_apply]
      simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.coe_sub,
        Pi.sub_apply, Finsupp.single_apply, e1, lp.coeFn_sub, lp.single_apply, Pi.single_apply]
      simp only [eq_comm]
    rw [hL, map_sum] at h
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.single_sub, map_sub]
  let one : lp (fun _ : G => ℝ) ∞ :=
    ⟨fun _ => 1, memℓp_infty_iff.2 ⟨1, by rintro _ ⟨y, rfl⟩; simp⟩⟩
  let B := ∑ a : A, (β a - lshift (a : G)⁻¹ (β a))
  have hB : ∀ y, (B : G → ℝ) y = ∑ a : A, (b a y - b a (a * y)) := by
    intro y
    simp only [B, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_sub, Pi.sub_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [lshift, β]
  have h1 := hpos (B - u • one) (fun y => by
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hB]
    have : (one : G → ℝ) y = 1 := rfl
    rw [this]; linarith [key y])
  have h2 : M B = 0 := by
    simp only [B, map_sum, map_sub, hinv, sub_self, Finset.sum_const_zero]
  have h3 : M one = 1 := hone one (fun _ => rfl)
  rw [map_sub, map_smul, h2, h3] at h1
  simp at h1
  linarith

end Mean

/-- Namioka's argument (Garrido, proof of Theorem 3.6, p. 9): a group with a left-invariant
mean on `ℓ^∞(G)` satisfies the Følner condition. -/
theorem nam_satisfiesFoelnerCondition_of_hasInvariantMean (G : Type*) [Group G]
    (hmean : HasInvariantMean G) : SatisfiesFoelnerCondition G := by
  classical
  intro A hA ε hε
  set A' := hA.toFinset
  have hδ : 0 < ε / (A'.card + 1) := by positivity
  obtain ⟨f, hf0, hf1, hfA⟩ := nam_step1 hmean A' _ hδ
  set S0 := f.support
  set T := S0 ∪ (A' ×ˢ S0).image (fun p => p.1 * p.2)
  have hS0T : S0 ⊆ T := Finset.subset_union_left
  have hAT : ∀ a ∈ A', ∀ x ∈ S0, a * x ∈ T := fun a ha x hx =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨(a, x), Finset.mem_product.2 ⟨ha, hx⟩, rfl⟩)
  have hN : ∑ x ∈ T, f x = 1 := by
    rw [← hf1]
    exact (Finsupp.sum_of_support_subset f hS0T (fun _ r => r) (fun _ _ => rfl)).symm
  have hDa : ∀ a ∈ A', ∑ x ∈ T, |f x - f (a⁻¹ * x)| ≤ ε / (A'.card + 1) := by
    intro a ha
    refine le_trans ?_ (hfA a ha).le
    refine le_trans (le_of_eq ?_) (nam_sum_le_norm _ T)
    refine Finset.sum_congr rfl fun x _ => ?_
    have hmd : Finsupp.mapDomain (fun y => a * y) f x = f (a⁻¹ * x) := by
      simpa using Finsupp.mapDomain_apply (mul_right_injective a) f (a⁻¹ * x)
    rw [nam_ι_apply, Finsupp.coe_sub, Pi.sub_apply, Finsupp.lmapDomain_apply, hmd]
  have hD : ∑ a ∈ A', ∑ x ∈ T, |f x - f (a⁻¹ * x)| ≤ ε * ∑ x ∈ T, f x := by
    rw [hN, mul_one]
    calc _ ≤ ∑ _a ∈ A', ε / (A'.card + 1) := Finset.sum_le_sum hDa
      _ = A'.card * (ε / (A'.card + 1)) := by simp
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
  have hex : ∃ x, 0 < f x := by
    by_contra h
    push Not at h
    have : ∑ x ∈ T, f x = 0 := Finset.sum_eq_zero fun x _ => le_antisymm (h x) (hf0 x)
    linarith
  obtain ⟨F, hFne, hFS0, hF⟩ := nam_layer A' S0 T hS0T ε S0.card f hf0
    (fun x hx => Finsupp.mem_support_iff.2 hx.ne') (Finset.card_le_card (Finset.filter_subset _ _))
    hex hD
  refine ⟨↑F, F.finite_toSet, by simpa using hFne, fun a ha => ?_⟩
  have ha' : a ∈ A' := hA.mem_toFinset.2 ha
  rw [nam_card_symmDiff F T a (hFS0.trans hS0T) (fun x hx => hAT a ha' x (hFS0 hx)),
    Set.ncard_coe_finset, div_le_iff₀ (by exact_mod_cast hFne.card_pos)]
  exact le_trans (Finset.single_le_sum
    (f := fun a => ∑ x ∈ T, |namInd F x - namInd F (a⁻¹ * x)|)
    (fun a _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) ha') hF


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

/-- Theorem 3.6, the goal: `FOL` gives Følner ⇒ amenable, and `NAM` gives the converse from
the invariant mean that `MEAN` builds out of an amenability measure. -/
theorem satisfiesFoelnerCondition_iff_isAmenable' (G : Type*) [Group G] :
    SatisfiesFoelnerCondition G ↔ IsAmenable G :=
  ⟨fol_isAmenable_of_satisfiesFoelnerCondition, fun h =>
    nam_satisfiesFoelnerCondition_of_hasInvariantMean G (mean_hasInvariantMean_of_isAmenable h)⟩

end Garrido.Lib

open Garrido
open scoped ENNReal Pointwise

theorem solution (G : Type*) [Group G] :
    SatisfiesFoelnerCondition G ↔ IsAmenable G := by
  apply Garrido.Lib.satisfiesFoelnerCondition_iff_isAmenable' <;> assumption
