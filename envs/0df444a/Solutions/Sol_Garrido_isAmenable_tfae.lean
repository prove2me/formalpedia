-- Prove2me | solution 1 for Garrido.isAmenable_tfae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T19:49:07.43343+00:00
-- url     : https://prove2.me/submissions/cf8cec11-2f2b-4845-8c7d-46f91e494c87

import Mathlib
import Theorems.Thm_Garrido_exists_invariant_measure_eq_one_iff_not_isParadoxical
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

/-- Finite additivity over the fibres of a map. -/
theorem mean_fam_fiber (hm : IsFinitelyAdditiveMeasure m) {α : Type*} [DecidableEq α]
    (π : X → α) (T : Finset α) :
    m (π ⁻¹' (T : Set α)) = ∑ a ∈ T, m (π ⁻¹' {a}) := by
  induction T using Finset.induction_on with
  | empty => simp [hm.1]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.coe_insert, Set.insert_eq, Set.preimage_union]
    apply hm.2
    exact Disjoint.preimage π (Set.disjoint_singleton_left.2 (by simpa using ha))

theorem mean_mono (hm : IsFinitelyAdditiveMeasure m) {s t : Set X} (h : s ⊆ t) : m s ≤ m t := by
  have : t = s ∪ (t \ s) := (Set.union_sdiff_cancel h).symm
  rw [this, hm.2 _ _ Set.disjoint_sdiff_right]
  exact le_self_add

theorem mean_ne_top (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : Set X) :
    m s ≠ ∞ :=
  ne_top_of_le_ne_top (by rw [h1]; exact ENNReal.one_ne_top) (mean_mono m hm (subset_univ s))

/-- The integral of a finitely valued function. -/
noncomputable def meanI (s : X → ℝ) : ℝ := ∑ᶠ v : ℝ, v * (m (s ⁻¹' {v})).toReal

variable {m}

theorem meanI_factor (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    {α : Type*} [DecidableEq α] (π : X → α) (T : Finset α) (hT : ∀ x, π x ∈ T) (ψ : α → ℝ) :
    meanI m (ψ ∘ π) = ∑ a ∈ T, ψ a * (m (π ⁻¹' {a})).toReal := by
  classical
  rw [meanI, finsum_eq_sum_of_support_subset _ (s := T.image ψ) ?_]
  · have e : ∀ v, (ψ ∘ π) ⁻¹' {v} = π ⁻¹' ((T.filter (fun a => ψ a = v) : Finset α) : Set α) := by
      intro v; ext x; simp [hT x]
    simp_rw [e, mean_fam_fiber m hm, ENNReal.toReal_sum (fun a _ => mean_ne_top m hm h1 _),
      Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (g := ψ) (t := T.image ψ)
      (fun a ha => Finset.mem_image_of_mem ψ ha)]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  · intro v hv
    rw [Function.mem_support] at hv
    by_contra h
    apply hv
    have : (ψ ∘ π) ⁻¹' {v} = ∅ := by
      ext x
      simp only [mem_preimage, Function.comp_apply, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      intro hx
      exact h (by simpa using ⟨π x, hT x, hx⟩)
    simp [this, hm.1]

theorem meanI_eq_sum (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    (s : X → ℝ) (T : Finset ℝ) (hT : ∀ x, s x ∈ T) :
    meanI m s = ∑ v ∈ T, v * (m (s ⁻¹' {v})).toReal :=
  meanI_factor hm h1 s T hT id

theorem mean_range_pair {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => (s x, t x)).Finite :=
  (hs.prod ht).subset (by rintro _ ⟨x, rfl⟩; exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩)

theorem mean_range_map {s : X → ℝ} (hs : (range s).Finite) (φ : ℝ → ℝ) :
    (range fun x => φ (s x)).Finite :=
  (hs.image φ).subset (by rintro _ ⟨x, rfl⟩; exact ⟨s x, ⟨x, rfl⟩, rfl⟩)

theorem mean_range_add {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => s x + t x).Finite :=
  ((mean_range_pair hs ht).image (fun p => p.1 + p.2)).subset
    (by rintro _ ⟨x, rfl⟩; exact ⟨(s x, t x), ⟨x, rfl⟩, rfl⟩)

theorem mean_range_const (c : ℝ) : (range fun _ : X => c).Finite :=
  (Set.finite_singleton c).subset Set.range_const_subset

theorem meanI_add (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) :
    meanI m (fun x => s x + t x) = meanI m s + meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hT : ∀ x, π x ∈ hs.toFinset ×ˢ ht.toFinset := fun x => by simp [π]
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  have e3 := meanI_factor hm h1 π _ hT (fun p => p.1 + p.2)
  simp only [Function.comp_def, π] at e1 e2 e3
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => add_mul _ _ _

theorem meanI_map (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s : X → ℝ}
    (hs : (range s).Finite) (c : ℝ) : meanI m (fun x => c * s x) = c * meanI m s := by
  classical
  have hT : ∀ x, s x ∈ hs.toFinset := fun x => by simp
  have e1 := meanI_factor hm h1 s _ hT (fun v => c * v)
  have e2 := meanI_eq_sum hm h1 s _ hT
  simp only [Function.comp_def] at e1
  rw [e1, e2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

theorem meanI_const (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (c : ℝ) :
    meanI m (fun _ : X => c) = c := by
  have e := meanI_factor hm h1 (fun _ : X => ()) Finset.univ (fun _ => Finset.mem_univ _)
    (fun _ => c)
  simp only [Function.comp_def] at e
  rw [e]
  simp [h1]

theorem meanI_mono (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) (hst : ∀ x, s x ≤ t x) :
    meanI m s ≤ meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hπ := mean_range_pair hs ht
  have hT : ∀ x, π x ∈ hπ.toFinset := fun x => (Set.Finite.mem_toFinset hπ).2 ⟨x, rfl⟩
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  simp only [Function.comp_def, π] at e1 e2
  rw [e1, e2]
  refine Finset.sum_le_sum fun a ha => ?_
  obtain ⟨x, rfl⟩ := (Set.Finite.mem_toFinset hπ).1 ha
  exact mul_le_mul_of_nonneg_right (hst x) ENNReal.toReal_nonneg

theorem meanI_smul_inv {G : Type*} [Group G] {m : Set G → ℝ≥0∞} (hinv : IsInvariant G m)
    (s : G → ℝ) (g : G) : meanI m (fun x => s (g⁻¹ * x)) = meanI m s := by
  unfold meanI
  congr 1
  funext v
  have : (fun x => s (g⁻¹ * x)) ⁻¹' {v} = g • (s ⁻¹' {v}) := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    rfl
  rw [this, hinv]

/-! ### The upper integral on `ℓ∞` -/

local notation "E" X => lp (fun _ : X => ℝ) ∞

variable (m) in
/-- Upper Darboux integral of a bounded function. -/
noncomputable def meanP (f : E X) : ℝ :=
  sInf {r | ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧ meanI m s = r}

theorem mean_abs_le (f : E X) (x : X) : |(f : X → ℝ) x| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero f x
  simpa [Real.norm_eq_abs] using this

theorem meanP_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {f : E X} {s : X → ℝ}
    (hs : (range s).Finite) (hfs : ∀ x, (f : X → ℝ) x ≤ s x) : meanP m f ≤ meanI m s := by
  refine csInf_le ⟨-‖f‖, ?_⟩ ⟨s, hs, hfs, rfl⟩
  rintro _ ⟨t, ht, hft, rfl⟩
  rw [← meanI_const hm h1 (-‖f‖)]
  exact meanI_mono hm h1 (mean_range_const _) ht
    (fun x => le_trans (neg_le_of_abs_le (mean_abs_le f x)) (hft x))

theorem le_meanP {f : E X} {r : ℝ}
    (h : ∀ s : X → ℝ, (range s).Finite → (∀ x, (f : X → ℝ) x ≤ s x) → r ≤ meanI m s) :
    r ≤ meanP m f := by
  refine le_csInf ⟨_, fun _ => ‖f‖, mean_range_const _,
    fun x => le_trans (le_abs_self _) (mean_abs_le f x), rfl⟩ ?_
  rintro _ ⟨s, hs, hfs, rfl⟩
  exact h s hs hfs

/-- Approximation from above by a finitely valued function, within `ε`. -/
theorem mean_approx (f : E X) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧
      ∀ x, s x ≤ (f : X → ℝ) x + ε := by
  refine ⟨fun x => ε * ⌈(f : X → ℝ) x / ε⌉, ?_, fun x => ?_, fun x => ?_⟩
  · refine ((Set.finite_Icc ⌈-‖f‖ / ε⌉ ⌈‖f‖ / ε⌉).image (fun k : ℤ => ε * k)).subset ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨_, ⟨Int.ceil_mono ?_, Int.ceil_mono ?_⟩, rfl⟩
    · exact div_le_div_of_nonneg_right (neg_le_of_abs_le (mean_abs_le f x)) hε.le
    · exact div_le_div_of_nonneg_right (le_trans (le_abs_self _) (mean_abs_le f x)) hε.le
  · have := Int.le_ceil ((f : X → ℝ) x / ε)
    calc (f : X → ℝ) x = ε * ((f : X → ℝ) x / ε) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hε.le
  · have := Int.ceil_lt_add_one ((f : X → ℝ) x / ε)
    calc ε * (⌈(f : X → ℝ) x / ε⌉ : ℝ) ≤ ε * ((f : X → ℝ) x / ε + 1) :=
          mul_le_mul_of_nonneg_left this.le hε.le
      _ = (f : X → ℝ) x + ε := by field_simp

/-- A finitely valued function as an element of `ℓ∞`. -/
noncomputable def meanOfFin (s : X → ℝ) (hs : (range s).Finite) : E X :=
  ⟨s, memℓp_infty_iff.2 (by
    have : (range fun i => ‖s i‖) = (fun v => ‖v‖) '' range s := by
      rw [← Set.range_comp]; rfl
    rw [this]
    exact (hs.image _).bddAbove)⟩

@[simp] theorem meanOfFin_apply (s : X → ℝ) (hs : (range s).Finite) (x : X) :
    (meanOfFin s hs : X → ℝ) x = s x := rfl

theorem meanP_ofFin (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : X → ℝ)
    (hs : (range s).Finite) : meanP m (meanOfFin s hs) = meanI m s :=
  le_antisymm (meanP_le hm h1 hs fun _ => le_rfl)
    (le_meanP fun t ht hst => meanI_mono (t := t) hm h1 hs ht hst)

theorem meanP_smul_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) ≤ c * meanP m f := by
  have : meanP m (c • f) / c ≤ meanP m f := by
    refine le_meanP fun s hs hfs => ?_
    rw [div_le_iff₀ hc]
    calc meanP m (c • f) ≤ meanI m (fun x => c * s x) :=
          meanP_le hm h1 (mean_range_map hs _) (fun x => by
            simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
            exact mul_le_mul_of_nonneg_left (hfs x) hc.le)
      _ = meanI m s * c := by rw [meanI_map hm h1 hs, mul_comm]
  rwa [div_le_iff₀ hc, mul_comm] at this

theorem meanP_smul (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) = c * meanP m f := by
  refine le_antisymm (meanP_smul_le hm h1 hc f) ?_
  have := meanP_smul_le hm h1 (inv_pos.2 hc) (c • f)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  calc c * meanP m f ≤ c * (c⁻¹ * meanP m (c • f)) := mul_le_mul_of_nonneg_left this hc.le
    _ = _ := by field_simp

theorem meanP_add_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f g : E X) :
    meanP m (f + g) ≤ meanP m f + meanP m g := by
  have h2 : meanP m (f + g) - meanP m f ≤ meanP m g := by
    refine le_meanP fun t ht hgt => ?_
    have : meanP m (f + g) - meanI m t ≤ meanP m f := by
      refine le_meanP fun s hs hfs => ?_
      have := meanP_le hm h1 (f := f + g) (mean_range_add hs ht)
        (fun x => by simp only [lp.coeFn_add, Pi.add_apply]; exact add_le_add (hfs x) (hgt x))
      rw [meanI_add hm h1 hs ht] at this
      linarith
    linarith
  linarith

theorem meanP_zero (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    meanP m (0 : E X) = 0 := by
  refine le_antisymm ?_ ?_
  · calc meanP m (0 : E X) ≤ meanI m (fun _ => 0) :=
          meanP_le hm h1 (mean_range_const _) (fun x => by simp)
      _ = 0 := meanI_const hm h1 0
  · refine le_meanP fun s hs hfs => ?_
    rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
    exact meanI_mono hm h1 (mean_range_const _) hs (fun x => by simpa using hfs x)

/-- The upper integral is linear (Hahn–Banach plus uniform approximation). -/
theorem mean_exists_linear (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    ∃ L : (E X) →ₗ[ℝ] ℝ, ∀ f, L f = meanP m f := by
  obtain ⟨L, -, hL⟩ := exists_extension_of_le_sublinear
    ({ domain := ⊥, toFun := 0 } : (E X) →ₗ.[ℝ] ℝ) (meanP m)
    (fun c hc f => meanP_smul hm h1 hc f) (meanP_add_le hm h1)
    (fun x => by
      have hx : (x : E X) = 0 := (Submodule.mem_bot ℝ).1 x.2
      simp [hx, meanP_zero hm h1])
  refine ⟨L, fun f => le_antisymm (hL f) ?_⟩
  -- `L` agrees with `meanI` on finitely valued functions.
  have hLs : ∀ s hs, L (meanOfFin s hs) = meanI m s := by
    intro s hs
    refine le_antisymm ((hL _).trans (meanP_ofFin hm h1 s hs).le) ?_
    have hns := mean_range_map hs (fun v => -1 * v)
    have e : -(meanOfFin s hs) = meanOfFin (fun x => -1 * s x) hns := by
      ext x; simp
    have := hL (-(meanOfFin s hs))
    rw [map_neg, e, meanP_ofFin hm h1 _ hns, meanI_map hm h1 hs] at this
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨s, hs, hfs, hsf⟩ := mean_approx f hε
  have hs' := mean_range_map hs (fun v => v + -ε)
  have h3 : meanI m (fun x => s x + -ε) = meanI m s - ε := by
    rw [meanI_add hm h1 hs (mean_range_const _), meanI_const hm h1]; ring
  have h4 : L (meanOfFin _ hs') ≤ L f := by
    have := hL (meanOfFin _ hs' - f)
    have h0 : meanP m (meanOfFin _ hs' - f) ≤ 0 := by
      calc meanP m (meanOfFin _ hs' - f) ≤ meanI m (fun _ => 0) :=
            meanP_le hm h1 (mean_range_const _) (fun x => by
              simp only [lp.coeFn_sub, Pi.sub_apply, meanOfFin_apply]; linarith [hsf x])
        _ = 0 := meanI_const hm h1 0
    rw [map_sub] at this
    linarith
  rw [hLs] at h4
  calc meanP m f ≤ meanI m s := meanP_le hm h1 hs hfs
    _ ≤ L f + ε := by linarith

/-- **The integral** `∫ · dm` of a bounded function against a finitely additive probability
measure. -/
noncomputable def mean_integral (m : Set X → ℝ≥0∞) (hm : IsFinitelyAdditiveMeasure m)
    (h1 : m univ = 1) : (E X) →ₗ[ℝ] ℝ where
  toFun := meanP m
  map_add' f g := by
    obtain ⟨L, hL⟩ := mean_exists_linear hm h1
    rw [← hL, ← hL, ← hL, map_add]
  map_smul' c f := by
    obtain ⟨L, hL⟩ := mean_exists_linear hm h1
    rw [← hL, ← hL, map_smul]; rfl

theorem mean_integral_apply (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X) :
    mean_integral m hm h1 f = meanP m f := rfl

theorem mean_integral_nonneg (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (hf : ∀ x, 0 ≤ (f : X → ℝ) x) : 0 ≤ mean_integral m hm h1 f := by
  refine le_meanP fun s hs hfs => ?_
  rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
  exact meanI_mono hm h1 (mean_range_const _) hs (fun x => (hf x).trans (hfs x))

theorem mean_integral_eq_const (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (c : ℝ) (hf : ∀ x, (f : X → ℝ) x = c) : mean_integral m hm h1 f = c := by
  have : f = meanOfFin (fun _ => c) (mean_range_const c) := by ext x; simp [hf]
  rw [this, mean_integral_apply, meanP_ofFin hm h1, meanI_const hm h1]

theorem mean_integral_one (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (hf : ∀ x, (f : X → ℝ) x = 1) : mean_integral m hm h1 f = 1 :=
  mean_integral_eq_const hm h1 f 1 hf

theorem mean_range_indicator (A : Set X) : (range (A.indicator (1 : X → ℝ))).Finite :=
  (Set.toFinite ({0, 1} : Set ℝ)).subset (by
    rintro _ ⟨x, rfl⟩; by_cases h : x ∈ A <;> simp [h])

/-- The indicator function of `A` as an element of `ℓ∞`. -/
noncomputable def mean_ind (A : Set X) : E X := meanOfFin _ (mean_range_indicator A)

@[simp] theorem mean_ind_apply (A : Set X) (x : X) :
    (mean_ind A : X → ℝ) x = A.indicator 1 x := rfl

theorem mean_integral_lshift {G : Type*} [Group G] {m : Set G → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (hinv : IsInvariant G m) (g : G)
    (f : E G) : mean_integral m hm h1 (lshift g f) = mean_integral m hm h1 f := by
  have key : ∀ (g : G) (f : E G), meanP m (lshift g f) ≤ meanP m f := by
    intro g f
    refine le_meanP fun s hs hfs => ?_
    rw [← meanI_smul_inv hinv s g]
    exact meanP_le hm h1 ((hs.image id).subset (by rintro _ ⟨x, rfl⟩; exact ⟨_, ⟨_, rfl⟩, rfl⟩))
      (fun x => hfs _)
  refine le_antisymm (key g f) ?_
  have e : f = lshift g⁻¹ (lshift g f) := by
    ext x; show (f : G → ℝ) x = (f : G → ℝ) (g⁻¹ * (g⁻¹⁻¹ * x)); simp
  calc mean_integral m hm h1 f = meanP m (lshift g⁻¹ (lshift g f)) := by
        rw [mean_integral_apply, ← e]
    _ ≤ _ := key _ _

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

/-- **(2) ⇒ (1) of Theorem 1.15**: a left-invariant mean gives an invariant finitely additive
probability measure, `m A = ofReal (M 1_A)`. -/
theorem mean_isAmenable_of_hasInvariantMean {G : Type*} [Group G] (h : HasInvariantMean G) :
    IsAmenable G := by
  obtain ⟨M, hM⟩ := h
  refine mean_isAmenable_of_mean (MonoidHom.id G) M hM mean_ind (fun A q => ?_) (fun q => ?_)
    (fun q => ?_) (fun A B hAB q => ?_) (fun g A q => ?_)
  · simp only [mean_ind_apply]; by_cases h : q ∈ A <;> simp [h]
  · simp
  · simp
  · simp only [mean_ind_apply]; exact congrFun (Set.indicator_union_of_disjoint hAB (1 : G → ℝ)) q
  · simp only [mean_ind_apply, MonoidHom.id_apply]
    by_cases h : g⁻¹ * q ∈ A
    · have : q ∈ g • A := Set.mem_smul_set_iff_inv_smul_mem.2 h
      simp [h, this]
    · have : q ∉ g • A := fun h' => h (Set.mem_smul_set_iff_inv_smul_mem.1 h')
      simp [h, this]

/-- **(1) ⇒ (2) of Theorem 1.15**: integrating against an invariant finitely additive
probability measure is a left-invariant mean. -/
theorem mean_hasInvariantMean_of_isAmenable {G : Type*} [Group G] (h : IsAmenable G) :
    HasInvariantMean G := by
  obtain ⟨m, hm, h1, hinv⟩ := h
  exact ⟨mean_integral m hm h1, fun f hf => mean_integral_nonneg hm h1 f hf,
    fun f hf => mean_integral_one hm h1 f hf, fun g f => mean_integral_lshift hm h1 hinv g f⟩

theorem mean_isAmenable_iff_hasInvariantMean (G : Type*) [Group G] :
    IsAmenable G ↔ HasInvariantMean G :=
  ⟨mean_hasInvariantMean_of_isAmenable, mean_isAmenable_of_hasInvariantMean⟩

end MeanToMeasure

/-! ### Theorem 1.15 -/

/-- Theorem 1.15, reduced to Tarski's theorem (Theorem 1.11) for `G` acting on itself, `E = univ`. -/
theorem mean_isAmenable_tfae_of_tarski (G : Type*) [Group G]
    (htarski : (∃ m : Set G → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
        IsInvariant G m) ↔ ¬ IsParadoxical G (Set.univ : Set G)) :
    [IsAmenable G,
      HasInvariantMean G,
      ¬ IsParadoxical G (Set.univ : Set G)].TFAE := by
  tfae_have 1 ↔ 2 := mean_isAmenable_iff_hasInvariantMean G
  tfae_have 1 ↔ 3 := htarski
  tfae_finish

/-- The same, with Theorem 1.11 taken verbatim as the hypothesis (as the coordinator will
compose it). -/
theorem mean_isAmenable_tfae_of_tarski' (G : Type u) [Group G]
    (h1_11 : ∀ {G X : Type u} [Group G] [MulAction G X] (E : Set X) (_hE : E.Nonempty),
      (∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m E = 1 ∧
        IsInvariant G m) ↔ ¬ IsParadoxical G E) :
    [IsAmenable G,
      HasInvariantMean G,
      ¬ IsParadoxical G (Set.univ : Set G)].TFAE :=
  mean_isAmenable_tfae_of_tarski G (h1_11 (G := G) (X := G) Set.univ Set.univ_nonempty)


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

/-- Theorem 1.15: `MEAN` reduced it to Tarski's Theorem 1.11, imported as published. -/
theorem isAmenable_tfae' (G : Type*) [Group G] :
    [IsAmenable G,
      HasInvariantMean G,
      ¬ IsParadoxical G (Set.univ : Set G)].TFAE :=
  mean_isAmenable_tfae_of_tarski' G Garrido.exists_invariant_measure_eq_one_iff_not_isParadoxical

end Garrido.Lib

open Garrido
open scoped ENNReal Pointwise

theorem solution (G : Type*) [Group G] :
    [IsAmenable G,
      HasInvariantMean G,
      ¬ IsParadoxical G (Set.univ : Set G)].TFAE := by
  exact Garrido.Lib.isAmenable_tfae' G
