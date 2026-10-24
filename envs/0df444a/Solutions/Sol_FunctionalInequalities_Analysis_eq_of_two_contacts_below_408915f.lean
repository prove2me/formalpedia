-- Prove2me | solution 1 for FunctionalInequalities.Analysis.eq_of_two_contacts_below_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:15:50.132608+00:00
-- url     : https://prove2.me/submissions/7b56744d-3528-487c-99f2-f81ffdda1f8c

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_contactSet_eq_singleton_of_exposed_of_local_bounds_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_exposed_contact_of_lt_408915f

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F5SublevelContactLemma
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.supporting_affine_convex (c : ℝ) (p x : E) :
    ConvexOn ℝ univ (fun w => c + ⟪p, w - x⟫) := by
  refine (((innerSL ℝ p).toLinearMap.convexOn
    (convex_univ : Convex ℝ (univ : Set E))).add_const (c - ⟪p, x⟫)).congr ?_
  intro w _
  change ⟪p, w⟫ + (c - ⟪p, x⟫) = c + ⟪p, w - x⟫
  rw [inner_sub_right]
  ring
private lemma FunctionalInequalities.Analysis.subgradient_of_local_agreement {u v : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {U : Set E} (hU : IsOpen U) {x q : E} (hx : x ∈ U)
    (heq : ∀ ⦃w⦄, w ∈ U → v w = u w)
    (hq : ∀ w, v x + ⟪q, w - x⟫ ≤ v w) :
    ∀ w, u x + ⟪q, w - x⟫ ≤ u w := by
  have hloc : IsLocalMin (fun w => u w - ⟪q, w⟫) x := by
    filter_upwards [hU.eventually_mem hx] with w hw
    change u x - ⟪q, x⟫ ≤ u w - ⟪q, w⟫
    have hh := hq w
    rw [heq hx, heq hw, inner_sub_right] at hh
    linarith
  have hg := IsMinOn.of_isLocalMin_of_convex_univ hloc
    (hconv.sub ((innerSL ℝ q).toLinearMap.concaveOn convex_univ))
  intro w
  have hh := hg w
  change u x - ⟪q, x⟫ ≤ u w - ⟪q, w⟫ at hh
  rw [inner_sub_right]
  linarith
private lemma FunctionalInequalities.Analysis.subgradientImage_of_local_agreement {u v : E → ℝ}
    (hconv : ConvexOn ℝ univ u) (huv : ∀ x, u x ≤ v x)
    {U : Set E} (hU : IsOpen U) (heq : ∀ ⦃x⦄, x ∈ U → v x = u x)
    {G : Set E} (hGU : G ⊆ U) :
    subgradientImage v G = subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, hx, subgradient_of_local_agreement hconv hU (hGU hx) heq hq⟩
  · rintro ⟨x, hx, hq⟩
    refine ⟨x, hx, ?_⟩
    intro w
    rw [heq (hGU hx)]
    exact (hq w).trans (huv w)
section FiniteDimensional
variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution {u : E → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ x, u x₀ + ⟪p, x - x₀⟫ ≤ u x) {R : ℝ}
    (hK : IsCompact {x | u x ≤ R})
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {x | u x < R} →
      ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
        ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) ∧
        (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) ≤
          ENNReal.ofReal b * (volume : Measure E) G)
    (hxR : u x₀ < R) {y : E} (hyR : u y < R)
    (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by
  classical
  by_contra hne
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨r, hr, hrR⟩ := exists_between (max_lt hxR hyR)
  have hx_r : u x₀ < r := (le_max_left _ _).trans_lt hr
  have hy_r : u y < r := (le_max_right _ _).trans_lt hr
  have hKr : IsCompact {x | u x ≤ r} :=
    hK.of_isClosed_subset (isClosed_le hu continuous_const)
      (fun _ hx => hx.trans hrR.le)
  obtain ⟨z, θ₀, hz, hzr, hexp₀⟩ :=
    FunctionalInequalities.Analysis.exists_exposed_contact_of_lt_408915f hconv hp hx_r hKr
  have hθ₀ : θ₀ ≠ 0 := by
    intro hzero
    by_cases hxz : x₀ = z
    · have hyz : y ≠ z := by
        intro hyz
        exact hne (hyz.trans hxz.symm)
      have hh := hexp₀ y hy hy_r.le hyz
      simp [hzero] at hh
    · have hxcontact : u x₀ = u x₀ + ⟪p, x₀ - x₀⟫ := by simp
      have hh := hexp₀ x₀ hxcontact hx_r.le hxz
      simp [hzero] at hh
  have hn : 0 < ‖θ₀‖ := norm_pos_iff.mpr hθ₀
  let θ : E := ‖θ₀‖⁻¹ • θ₀
  have hθ : ‖θ‖ = 1 := by
    dsimp only [θ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ (ne_of_gt hn)]
  let ℓ : E → ℝ := fun x => u x₀ + ⟪p, x - x₀⟫
  have hℓ : ConvexOn ℝ univ ℓ := supporting_affine_convex (u x₀) p x₀
  have hℓcont : Continuous ℓ := by
    exact continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const))
  have hℓ0 : ℓ x₀ = u x₀ := by simp [ℓ]
  have hℓu (x : E) : ℓ x ≤ u x := hp x
  let v : E → ℝ := fun x => max (u x) (ℓ x + 2 * (ℓ x - r))
  have hvconv : ConvexOn ℝ univ v := by
    exact hconv.sup
      (hℓ.add (ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 2)
        (hℓ.sub (concaveOn_const r convex_univ))))
  have hvcont : Continuous v :=
    continuousOn_univ.mp (hvconv.continuousOn isOpen_univ)
  have huv (x : E) : u x ≤ v x := le_max_left _ _
  have hv0 : v x₀ = u x₀ := by
    change max (u x₀) (ℓ x₀ + 2 * (ℓ x₀ - r)) = u x₀
    rw [hℓ0]
    apply max_eq_left
    linarith
  have hvp : ∀ x, v x₀ + ⟪p, x - x₀⟫ ≤ v x := by
    intro x
    rw [hv0]
    exact (hp x).trans (huv x)
  have hcontact (x : E) :
      v x = v x₀ + ⟪p, x - x₀⟫ ↔ u x = ℓ x ∧ ℓ x ≤ r := by
    rw [hv0]
    change max (u x) (ℓ x + 2 * (ℓ x - r)) = ℓ x ↔
      u x = ℓ x ∧ ℓ x ≤ r
    constructor
    · intro hx
      have hfirst : u x ≤ ℓ x :=
        (le_max_left (u x) (ℓ x + 2 * (ℓ x - r))).trans_eq hx
      have hsecond : ℓ x + 2 * (ℓ x - r) ≤ ℓ x :=
        (le_max_right (u x) (ℓ x + 2 * (ℓ x - r))).trans_eq hx
      exact ⟨le_antisymm hfirst (hℓu x), by linarith⟩
    · rintro ⟨hx, hxr⟩
      rw [hx]
      apply max_eq_left
      linarith
  let C : Set E := {x | v x = v x₀ + ⟪p, x - x₀⟫}
  have hC : IsCompact C := by
    apply hKr.of_isClosed_subset
    · exact isClosed_eq hvcont
        (continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const)))
    · intro x hx
      obtain ⟨hxu, hxr⟩ := (hcontact x).mp hx
      exact hxu.trans_le hxr
  have hzC : z ∈ C := (hcontact z).mpr ⟨hz, hz.symm.trans_le hzr.le⟩
  have hxC : x₀ ∈ C := by
    apply (hcontact x₀).mpr
    exact ⟨hℓ0.symm, hℓ0.trans_le hx_r.le⟩
  have hyC : y ∈ C := (hcontact y).mpr ⟨hy, hy.symm.trans_le hy_r.le⟩
  have hexp : ∀ x ∈ C, x ≠ z → ⟪x - z, θ⟫ < 0 := by
    intro x hx hxz
    obtain ⟨hxu, hxr⟩ := (hcontact x).mp hx
    have hh := hexp₀ x hxu (hxu.trans_le hxr) hxz
    change ⟪x - z, ‖θ₀‖⁻¹ • θ₀⟫ < 0
    rw [inner_smul_right]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hn) hh
  let U : Set E := {x | ℓ x < r} ∩ {x | u x < R}
  have hU : IsOpen U :=
    (isOpen_lt hℓcont continuous_const).inter (isOpen_lt hu continuous_const)
  have hzU : z ∈ U := by
    exact ⟨hz.symm.trans_lt hzr, hzr.trans hrR⟩
  have hvU : ∀ ⦃x⦄, x ∈ U → v x = u x := by
    intro x hx
    change max (u x) (ℓ x + 2 * (ℓ x - r)) = u x
    apply max_eq_left
    have hlt : ℓ x < r := hx.1
    have hle := hℓu x
    linarith
  have hwidth : ∃ h : ℝ, 0 < h ∧ C ∩ {x | -h ≤ ⟪x - z, θ⟫} ⊆ U := by
    let D : Set E := C ∩ Uᶜ
    have hD : IsCompact D := hC.inter_right hU.isClosed_compl
    have hf : Continuous (fun x : E => ⟪x - z, θ⟫) :=
      (continuous_id.sub continuous_const).inner continuous_const
    by_cases hDne : D.Nonempty
    · obtain ⟨d, hd, hmax⟩ := hD.exists_isMaxOn hDne hf.continuousOn
      have hdz : d ≠ z := by
        intro hdZ
        exact hd.2 (hdZ.symm ▸ hzU)
      have hdneg := hexp d hd.1 hdz
      refine ⟨-⟪d - z, θ⟫ / 2, by linarith, ?_⟩
      intro x hx
      by_contra hxU
      have hxd : x ∈ D := ⟨hx.1, hxU⟩
      have hh : ⟪x - z, θ⟫ ≤ ⟪d - z, θ⟫ := hmax hxd
      have hcap := hx.2
      change -(-⟪d - z, θ⟫ / 2) ≤ ⟪x - z, θ⟫ at hcap
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      by_contra hxU
      exact hDne ⟨x, hx.1, hxU⟩
  obtain ⟨h, hh, hCU⟩ := hwidth
  have hvB : ∀ Q : Set E, IsCompact Q → Q ⊆ U →
      ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
        ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage v G) ∧
        (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage v G) ≤
          ENNReal.ofReal b * (volume : Measure E) G := by
    intro Q hQ hQU
    obtain ⟨a, b, ha, hab⟩ := hB Q hQ (fun x hx => (hQU hx).2)
    refine ⟨a, b, ha, ?_⟩
    intro G hG hGQ
    have hGU : G ⊆ U := fun _ hx => hQU (hGQ (subset_closure hx))
    rw [subgradientImage_of_local_agreement hconv huv hU hvU hGU]
    exact hab G hG hGQ
  have hsingle : C = {z} :=
    FunctionalInequalities.Analysis.contactSet_eq_singleton_of_exposed_of_local_bounds_408915f hvconv hvp hC hzC
      hθ hexp hh hU hCU hvB
  have hxz : x₀ = z := mem_singleton_iff.mp (hsingle ▸ hxC)
  have hyz : y = z := mem_singleton_iff.mp (hsingle ▸ hyC)
  exact hne (hyz.trans hxz.symm)
