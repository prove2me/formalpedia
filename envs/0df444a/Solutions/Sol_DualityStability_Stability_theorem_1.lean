-- Prove2me | solution 1 for DualityStability.Stability.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T06:25:46.131127+00:00
-- url     : https://prove2.me/submissions/dda4770f-88fb-4068-8c1a-cb5f7fe3377e

import Mathlib
import Definitions.Def_DualityStability_Stability_ConvexFunction
import Definitions.Def_DualityStability_Stability_perturbInf
import Definitions.Def_DualityStability_Stability_StablySet
open Set Filter Topology DualityStability.Stability

namespace StabilityProof
open Set Filter Topology DualityStability.Stability

theorem convex_bound_weights {F : Type*} [AddCommGroup F] [Module ℝ F]
    {h : F → EReal} (hc : ConvexFn h) {x y : F} {a b s t : ℝ}
    (hx : h x ≤ (a : EReal)) (hy : h y ≤ (b : EReal))
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    h (s • x + t • y) ≤ ((s * a + t * b : ℝ) : EReal) := by
  exact hc (x := (x,a)) hx (y := (y,b)) hy hs ht hst

theorem convex_bound {F : Type*} [AddCommGroup F] [Module ℝ F]
    {h : F → EReal} (hc : ConvexFn h) {x y : F} {a b t : ℝ}
    (hx : h x ≤ (a : EReal)) (hy : h y ≤ (b : EReal))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    h (t • x + (1-t) • y) ≤ ((t*a+(1-t)*b : ℝ) : EReal) := by
  exact convex_bound_weights hc hx hy ht0 (sub_nonneg.mpr ht1) (by ring)

theorem finite_cost_parts {a b : EReal} {r : ℝ}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (h : a+b < (r : EReal)) :
    a ≠ ⊤ ∧ b ≠ ⊤ := by
  exact (EReal.add_ne_top_iff_ne_top₂ ha hb).mp (ne_top_of_lt (h.trans (EReal.coe_lt_top r)))

end StabilityProof

namespace StabilityProof
open Set Filter Topology DualityStability.Stability

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
theorem perturb_convex (A : E →L[ℝ] F) (f : E → EReal) (g : F → EReal)
    (hf : ProperConvexFn f) (hg : ProperConcaveFn g) : ConvexFn (perturbInf f g A) := by
  apply convex_iff_add_mem.mpr
  rintro ⟨z,a⟩ ha ⟨w,b⟩ hb s t hs ht hst
  change perturbInf f g A (s • z + t • w) ≤ ((s*a+t*b : ℝ) : EReal)
  change perturbInf f g A z ≤ (a : EReal) at ha
  change perturbInf f g A w ≤ (b : EReal) at hb
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r hr
  have hrr : s*a+t*b < r := by exact_mod_cast hr
  let δ : ℝ := (r-(s*a+t*b))/2
  have hd : 0 < δ := by dsimp [δ]; linarith
  have hz : perturbInf f g A z < ((a+δ : ℝ) : EReal) :=
    ha.trans_lt (by exact_mod_cast (show a < a+δ by linarith))
  have hw : perturbInf f g A w < ((b+δ : ℝ) : EReal) :=
    hb.trans_lt (by exact_mod_cast (show b < b+δ by linarith))
  obtain ⟨x,hx⟩ := iInf_lt_iff.mp hz
  obtain ⟨y,hy⟩ := iInf_lt_iff.mp hw
  have hfxb : f x ≠ ⊥ := ne_of_gt (hf.2.1 x)
  have hfyb : f y ≠ ⊥ := ne_of_gt (hf.2.1 y)
  have hgxb : -g (A x-z) ≠ ⊥ := by simpa using ne_of_lt (hg.2.1 (A x-z))
  have hgyb : -g (A y-w) ≠ ⊥ := by simpa using ne_of_lt (hg.2.1 (A y-w))
  have hxp := finite_cost_parts hfxb hgxb (by simpa only [sub_eq_add_neg] using hx)
  have hyp := finite_cost_parts hfyb hgyb (by simpa only [sub_eq_add_neg] using hy)
  let fx := (f x).toReal
  let fy := (f y).toReal
  let gx := (-g (A x-z)).toReal
  let gy := (-g (A y-w)).toReal
  have hfx : (fx : EReal) = f x := EReal.coe_toReal hxp.1 hfxb
  have hfy : (fy : EReal) = f y := EReal.coe_toReal hyp.1 hfyb
  have hgx : (gx : EReal) = -g (A x-z) := EReal.coe_toReal hxp.2 hgxb
  have hgy : (gy : EReal) = -g (A y-w) := EReal.coe_toReal hyp.2 hgyb
  have hx' : fx+gx < a+δ := by
    have hh := hx
    rw [sub_eq_add_neg, ← hfx, ← hgx] at hh
    exact_mod_cast hh
  have hy' : fy+gy < b+δ := by
    have hh := hy
    rw [sub_eq_add_neg, ← hfy, ← hgy] at hh
    exact_mod_cast hh
  have hfc := convex_bound_weights hf.1 hfx.ge hfy.ge hs ht hst
  have hgc := convex_bound_weights hg.1 hgx.ge hgy.ge hs ht hst
  have harg : A (s • x+t • y)-(s • z+t • w) = s • (A x-z)+t • (A y-w) := by
    simp only [map_add, map_smul, smul_sub]
    abel
  calc
    perturbInf f g A (s • z+t • w)
        ≤ f (s • x+t • y)-g (A (s • x+t • y)-(s • z+t • w)) := iInf_le _ _
    _ = f (s • x+t • y)+(-g (s • (A x-z)+t • (A y-w))) := by rw [harg, sub_eq_add_neg]
    _ ≤ ((s*fx+t*fy : ℝ) : EReal)+((s*gx+t*gy : ℝ) : EReal) := add_le_add hfc hgc
    _ ≤ (r : EReal) := by
      norm_cast
      have hh := add_le_add (mul_le_mul_of_nonneg_left hx'.le hs)
        (mul_le_mul_of_nonneg_left hy'.le ht)
      have he : s*(a+δ)+t*(b+δ) = s*a+t*b+δ := by
        calc
          _ = s*a+t*b+(s+t)*δ := by ring
          _ = s*a+t*b+δ := by rw [hst, one_mul]
      rw [he] at hh
      dsimp [δ] at hh
      nlinarith

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [ContinuousSMul ℝ F] in
theorem perturb_upper (A : E →L[ℝ] F) (f : E → EReal) (g : F → EReal)
    (hx : ∃ x : E, f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ g (A x) ≠ ⊥ ∧ g (A x) ≠ ⊤ ∧ ContinuousAt g (A x)) :
    ∃ B : ℝ, ∀ᶠ z in nhds (0 : F), perturbInf f g A z ≤ (B : EReal) := by
  obtain ⟨x,hfb,hft,hgb,hgt,hc⟩ := hx
  let a := (f x).toReal
  let b := (g (A x)).toReal
  have ha : (a : EReal) = f x := EReal.coe_toReal hft hfb
  have hb : (b : EReal) = g (A x) := EReal.coe_toReal hgt hgb
  have hcont : Tendsto (fun z : F => g (A x-z)) (nhds 0) (nhds (g (A x))) := by
    have hm : Continuous (fun z : F => A x - z) := by fun_prop
    exact hc.tendsto.comp (by simpa only [sub_zero] using hm.tendsto (0 : F))
  have hb' : ((b-1 : ℝ) : EReal) < g (A x) := by rw [← hb]; norm_cast; linarith
  have he : ∀ᶠ z : F in nhds 0, ((b-1 : ℝ) : EReal) < g (A x-z) :=
    hcont.eventually (Ioi_mem_nhds hb')
  refine ⟨a-(b-1), ?_⟩
  filter_upwards [he] with z hz
  calc
    perturbInf f g A z ≤ f x-g (A x-z) := iInf_le _ _
    _ ≤ (a : EReal)-((b-1 : ℝ) : EReal) := EReal.sub_le_sub ha.ge hz.le
    _ = ((a-(b-1) : ℝ) : EReal) := by norm_cast

end StabilityProof

namespace StabilityProof
open Set Filter DualityStability.Stability
open scoped Topology

lemma real_lower_of_upper {v : EReal} {a : ℝ}
    (h : ∀ r : ℝ, v ≤ (r : EReal) → a ≤ r) : (a : EReal) ≤ v := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r hr
  exact EReal.coe_le_coe (h r hr.le)

section Topology
variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

omit [Module ℝ F] [ContinuousSMul ℝ F] in
lemma symmetric_upper (h : F → EReal)
    (hb : ∃ B : ℝ, ∀ᶠ z in nhds (0 : F), h z ≤ (B : EReal)) :
    ∃ (B : ℝ) (V : Set F), IsOpen V ∧ (0 : F) ∈ V ∧
      (∀ z ∈ V, -z ∈ V) ∧ ∀ z ∈ V, h z ≤ (B : EReal) := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨O, hO, ho, hz⟩ := eventually_nhds_iff.mp hB
  refine ⟨B, O ∩ (fun z : F => -z) ⁻¹' O, ho.inter (ho.preimage continuous_neg),
    ⟨hz, by simpa using hz⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨hz.2, by simpa using hz.1⟩
  · intro z hz
    exact hO z hz.1

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma midpoint_lower (h : F → EReal) (hc : ConvexFn h) {a B : ℝ}
    (h0 : h 0 = (a : EReal)) {z : F} (hz : h (-z) ≤ (B : EReal)) :
    ((2 * a - B : ℝ) : EReal) ≤ h z := by
  apply real_lower_of_upper
  intro r hr
  have hv := convex_bound hc hr hz (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have he : (1 / 2 : ℝ) • z + (1 - 1 / 2 : ℝ) • (-z) = 0 := by module
  rw [he, h0, EReal.coe_le_coe_iff] at hv
  linarith

lemma finite_of_bounds {v : EReal} {a B : ℝ}
    (ha : (a : EReal) ≤ v) (hb : v ≤ (B : EReal)) :
    (v.toReal : EReal) = v :=
  EReal.coe_toReal (hb.trans_lt (EReal.coe_lt_top B)).ne
    ((EReal.bot_lt_coe a).trans_le ha).ne'

lemma convex_continuous_neighborhood (h : F → EReal) (hc : ConvexFn h)
    (hb : ∃ B : ℝ, ∀ᶠ z in nhds (0 : F), h z ≤ (B : EReal)) :
    ∃ U ∈ nhds (0 : F), ContinuousOn h U := by
  obtain ⟨B, V, hVo, hV0, hVneg, hVB⟩ := symmetric_upper h hb
  by_cases h0bot : h 0 = ⊥
  · let U : Set F := (fun z : F => (2 : ℝ) • z) ⁻¹' V
    have hUo : IsOpen U := hVo.preimage (by fun_prop)
    have hU0 : (0 : F) ∈ U := by simpa [U] using hV0
    have hbot : ∀ z ∈ U, h z = ⊥ := by
      intro z hz
      apply (EReal.eq_bot_iff_forall_lt _).mpr
      intro r
      have hfirst : h 0 ≤ ((2 * (r - 1) - B : ℝ) : EReal) := by
        rw [h0bot]
        exact bot_le
      have hv := convex_bound hc hfirst (hVB _ hz) (t := (1 / 2 : ℝ))
        (by norm_num) (by norm_num)
      have he : (1 / 2 : ℝ) • (0 : F) + (1 - 1 / 2 : ℝ) • ((2 : ℝ) • z) = z := by
        simp only [smul_zero, zero_add, smul_smul]
        norm_num
      rw [he] at hv
      have hr : (1 / 2 : ℝ) * (2 * (r - 1) - B) + (1 - 1 / 2 : ℝ) * B = r - 1 := by ring
      rw [hr] at hv
      exact hv.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
    refine ⟨U, hUo.mem_nhds hU0, ?_⟩
    exact continuousOn_const.congr (fun z hz => hbot z hz)
  · have h0top : h 0 ≠ ⊤ := (hVB 0 hV0 |>.trans_lt (EReal.coe_lt_top B)).ne
    let a := (h 0).toReal
    have h0 : h 0 = (a : EReal) := (EReal.coe_toReal h0top h0bot).symm
    have hfin : ∀ z ∈ V, ((h z).toReal : EReal) = h z := by
      intro z hz
      exact finite_of_bounds (midpoint_lower h hc h0 (hVB _ (hVneg z hz))) (hVB z hz)
    refine ⟨V, hVo.mem_nhds hV0, ?_⟩
    intro x hx
    have hcont : ContinuousAt (fun z => (h z).toReal) x := by
      apply Metric.continuousAt_iff'.mpr
      intro ε hε
      let b := (h x).toReal
      have hbB : b ≤ B := EReal.coe_le_coe_iff.mp ((hfin x hx).trans_le (hVB x hx))
      let D := 2 * (B - b + ε + 1)
      have hD : 0 < D := by dsimp [D]; linarith
      let t := ε / D
      have ht : 0 < t := div_pos hε hD
      have ht1 : t < 1 := (div_lt_one hD).mpr (by dsimp [D]; linarith)
      have herr : t * (B - b) < ε := by
        dsimp [t]
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hD).mpr
        dsimp [D]
        nlinarith
      have hu : ContinuousAt (fun y : F => x + t⁻¹ • (y - x)) x := by fun_prop
      have hv : ContinuousAt (fun y : F => x - t⁻¹ • (y - x)) x := by fun_prop
      have hue : ∀ᶠ y in nhds x, x + t⁻¹ • (y - x) ∈ V :=
        hu.tendsto.eventually (by simpa using hVo.mem_nhds hx)
      have hve : ∀ᶠ y in nhds x, x - t⁻¹ • (y - x) ∈ V :=
        hv.tendsto.eventually (by simpa using hVo.mem_nhds hx)
      filter_upwards [hVo.mem_nhds hx, hue, hve] with y hy huy hvy
      have hupper := convex_bound hc (hfin x hx).symm.le (hVB _ huy)
        (t := 1 - t) (by linarith) (by linarith)
      have hupper_eq : (1 - t) • x + (1 - (1 - t)) • (x + t⁻¹ • (y - x)) = y := by
        have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
        calc
          _ = x + (t * t⁻¹) • (y - x) := by module
          _ = y := by rw [hcancel]; simp
      rw [hupper_eq, ← hfin y hy, EReal.coe_le_coe_iff] at hupper
      have hsum : 0 < 1 + t := by linarith
      have halpha : 0 ≤ 1 / (1 + t) := by positivity
      have halpha1 : 1 / (1 + t) ≤ 1 := (div_le_one hsum).mpr (by linarith)
      have hlower := convex_bound hc (hfin y hy).symm.le (hVB _ hvy) halpha halpha1
      have hcoef1 : 1 / (1 + t) - (1 - 1 / (1 + t)) * t⁻¹ = 0 := by
        field_simp [ht.ne', hsum.ne']
        ring
      have hcoef2 : (1 - 1 / (1 + t)) + (1 - 1 / (1 + t)) * t⁻¹ = 1 := by
        field_simp [ht.ne', hsum.ne']
        ring
      have hlower_eq : (1 / (1 + t)) • y + (1 - 1 / (1 + t)) •
          (x - t⁻¹ • (y - x)) = x := by
        calc
          _ = (1 / (1 + t) - (1 - 1 / (1 + t)) * t⁻¹) • y +
              ((1 - 1 / (1 + t)) + (1 - 1 / (1 + t)) * t⁻¹) • x := by module
          _ = x := by rw [hcoef1, hcoef2]; simp
      rw [hlower_eq, ← hfin x hx, EReal.coe_le_coe_iff] at hlower
      have hcoef3 : 1 - 1 / (1 + t) = t / (1 + t) := by field_simp; ring
      rw [hcoef3] at hlower
      have hlower' : b * (1 + t) ≤ (h y).toReal + t * B := by
        apply (le_div_iff₀ hsum).mp
        simpa only [add_div, mul_div_assoc, one_mul, div_mul_eq_mul_div] using hlower
      rw [Real.dist_eq, abs_lt]
      dsimp [b] at herr ⊢
      constructor <;> nlinarith
    have he : (fun z => ((h z).toReal : EReal)) =ᶠ[nhds x] h := by
      filter_upwards [hVo.mem_nhds hx] with z hz
      exact hfin z hz
    have hcoe : ContinuousAt (fun z => ((h z).toReal : EReal)) x :=
      continuous_coe_real_ereal.continuousAt.comp hcont
    exact (hcoe.congr_of_eventuallyEq he.symm).continuousWithinAt

end Topology
end StabilityProof

namespace StabilityProof
open Set Filter DualityStability.Stability
open scoped Topology

section Algebra
variable {F : Type*} [AddCommGroup F] [Module ℝ F]

lemma positive_ray_lower (h : F → EReal) (hc : ConvexFn h) {a B : ℝ}
    (h0 : h 0 = (a : EReal)) {z : F} (hz : h (-z) ≤ (B : EReal))
    {ε : ℝ} (hε : 0 < ε) : ((a + ε * (a - B) : ℝ) : EReal) ≤ h (ε • z) := by
  apply real_lower_of_upper
  intro r hr
  have hd : 0 < 1 + ε := by linarith
  have hv := convex_bound hc hr hz (t := 1 / (1 + ε)) (by positivity)
    ((div_le_one hd).mpr (by linarith))
  have hcoef : 1 - 1 / (1 + ε) = ε / (1 + ε) := by field_simp; ring
  rw [hcoef] at hv
  have he : (1 / (1 + ε)) • (ε • z) + (ε / (1 + ε)) • (-z) = 0 := by
    simp only [smul_smul, smul_neg, div_mul_eq_mul_div, one_mul]
    exact add_neg_cancel _
  rw [he, h0, EReal.coe_le_coe_iff] at hv
  have hv' : a * (1 + ε) ≤ r + ε * B := by
    apply (le_div_iff₀ hd).mp
    simpa only [add_div, mul_div_assoc, one_mul, div_mul_eq_mul_div] using hv
  nlinarith

lemma positive_quotient_lower (h : F → EReal) (hc : ConvexFn h) {a B : ℝ}
    (h0 : h 0 = (a : EReal)) {z : F} (hz : h (-z) ≤ (B : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ((a - B : ℝ) : EReal) ≤ ((ε⁻¹ : ℝ) : EReal) * (h (ε • z) - h 0) := by
  have hl := positive_ray_lower h hc h0 hz hε
  by_cases ht : h (ε • z) = ⊤
  · rw [ht, h0, EReal.top_sub_coe, EReal.coe_mul_top_of_pos (inv_pos.mpr hε)]
    exact le_top
  · have hb : h (ε • z) ≠ ⊥ := ((EReal.bot_lt_coe (a + ε * (a - B))).trans_le hl).ne'
    have hf := EReal.coe_toReal ht hb
    rw [← hf, EReal.coe_le_coe_iff] at hl
    rw [← hf, h0, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hε).mpr
    nlinarith

end Algebra

section Topology
variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma directional_lower (h : F → EReal) (hc : ConvexFn h) {a B : ℝ}
    (h0 : h 0 = (a : EReal)) {z : F} (hz : h (-z) ≤ (B : EReal)) :
    ((a - B : ℝ) : EReal) ≤ dirDeriv0 h z := by
  unfold dirDeriv0
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact positive_quotient_lower h hc h0 hz hε

omit [ContinuousSMul ℝ F] in
lemma convex_stablySet (h : F → EReal) (hc : ConvexFn h)
    (hb : ∃ B : ℝ, ∀ᶠ z in nhds (0 : F), h z ≤ (B : EReal)) : StablySet h := by
  obtain ⟨B, V, hVo, hV0, hVneg, hVB⟩ := symmetric_upper h hb
  refine ⟨(hVB 0 hV0).trans_lt (EReal.coe_lt_top B), ?_⟩
  rintro ⟨a, h0, hbad⟩
  obtain ⟨z, hz, hlt⟩ := hbad V (hVo.mem_nhds hV0) (B - a)
  have hle := directional_lower h hc h0 (hVB _ (hVneg z hz))
  have he : -(B - a) = a - B := by ring
  rw [he] at hlt
  exact (not_lt_of_ge hle) hlt

end Topology
end StabilityProof

open Set Filter
open scoped Topology

namespace DualityStability.Stability

/-- Rockafellar (1967), Theorem 1, p. 175: under the standing hypotheses of §3 (`E`, `F` real
locally convex Hausdorff spaces, `A : E → F` continuous linear, `f` l.s.c. proper convex on `E`,
`g` u.s.c. proper concave on `F`), suppose there exists at least one `x ∈ E` such that `f` is
finite at `x`, and `g` is finite and continuous at `Ax`. Then `(P)` is stably set, and
`inf (P(z))` is a continuous function of `z` in some neighborhood of `z = 0`. -/
theorem theorem_1 {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    (A : E →L[ℝ] F) (f : E → EReal) (g : F → EReal)
    (hf : ProperConvexFn f) (hf_lsc : LowerSemicontinuous f)
    (hg : ProperConcaveFn g) (hg_usc : UpperSemicontinuous g)
    (hx : ∃ x : E, f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ g (A x) ≠ ⊥ ∧ g (A x) ≠ ⊤ ∧ ContinuousAt g (A x)) :
    StablySet (perturbInf f g A) ∧ ∃ U ∈ nhds (0 : F), ContinuousOn (perturbInf f g A) U := by
  have _ := hf_lsc
  have _ := hg_usc
  have hc := StabilityProof.perturb_convex A f g hf hg
  have hb := StabilityProof.perturb_upper A f g hx
  exact ⟨StabilityProof.convex_stablySet _ hc hb,
    StabilityProof.convex_continuous_neighborhood _ hc hb⟩

end DualityStability.Stability

open DualityStability.Stability

theorem solution {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    (A : E →L[ℝ] F) (f : E → EReal) (g : F → EReal)
    (hf : ProperConvexFn f) (hf_lsc : LowerSemicontinuous f)
    (hg : ProperConcaveFn g) (hg_usc : UpperSemicontinuous g)
    (hx : ∃ x : E, f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ g (A x) ≠ ⊥ ∧ g (A x) ≠ ⊤ ∧ ContinuousAt g (A x)) :
    StablySet (perturbInf f g A) ∧ ∃ U ∈ nhds (0 : F), ContinuousOn (perturbInf f g A) U := by
  exact DualityStability.Stability.theorem_1 A f g hf hf_lsc hg hg_usc hx
