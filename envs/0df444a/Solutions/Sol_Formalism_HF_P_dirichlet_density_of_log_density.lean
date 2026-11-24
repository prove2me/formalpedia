-- Prove2me | solution 1 for Formalism.HF.P.dirichlet_density_of_log_density
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:09.928724+00:00
-- url     : https://prove2.me/submissions/8ef2fa08-00fe-4669-9a71-0dda8441efaa

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Theorems.Thm_Formalism_HF_P_hasDerivAt_F
import Theorems.Thm_Formalism_HF_P_tendsto_log_inv_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (S : Set ℕ) (δ : ℝ) (h : LogDensity S δ) : DirDensity S δ := by
  unfold LogDensity at h
  unfold DirDensity
  set f : ℝ → ℝ := fun x => ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
    (fun m : ℕ => 1 / (m : ℝ) ^ x) n with hf
  set g : ℝ → ℝ := fun x => ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
    (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n with hg
  set L : ℝ → ℝ := fun x => Real.log (1 / (x - 1)) with hLdef
  have hder : ∀ x, 1 < x → HasDerivAt f (-g x) x := fun x hx => hasDerivAt_F S hx
  have hlogder : ∀ t : ℝ, 1 < t → HasDerivAt (fun t : ℝ => Real.log (t - 1)) (1 / (t - 1)) t :=
    fun t ht => ((hasDerivAt_id' t).sub_const 1).log (sub_pos.2 ht).ne'
  have hL : Tendsto L (𝓝[>] 1) atTop := tendsto_log_inv_sub_one
  have hLeq : ∀ x, L x = -Real.log (x - 1) := fun x => by
    simp only [hLdef, one_div, Real.log_inv]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set e := ε / 4 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hev := (Metric.tendsto_nhds.1 h) e he0
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  obtain ⟨u, hu1, hu⟩ := hev
  have hu1' : 1 < u := mem_Ioi.1 hu1
  set x₀ := (1 + u) / 2 with hx₀
  have hx₀1 : 1 < x₀ := by rw [hx₀]; linarith
  have hx₀u : x₀ < u := by rw [hx₀]; linarith

  have hgb : ∀ t, 1 < t → t < x₀ → (δ - e) / (t - 1) ≤ g t ∧ g t ≤ (δ + e) / (t - 1) := by
    intro t ht1 ht2
    have ht : t ∈ Ioo 1 u := ⟨ht1, by linarith⟩
    have hd := hu ht
    simp only [mem_ofPred_eq, Real.dist_eq] at hd
    rw [abs_lt] at hd
    have hpos : 0 < t - 1 := sub_pos.2 ht1
    constructor
    · rw [div_le_iff₀ hpos]; linarith
    · rw [le_div_iff₀ hpos]; linarith

  have hmono : MonotoneOn (fun t => f t + (δ + e) * Real.log (t - 1)) (Ioc 1 x₀) := by
    have hd : ∀ t, 1 < t → HasDerivAt (fun t => f t + (δ + e) * Real.log (t - 1))
        (-g t + (δ + e) * (1 / (t - 1))) t :=
      fun t ht => (hder t ht).add ((hlogder t ht).const_mul (δ + e))
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 1 x₀)
      (fun t ht => (hd t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by rw [interior_Ioc] at ht; exact ht.1)).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Ioc] at ht
    have := (hgb t ht.1 ht.2).2
    rw [mul_one_div]
    linarith
  have hanti : AntitoneOn (fun t => f t + (δ - e) * Real.log (t - 1)) (Ioc 1 x₀) := by
    have hd : ∀ t, 1 < t → HasDerivAt (fun t => f t + (δ - e) * Real.log (t - 1))
        (-g t + (δ - e) * (1 / (t - 1))) t :=
      fun t ht => (hder t ht).add ((hlogder t ht).const_mul (δ - e))
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 1 x₀)
      (fun t ht => (hd t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by rw [interior_Ioc] at ht; exact ht.1)).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Ioc] at ht
    have := (hgb t ht.1 ht.2).1
    rw [mul_one_div]
    linarith
  set Cp := f x₀ + (δ + e) * Real.log (x₀ - 1) with hCp
  set Cm := f x₀ + (δ - e) * Real.log (x₀ - 1) with hCm
  have hx₀mem : x₀ ∈ Ioc 1 x₀ := ⟨hx₀1, le_rfl⟩
  have hup : ∀ x, 1 < x → x < x₀ → f x ≤ Cp + (δ + e) * L x := by
    intro x h1 h2
    have := hmono ⟨h1, h2.le⟩ hx₀mem h2.le
    simp only at this
    rw [hLeq]; linarith
  have hlo : ∀ x, 1 < x → x < x₀ → Cm + (δ - e) * L x ≤ f x := by
    intro x h1 h2
    have := hanti ⟨h1, h2.le⟩ hx₀mem h2.le
    simp only at this
    rw [hLeq]; linarith
  have hnear : Ioo 1 x₀ ∈ 𝓝[>] (1:ℝ) := Ioo_mem_nhdsGT hx₀1
  have hLpos : ∀ᶠ x in 𝓝[>] (1:ℝ), 0 < L x := hL.eventually (eventually_gt_atTop 0)
  have hcp : ∀ᶠ x in 𝓝[>] (1:ℝ), |Cp| / L x < e :=
    (tendsto_const_nhds.div_atTop hL).eventually (gt_mem_nhds he0)
  have hcm : ∀ᶠ x in 𝓝[>] (1:ℝ), |Cm| / L x < e :=
    (tendsto_const_nhds.div_atTop hL).eventually (gt_mem_nhds he0)
  filter_upwards [hnear, hLpos, hcp, hcm] with x hx hLp hcpx hcmx
  have h1 := hup x hx.1 hx.2
  have h2 := hlo x hx.1 hx.2
  have hcp' : |Cp| < e * L x := by rw [div_lt_iff₀ hLp] at hcpx; linarith
  have hcm' : |Cm| < e * L x := by rw [div_lt_iff₀ hLp] at hcmx; linarith
  have hq : f x = (f x / L x) * L x := by field_simp
  have hupper : (f x / L x) * L x < (δ + 2 * e) * L x := by
    rw [← hq]; nlinarith [le_abs_self Cp]
  have hlower : (δ - 2 * e) * L x < (f x / L x) * L x := by
    rw [← hq]; nlinarith [neg_abs_le Cm]
  have hu' := lt_of_mul_lt_mul_right hupper hLp.le
  have hl' := lt_of_mul_lt_mul_right hlower hLp.le
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith
end Formalism.HF.P
