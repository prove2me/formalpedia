-- Prove2me | solution 1 for BilevelSOC.SecondOrder.remark_5_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:59:34.208975+00:00
-- url     : https://prove2.me/submissions/97208318-8105-4633-b5df-418b22a3a662

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Model

open scoped Topology
open Filter

open BilevelSOC.SecondOrder in
theorem solution {n m p q : ℕ} (D : Data n m p q) (hD : Standing D)
    (xbar : E n) (ybar : Y m) (hfeas : (xbar, ybar) ∈ feasSet D)
    (φr : E n → ℝ) (U : Set (E n)) (hU : U ∈ 𝓝 xbar)
    (hφU : ∀ x ∈ U, valueFn D x = (φr x : EReal))
    (L : NNReal) (hLip : LipschitzOnWith L φr U)
    (φ' : E n → ℝ) (hφDiff : ∀ d, HasDirDerivAt φr xbar d (φ' d))
    (hACQ : ACQ52 D (xbar, ybar)) :
    (∀ d : E n × Y m,
      (∀ j ∈ actg D (xbar, ybar), fderiv ℝ (D.g j) (xbar, ybar) d ≤ 0) →
      0 ≤ fderiv ℝ D.f (xbar, ybar) d - φ' d.1) ∧
    linConeVF D (xbar, ybar) φ' =
      {d | (∀ i ∈ actG D (xbar, ybar), fderiv ℝ (D.G i) (xbar, ybar) d ≤ 0) ∧
        fderiv ℝ D.f (xbar, ybar) d - φ' d.1 = 0 ∧
        ∀ j ∈ actg D (xbar, ybar), fderiv ℝ (D.g j) (xbar, ybar) d ≤ 0} := by
  set z : E n × Y m := (xbar, ybar) with hz
  have hxU : xbar ∈ U := mem_of_mem_nhds hU
  -- value at xbar
  have hval : φr xbar = D.f z := by
    have h1 := hφU xbar hxU
    have hy := hfeas.2
    have h2 : valueFn D xbar = (D.f (xbar, ybar) : EReal) := by
      apply le_antisymm
      · exact iInf₂_le ybar hy.1
      · exact le_iInf₂ (fun y hy' => EReal.coe_le_coe_iff.2 (hy.2 y hy'))
    rw [h1] at h2
    exact_mod_cast h2
  have part1 : ∀ d : E n × Y m,
      (∀ j ∈ actg D (xbar, ybar), fderiv ℝ (D.g j) (xbar, ybar) d ≤ 0) →
      0 ≤ fderiv ℝ D.f (xbar, ybar) d - φ' d.1 := by
    intro d hd
    have hdT : d ∈ tangentCone (lowerSet D) z := by
      rw [show tangentCone (lowerSet D) z = linCone52 D z from hACQ]
      exact hd
    obtain ⟨t, dk, htpos, ht0, hdk, hmem⟩ := hdT
    -- LHS limit
    have hfd : HasFDerivAt D.f (fderiv ℝ D.f z) z :=
      ((hD.2.1.differentiable (by norm_num)) z).hasFDerivAt
    have htd0 : Tendsto (fun k => t k • dk k) atTop (𝓝 0) := by
      have := ht0.smul hdk
      simpa using this
    have hcd : Tendsto (fun k => (t k)⁻¹ • (t k • dk k)) atTop (𝓝 d) := by
      have : (fun k => (t k)⁻¹ • (t k • dk k)) = dk := by
        funext k
        rw [smul_smul, inv_mul_cancel₀ (htpos k).ne', one_smul]
      rw [this]; exact hdk
    have hL := (hfd.hasFDerivWithinAt (s := Set.univ)).lim htd0
      (Eventually.of_forall (fun k => Set.mem_univ _)) hcd
    -- RHS limit
    have htw : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.2 ⟨ht0, Eventually.of_forall htpos⟩
    have hb : Tendsto (fun k => (t k)⁻¹ * (φr (xbar + t k • d.1) - φr xbar)) atTop
        (𝓝 (φ' d.1)) := by
      have := (hφDiff d.1).comp htw
      refine this.congr (fun k => ?_)
      simp only [Function.comp, div_eq_inv_mul]
    have hdk1 : Tendsto (fun k => (dk k).1) atTop (𝓝 d.1) := (continuous_fst.tendsto d).comp hdk
    have hpk : Tendsto (fun k => xbar + t k • (dk k).1) atTop (𝓝 xbar) := by
      have := tendsto_const_nhds (x := xbar) |>.add (ht0.smul hdk1)
      simpa using this
    have hqk : Tendsto (fun k => xbar + t k • d.1) atTop (𝓝 xbar) := by
      have := tendsto_const_nhds (x := xbar) |>.add (ht0.smul_const d.1)
      simpa using this
    have hpU := hpk.eventually (mem_of_superset hU subset_rfl)
    have hqU := hqk.eventually (mem_of_superset hU subset_rfl)
    have hdiff : Tendsto (fun k => (t k)⁻¹ * (φr (xbar + t k • (dk k).1) - φr xbar) -
        (t k)⁻¹ * (φr (xbar + t k • d.1) - φr xbar)) atTop (𝓝 0) := by
      have hbound : Tendsto (fun k => (L : ℝ) * ‖(dk k).1 - d.1‖) atTop (𝓝 0) := by
        have h1 : Tendsto (fun k => (dk k).1 - d.1) atTop (𝓝 0) := by
          have := hdk1.sub_const d.1
          simpa using this
        have := (h1.norm).const_mul (L : ℝ)
        simpa using this
      apply squeeze_zero_norm' _ hbound
      filter_upwards [hpU, hqU] with k hp hq
      rw [← mul_sub, sub_sub_sub_cancel_right, norm_mul, norm_inv, Real.norm_eq_abs,
        abs_of_pos (htpos k)]
      have hl := hLip.dist_le_mul _ hp _ hq
      rw [Real.dist_eq, dist_eq_norm] at hl
      have e : xbar + t k • (dk k).1 - (xbar + t k • d.1) = t k • ((dk k).1 - d.1) := by
        rw [smul_sub]; abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (htpos k)] at hl
      rw [Real.norm_eq_abs]
      calc (t k)⁻¹ * |φr (xbar + t k • (dk k).1) - φr (xbar + t k • d.1)|
          ≤ (t k)⁻¹ * (L * (t k * ‖(dk k).1 - d.1‖)) :=
            mul_le_mul_of_nonneg_left hl (inv_nonneg.2 (htpos k).le)
        _ = L * ‖(dk k).1 - d.1‖ := by
            rw [mul_left_comm, inv_mul_cancel_left₀ (htpos k).ne']
    have ha : Tendsto (fun k => (t k)⁻¹ * (φr (xbar + t k • (dk k).1) - φr xbar)) atTop
        (𝓝 (φ' d.1)) := by
      have := hb.add hdiff
      simp only [add_zero] at this
      refine this.congr (fun k => ?_)
      ring
    -- comparison
    have hle : ∀ᶠ k in atTop, (t k)⁻¹ * (φr (xbar + t k • (dk k).1) - φr xbar) ≤
        (t k)⁻¹ • (D.f (z + t k • dk k) - D.f z) := by
      filter_upwards [hpU] with k hp
      rw [smul_eq_mul]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (htpos k).le)
      have hzk := hmem k
      have hfeasy : (z + t k • dk k).2 ∈ lowerFeas D (xbar + t k • (dk k).1) := by
        intro j
        have := hzk j
        have e : (xbar + t k • (dk k).1, (z + t k • dk k).2) = z + t k • dk k := by
          ext <;> simp [hz]
        rw [e]; exact this
      have hv := hφU _ hp
      have h1 : valueFn D (xbar + t k • (dk k).1) ≤
          (D.f (xbar + t k • (dk k).1, (z + t k • dk k).2) : EReal) := iInf₂_le _ hfeasy
      rw [hv] at h1
      have h2 : φr (xbar + t k • (dk k).1) ≤ D.f (xbar + t k • (dk k).1, (z + t k • dk k).2) :=
        EReal.coe_le_coe_iff.1 h1
      have e : (xbar + t k • (dk k).1, (z + t k • dk k).2) = z + t k • dk k := by
        ext <;> simp [hz]
      rw [e] at h2
      rw [hval]
      linarith
    have := le_of_tendsto_of_tendsto ha hL hle
    linarith
  refine ⟨part1, ?_⟩
  ext d
  simp only [linConeVF, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, le_antisymm h2 (part1 d h3), h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2.le, h3⟩
