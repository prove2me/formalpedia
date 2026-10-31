-- Prove2me | solution 1 for DoubleAuctionEff.Repeated.C_bounded
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:53:45.22113+00:00
-- url     : https://prove2.me/submissions/5a3c58e2-fe86-4080-afa2-c39e1a49ac31

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open DoubleAuctionEff.Repeated Filter Topology

namespace DAECBoundedAux

theorem u_ne_top {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (x : J → ℝ) : u x ≠ ⊤ := by
  intro h
  have hx : x ∈ dom u := by simp [dom, h]
  have := h1.2.2 x hx 1 one_pos
  rw [h] at this
  exact not_top_lt this

/-- Recession argument: if a level set of a usc concave function contains points
`x0 + λ_k d_k` with `λ_k → ∞`, `d_k → d`, then `d` is a recession direction of `u`. -/
theorem recession {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (x0 : J → ℝ) (hx0 : x0 ∈ dom u) (lam : ℕ → ℝ) (d : ℕ → J → ℝ) (dd : J → ℝ)
    (hlam : Tendsto lam atTop atTop) (hd : Tendsto d atTop (𝓝 dd))
    (hmem : ∀ k, u x0 ≤ u (x0 + lam k • d k)) : IsRecessionDir u dd := by
  intro z hz α hα
  by_contra hlt
  push_neg at hlt
  obtain ⟨a', ha'1, ha'2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  set a : ℝ := (u z).toReal
  set b : ℝ := (u x0).toReal
  have hza : u z = (a : EReal) := (EReal.coe_toReal (u_ne_top h1 z) (ne_of_gt hz)).symm
  have hxb : u x0 = (b : EReal) := (EReal.coe_toReal (u_ne_top h1 x0) (ne_of_gt hx0)).symm
  have ha'a : a' < a := by rw [hza] at ha'2; exact_mod_cast ha'2
  -- θ_k = α / λ_k → 0
  have hθ : Tendsto (fun k => α / lam k) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlam
  set w : ℕ → J → ℝ := fun k => (α / lam k) • (x0 + lam k • d k) + (1 - α / lam k) • z
  have hlampos : ∀ᶠ k in atTop, 0 < lam k := hlam.eventually_gt_atTop 0
  have hw_eq : ∀ᶠ k in atTop, w k = z + (α / lam k) • (x0 - z) + α • d k := by
    filter_upwards [hlampos] with k hk
    simp only [w, smul_add, smul_smul, sub_smul, one_smul, smul_sub]
    rw [div_mul_cancel₀ α hk.ne']
    abel
  have hw : Tendsto w atTop (𝓝 (z + α • dd)) := by
    have : Tendsto (fun k => z + (α / lam k) • (x0 - z) + α • d k) atTop
        (𝓝 (z + (0 : ℝ) • (x0 - z) + α • dd)) :=
      ((tendsto_const_nhds.add (hθ.smul tendsto_const_nhds)).add (hd.const_smul α))
    rw [zero_smul, add_zero] at this
    exact this.congr' (hw_eq.mono fun k hk => hk.symm)
  have hev1 : ∀ᶠ k in atTop, u (w k) < a' := hw.eventually (h1.1 _ _ ha'1)
  have hval : Tendsto (fun k => (α / lam k) * b + (1 - α / lam k) * a) atTop
      (𝓝 (0 * b + (1 - 0) * a)) :=
    (hθ.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub hθ).mul tendsto_const_nhds)
  rw [zero_mul, zero_add, sub_zero, one_mul] at hval
  have hev2 : ∀ᶠ k in atTop, a' < (α / lam k) * b + (1 - α / lam k) * a :=
    hval.eventually (lt_mem_nhds ha'a)
  have hev3 : ∀ᶠ k in atTop, α / lam k ≤ 1 := hθ.eventually (ge_mem_nhds one_pos)
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := (hev1.and (hev2.and (hev3.and hlampos))).exists
  have hθ0 : 0 ≤ α / lam k := div_nonneg hα.le hk4.le
  have hA : ((x0 + lam k • d k, b) : (J → ℝ) × ℝ) ∈
      {q : (J → ℝ) × ℝ | ((q.2 : ℝ) : EReal) ≤ u q.1} := by
    show (b : EReal) ≤ _; rw [← hxb]; exact hmem k
  have hB : ((z, a) : (J → ℝ) × ℝ) ∈ {q : (J → ℝ) × ℝ | ((q.2 : ℝ) : EReal) ≤ u q.1} := by
    show (a : EReal) ≤ _; rw [← hza]
  have hC := h1.2.1 hA hB hθ0 (sub_nonneg.2 hk3) (by ring)
  have hC' : (((α / lam k) * b + (1 - α / lam k) * a : ℝ) : EReal) ≤ u (w k) := by
    simpa [w, smul_eq_mul] using hC
  have : (((α / lam k) * b + (1 - α / lam k) * a : ℝ) : EReal) < a' :=
    lt_of_le_of_lt hC' hk1
  rw [EReal.coe_lt_coe_iff] at this
  linarith

end DAECBoundedAux

open DAECBoundedAux in
theorem solution {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J]
    [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x0 : I → J → ℝ)
    (h1 : ∀ i, Assumption1 (u i) g) (h3 : Assumption3 u) (hx0 : ∀ i, x0 i ∈ dom (u i)) :
    Bornology.IsBounded {x : I → J → ℝ | ∑ i, x i = ∑ i, x0 i ∧ ∀ i, u i (x0 i) ≤ u i (x i)} := by
  set S := {x : I → J → ℝ | ∑ i, x i = ∑ i, x0 i ∧ ∀ i, u i (x0 i) ≤ u i (x i)} with hS
  by_contra hnb
  have hfar : ∀ n : ℕ, ∃ x ∈ S, (n : ℝ) + 1 < ‖x - x0‖ := by
    intro n
    by_contra hcon
    push_neg at hcon
    apply hnb
    refine (Metric.isBounded_closedBall (x := x0) (r := (n : ℝ) + 1)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hcon x hx
  choose xs hxsS hxsfar using hfar
  set lam : ℕ → ℝ := fun n => ‖xs n - x0‖
  have hlampos : ∀ n, 0 < lam n := fun n =>
    lt_trans (by positivity) (hxsfar n)
  set d : ℕ → I → J → ℝ := fun n => (lam n)⁻¹ • (xs n - x0)
  have hdnorm : ∀ n, d n ∈ Metric.sphere (0 : I → J → ℝ) 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm]
    simp only [d, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hlampos n)]
    exact inv_mul_cancel₀ (hlampos n).ne'
  obtain ⟨dd, hddS, φ, hφ, hlim⟩ := (isCompact_sphere (0 : I → J → ℝ) 1).tendsto_subseq hdnorm
  have hxs_eq : ∀ n, xs n = x0 + lam n • d n := by
    intro n
    simp only [d, smul_smul, mul_inv_cancel₀ (hlampos n).ne', one_smul]
    abel
  -- the limit direction has zero sum
  have hsum : ∑ i, dd i = 0 := by
    have hc : Continuous (fun v : I → J → ℝ => ∑ i, v i) := by fun_prop
    have h0 : ∀ n, ∑ i, d n i = 0 := by
      intro n
      simp only [d, Pi.smul_apply, Pi.sub_apply, ← Finset.smul_sum, Finset.sum_sub_distrib,
        (hxsS n).1, sub_self, smul_zero]
    have := (hc.tendsto dd).comp hlim
    have h' : Tendsto (fun _ : ℕ => (0 : J → ℝ)) atTop (𝓝 (∑ i, dd i)) := by
      refine this.congr fun k => ?_
      simp [Function.comp, h0]
    exact (tendsto_nhds_unique h' tendsto_const_nhds)
  -- each component is a recession direction
  have hrec : ∀ i, IsRecessionDir (u i) (dd i) := by
    intro i
    have hlamφ : Tendsto (fun k => lam (φ k)) atTop atTop := by
      refine tendsto_atTop_mono (fun k => (hxsfar (φ k)).le) ?_
      refine tendsto_atTop_add_const_right _ 1 ?_
      exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
    refine recession (h1 i) (x0 i) (hx0 i) (fun k => lam (φ k)) (fun k => d (φ k) i) (dd i)
      hlamφ ((continuous_apply i).tendsto dd |>.comp hlim) fun k => ?_
    have := (hxsS (φ k)).2 i
    rw [hxs_eq (φ k)] at this
    simpa using this
  have hzero := h3 dd hrec hsum
  rw [mem_sphere_zero_iff_norm, hzero, norm_zero] at hddS
  exact zero_ne_one hddS
