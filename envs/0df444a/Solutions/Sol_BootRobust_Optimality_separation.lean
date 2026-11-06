-- Prove2me | solution 1 for BootRobust.Optimality.separation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:16:06.544546+00:00
-- url     : https://prove2.me/submissions/bc2de98a-e9f5-4dba-bfa9-cfee81660c00

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : (ι → ℝ) → (ι → ℝ) → EReal) (hR : BootRobust.Optimality.IsDistributionDistance R)
    (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι) (r : ℝ)
    (N : Set (ι → ℝ)) (hN : BootRobust.Optimality.relOpen N) (hNconv : Convex ℝ N)
    (hNne : N.Nonempty)
    (hNpos : ∀ D' ∈ N, ∀ i, 0 < D' i) (hRN : ∀ D' ∈ N, (r : EReal) < R D' Dtr) :
    ∃ G : ι → ℝ, ∃ a : ℝ,
      (∀ D ∈ stdSimplex ℝ ι, R D Dtr ≤ (r : EReal) → ∑ i, D i * G i ≤ a) ∧
      (∀ D' ∈ N, a < ∑ i, D' i * G i) := by
  obtain ⟨U, hU, rfl⟩ := hN
  obtain ⟨x0, hx0⟩ := hNne
  haveI : Nonempty ι := ⟨(Fintype.card_pos_iff.mp (by
    by_contra h
    have h0 : Fintype.card ι = 0 := by omega
    have := hx0.2.2
    rw [Fintype.card_eq_zero_iff] at h0
    simp at this)).some⟩
  set c : ℝ := (Fintype.card ι : ℝ) with hc
  have hcpos : 0 < c := by rw [hc]; exact_mod_cast Fintype.card_pos
  -- projection onto the hyperplane `∑ x = 1` along the all-ones vector
  let proj : (ι → ℝ) → (ι → ℝ) := fun x i => x i - ((∑ j, x j) - 1) / c
  have hproj_sum : ∀ x, ∑ i, proj x i = 1 := by
    intro x
    simp only [proj, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hc]; field_simp; ring
  have hproj_simp : ∀ x ∈ stdSimplex ℝ ι, proj x = x := by
    intro x hx; funext i; simp [proj, hx.2]
  have hproj_cont : Continuous proj := by
    refine continuous_pi (fun i => ?_)
    exact (continuous_apply i).sub ((continuous_finset_sum _ (fun j _ => continuous_apply j)).sub
      continuous_const |>.div_const _)
  let pos : Set (ι → ℝ) := ⋂ i, {y | 0 < y i}
  have hpos_open : IsOpen pos :=
    isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
  let s : Set (ι → ℝ) := proj ⁻¹' (U ∩ stdSimplex ℝ ι)
  have hs_eq : s = proj ⁻¹' (U ∩ pos) := by
    ext x
    simp only [s, pos, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hNpos _ ⟨h1, h2⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => (h2 i).le, hproj_sum x⟩
  have hs_open : IsOpen s := by
    rw [hs_eq]; exact (hU.inter hpos_open).preimage hproj_cont
  have hs_conv : Convex ℝ s := by
    intro x hx y hy a b ha hb hab
    have : proj (a • x + b • y) = a • proj x + b • proj y := by
      funext i
      simp only [proj, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      rw [show b = 1 - a by linarith]
      field_simp
      ring
    show proj (a • x + b • y) ∈ U ∩ stdSimplex ℝ ι
    rw [this]
    exact hNconv hx hy ha hb hab
  let t : Set (ι → ℝ) := {D | D ∈ stdSimplex ℝ ι ∧ R D Dtr ≤ (r : EReal)}
  have ht_conv : Convex ℝ t := by
    rintro x ⟨hx, hxr⟩ y ⟨hy, hyr⟩ a b ha hb hab
    refine ⟨(convex_stdSimplex ℝ ι) hx hy ha hb hab, ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have h1 := hR.convex Dtr hDtr x hx y hy a ha (by linarith)
    refine h1.trans ?_
    have hx0 := hR.nonneg x hx Dtr hDtr
    have hy0 := hR.nonneg y hy Dtr hDtr
    have ex : R x Dtr = ((R x Dtr).toReal : EReal) := by
      rw [EReal.coe_toReal]
      · exact ne_top_of_le_ne_top (EReal.coe_ne_top r) hxr
      · exact ne_bot_of_le_ne_bot (by simp) hx0
    have ey : R y Dtr = ((R y Dtr).toReal : EReal) := by
      rw [EReal.coe_toReal]
      · exact ne_top_of_le_ne_top (EReal.coe_ne_top r) hyr
      · exact ne_bot_of_le_ne_bot (by simp) hy0
    rw [ex] at hxr
    rw [ey] at hyr
    rw [ex, ey]
    have hxr' : (R x Dtr).toReal ≤ r := by exact_mod_cast hxr
    have hyr' : (R y Dtr).toReal ≤ r := by exact_mod_cast hyr
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    have : a * (R x Dtr).toReal + (1 - a) * (R y Dtr).toReal ≤ r := by
      have := mul_le_mul_of_nonneg_left hxr' ha
      have := mul_le_mul_of_nonneg_left hyr' (show 0 ≤ 1 - a by linarith)
      nlinarith
    exact_mod_cast this
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro x hxs ⟨hxt, hxr⟩
    have : proj x = x := hproj_simp x hxt
    have hxN : x ∈ U ∩ stdSimplex ℝ ι := by
      have := hxs; simp only [s, Set.mem_preimage] at this; rwa [hproj_simp x hxt] at this
    exact absurd hxr (not_le.mpr (hRN x hxN))
  obtain ⟨f, u, hfs, hft⟩ := geometric_hahn_banach_open hs_conv hs_open ht_conv hdisj
  have hf : ∀ x : ι → ℝ, f x = ∑ i, x i * f (fun j => if i = j then 1 else 0) := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) x
    simpa [smul_eq_mul] using this
  refine ⟨fun i => -f (fun j => if i = j then 1 else 0), -u, ?_, ?_⟩
  · intro D hD hDr
    have := hft D ⟨hD, hDr⟩
    have e : ∑ i, D i * -f (fun j => if i = j then 1 else 0) = - f D := by
      rw [hf D]; simp [Finset.sum_neg_distrib]
    rw [e]; linarith
  · intro D' hD'
    have hs' : D' ∈ s := by
      show proj D' ∈ U ∩ stdSimplex ℝ ι
      rw [hproj_simp D' hD'.2]; exact hD'
    have := hfs D' hs'
    have e : ∑ i, D' i * -f (fun j => if i = j then 1 else 0) = - f D' := by
      rw [hf D']; simp [Finset.sum_neg_distrib]
    rw [e]; linarith
