-- Prove2me | solution 1 for CtxInvOpt.PolyCone.lemmaB2_inradius
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:59:37.318123+00:00
-- url     : https://prove2.me/submissions/3c686698-548d-42a7-91ca-6e1793bf8700

import Mathlib
import Definitions.Def_CtxInvOpt_PolyCone_Cones

open CtxInvOpt.PolyCone

theorem solution {p : ℕ} (hp : 2 ≤ p) (g : Fin p → EuclideanSpace ℝ (Fin p))
    (hli : LinearIndependent ℝ g) (hunit : ∀ i, ‖g i‖ = 1) (lmin lmax : ℝ) (hlmin : 0 < lmin)
    (hbracket : ∀ u : Fin p → ℝ,
      lmin * (∑ i, u i ^ 2) ≤ ‖∑ i, u i • g i‖ ^ 2 ∧
        ‖∑ i, u i • g i‖ ^ 2 ≤ lmax * (∑ i, u i ^ 2)) :
    1 / Real.sqrt p * Real.sqrt (lmin / lmax) ≤ inradius (simplicialCone g) := by
  have : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  set b := basisOfLinearIndependentOfCardEqFinrank hli (by simp) with hbdef
  have hb : ⇑b = g := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  set K := simplicialCone g with hK
  have hrep : ∀ y, y = ∑ i, b.repr y i • g i := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [hb]
  have hcoef : ∀ (c : Fin p → ℝ) (i : Fin p), b.repr (∑ j, c j • g j) i = c i := by
    intro c i; rw [← hb, b.repr_sum_self]
  -- points of the frontier have a nonpositive coordinate
  have hfr : ∀ y ∈ frontier K, ∃ i, b.repr y i ≤ 0 := by
    intro y hy
    by_contra h
    push Not at h
    set U : Set (EuclideanSpace ℝ (Fin p)) := ⋂ i, (fun z => b.repr z i) ⁻¹' Set.Ioi 0
    have hU : IsOpen U := by
      refine isOpen_iInter_of_finite (fun i => ?_)
      have hc : Continuous (fun z => b.repr z i) := by
        have := LinearMap.continuous_of_finiteDimensional (b.coord i)
        exact this
      exact isOpen_Ioi.preimage hc
    have hUK : U ⊆ K := by
      intro z hz
      simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi] at hz
      exact ⟨fun i => b.repr z i, fun i => (hz i).le, hrep z⟩
    have hyU : y ∈ U := by
      simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]; exact h
    exact hy.2 (interior_maximal hUK hU hyU)
  -- the frontier is nonempty
  have hne : (frontier K).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have hcl : IsClopen K := isClopen_iff_frontier_eq_empty.mpr h
    rcases isClopen_iff.mp hcl with h0 | h0
    · have : (0 : EuclideanSpace ℝ (Fin p)) ∈ K := ⟨fun _ => 0, fun _ => le_rfl, by simp⟩
      rw [h0] at this; exact this
    · have : -g ⟨0, by omega⟩ ∈ K := by rw [h0]; trivial
      obtain ⟨α, hα0, hα⟩ := this
      have h1 := congrArg (fun z => b.repr z ⟨0, by omega⟩) hα
      simp only [hcoef] at h1
      have h2 : b.repr (-g ⟨0, by omega⟩) ⟨0, by omega⟩ = -1 := by
        rw [map_neg, ← hb, b.repr_self]; simp
      rw [h2] at h1
      linarith [hα0 ⟨0, by omega⟩]
  -- the centre point
  set s : EuclideanSpace ℝ (Fin p) := ∑ i, g i with hs
  have hp' : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hsl : lmin * p ≤ ‖s‖ ^ 2 := by
    have := (hbracket (fun _ => 1)).1; simpa [hs] using this
  have hsu : ‖s‖ ^ 2 ≤ lmax * p := by
    have := (hbracket (fun _ => 1)).2; simpa [hs] using this
  have hs2 : 0 < ‖s‖ ^ 2 := lt_of_lt_of_le (by positivity) hsl
  have hspos : 0 < ‖s‖ := by
    rcases (norm_nonneg s).lt_or_eq with h | h
    · exact h
    · rw [← h] at hs2; simp at hs2
  have hlmax : 0 < lmax := by
    by_contra h; push Not at h; nlinarith
  set x : EuclideanSpace ℝ (Fin p) := ∑ i, (fun _ => ‖s‖⁻¹) i • g i with hx
  have hxs : x = ‖s‖⁻¹ • s := by rw [hx, hs, Finset.smul_sum]
  have hxn : ‖x‖ = 1 := by
    rw [hxs, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hspos.ne']
  have hxK : x ∈ K := ⟨fun _ => ‖s‖⁻¹, fun _ => by positivity, rfl⟩
  have hxmem : x ∈ CtxInvOpt.Offline.unitSphere p ∩ K := by
    refine ⟨?_, hxK⟩
    simp [CtxInvOpt.Offline.unitSphere, hxn]
  set r := 1 / Real.sqrt p * Real.sqrt (lmin / lmax) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = lmin / (lmax * p) := by
    rw [hr, mul_pow, div_pow, Real.sq_sqrt hp'.le, Real.sq_sqrt (by positivity)]
    field_simp
  have hdist : r ≤ Metric.infDist x (frontier K) := by
    rw [Metric.le_infDist hne]
    intro y hy
    obtain ⟨i, hi⟩ := hfr y hy
    set u : Fin p → ℝ := fun j => b.repr x j - b.repr y j with hu
    have hxy : x - y = ∑ j, u j • g j := by
      conv_lhs => rw [hrep x, hrep y]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hu, sub_smul]
    have hxi : b.repr x i = ‖s‖⁻¹ := by rw [hx, hcoef]
    have hui : ‖s‖⁻¹ ≤ u i := by simp only [hu]; rw [hxi]; linarith
    have hsum : u i ^ 2 ≤ ∑ j, u j ^ 2 :=
      Finset.single_le_sum (f := fun j => u j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hlow := (hbracket u).1
    rw [← hxy] at hlow
    have hinv : (‖s‖⁻¹) ^ 2 ≤ u i ^ 2 := pow_le_pow_left₀ (by positivity) hui 2
    have h3 : lmin * (‖s‖⁻¹) ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left (hinv.trans hsum) hlmin.le
      linarith
    have h4 : lmin / (lmax * p) ≤ lmin * (‖s‖⁻¹) ^ 2 := by
      rw [inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left hlmin.le hs2 hsu
    rw [dist_eq_norm]
    have h5 : r ^ 2 ≤ ‖x - y‖ ^ 2 := by rw [hr2]; linarith
    exact (pow_le_pow_iff_left₀ hr0 (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp h5
  refine hdist.trans ?_
  unfold inradius
  obtain ⟨y0, hy0⟩ := hne
  refine le_ciSup (f := fun z : (CtxInvOpt.Offline.unitSphere p ∩ K : Set _) =>
    Metric.infDist (z : EuclideanSpace ℝ (Fin p)) (frontier K)) ⟨1 + ‖y0‖, ?_⟩ ⟨x, hxmem⟩
  rintro _ ⟨z, rfl⟩
  have hz : ‖(z : EuclideanSpace ℝ (Fin p))‖ = 1 := by
    have := z.2.1; simpa [CtxInvOpt.Offline.unitSphere] using this
  calc Metric.infDist (z : EuclideanSpace ℝ (Fin p)) (frontier K)
      ≤ dist (z : EuclideanSpace ℝ (Fin p)) y0 := Metric.infDist_le_dist_of_mem hy0
    _ ≤ ‖(z : EuclideanSpace ℝ (Fin p))‖ + ‖y0‖ := by
        rw [dist_eq_norm]; exact norm_sub_le _ _
    _ = 1 + ‖y0‖ := by rw [hz]
