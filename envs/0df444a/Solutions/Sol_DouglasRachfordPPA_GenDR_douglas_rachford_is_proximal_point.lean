-- Prove2me | solution 1 for DouglasRachfordPPA.GenDR.douglas_rachford_is_proximal_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:15:51.166002+00:00
-- url     : https://prove2.me/submissions/dfd08371-33e5-437b-87a7-80e35e596dd5

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator

set_option autoImplicit false

open InnerProductSpace ThreeOpSplitting.Convergence in
theorem DRPPA_d9dcf3d1_uniq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → Set H) (hT : IsMonotoneOp T) (lam : ℝ) (hlam : 0 < lam)
    (p p' c c' : H) (hc : c ∈ T p) (hc' : c' ∈ T p')
    (h : p + lam • c = p' + lam • c') : p = p' := by
  have h1 := hT p p' c c' hc hc'
  have h2 : c - c' = lam⁻¹ • (p' - p) := by
    have : lam • (c - c') = p' - p := by linear_combination (norm := module) h
    rw [← this, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  rw [h2, inner_smul_right] at h1
  have h3 : ⟪p - p', p' - p⟫_ℝ = -‖p - p'‖ ^ 2 := by
    rw [← neg_sub p p', inner_neg_right, real_inner_self_eq_norm_sq]
  rw [h3] at h1
  have h4 : ‖p - p'‖ ^ 2 ≤ 0 := by
    have := inv_pos.mpr hlam
    nlinarith
  have : ‖p - p'‖ = 0 := by nlinarith [norm_nonneg (p - p')]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

open InnerProductSpace ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR in
theorem DRPPA_d9dcf3d1_part1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lam : ℝ) (hlam : 0 < lam) (A B : H → Set H)
    (hA : IsMonotoneOp A) (hB : IsMonotoneOp B)
    (JA JB : H → H) (hJA : IsResolvent lam A JA) (hJB : IsResolvent lam B JB) (x : H) :
    opResolvent 1 (splittingOp lam A B) x = {drMap JA JB x} := by
  ext y
  simp only [opResolvent, opInv, opAdd, opId, opSmul, splittingOp, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, one_smul]
  constructor
  · rintro ⟨y', rfl, z, ⟨s, ⟨u, b, v, a, hb, ha, hva, hy, hs⟩, rfl⟩, hx⟩
    have hxu : x = u + lam • b := by rw [hx, hy, hs]; abel
    have hlam' : lam ≠ 0 := hlam.ne'
    have hb' := hJB x
    have hu : u = JB x := by
      refine DRPPA_d9dcf3d1_uniq B hB lam hlam u (JB x) b _ hb hb' ?_
      rw [smul_smul, mul_inv_cancel₀ hlam', one_smul, ← hxu]; abel
    have hbb : lam • b = x - JB x := by rw [← hu, hxu]; abel
    have ha' := hJA ((2 : ℝ) • JB x - x)
    have hv : v = JA ((2 : ℝ) • JB x - x) := by
      refine DRPPA_d9dcf3d1_uniq A hA lam hlam v _ a _ ha ha' ?_
      rw [smul_smul, mul_inv_cancel₀ hlam', one_smul, hva, hbb, hu]
      module
    rw [hy, hv, hbb]
    rfl
  · rintro rfl
    refine ⟨drMap JA JB x, rfl, x - drMap JA JB x, ⟨x - drMap JA JB x,
      ⟨JB x, lam⁻¹ • (x - JB x), JA ((2 : ℝ) • JB x - x),
        lam⁻¹ • (((2 : ℝ) • JB x - x) - JA ((2 : ℝ) • JB x - x)), hJB x,
        hJA _, ?_, ?_, by simp only [drMap]; abel⟩, rfl⟩, by abel⟩
    · rw [smul_smul, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, one_smul]; module
    · rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]; simp only [drMap]

open InnerProductSpace ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (lam : ℝ) (hlam : 0 < lam) (A B : H → Set H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : H → H) (hJA : IsResolvent lam A JA) (hJB : IsResolvent lam B JB) :
    (∀ x : H, opResolvent 1 (splittingOp lam A B) x = {drMap JA JB x}) ∧
    (∀ z : ℕ → H, (∀ k, z (k + 1) = drMap JA JB (z k)) ↔
      (∀ k, z (k + 1) ∈ opResolvent 1 (splittingOp lam A B) (z k))) := by
  have h1 := DRPPA_d9dcf3d1_part1 lam hlam A B hA.1 hB.1 JA JB hJA hJB
  refine ⟨h1, fun z => ?_⟩
  simp only [h1, Set.mem_singleton_iff]
