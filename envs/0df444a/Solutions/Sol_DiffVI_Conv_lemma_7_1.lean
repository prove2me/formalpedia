-- Prove2me | solution 1 for DiffVI.Conv.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:39:44.764607+00:00
-- url     : https://prove2.me/submissions/dc417a2a-015e-4744-8aa8-86b42b4d9432

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Conv_Setting
open MeasureTheory Filter Topology
open scoped InnerProductSpace

open SolodovSvaiterVI.Alg21 DiffVI.Conv in
theorem solution {n m : ℕ} (T : ℝ) (hT : 0 < T) (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hA : DiffVI.Exist.CondA T f B G) (hB : DiffVI.Exist.CondB T B)
    (Lf ρf σB : ℝ) (hLf0 : 0 < Lf) (hLf : DiffVI.Exist.LipOnΩ T f Lf) (hρf0 : 0 < ρf)
    (hρf : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ (Fin n), ‖f t x‖ ≤ ρf * (1 + ‖x‖))
    (hσB : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ (Fin n), ‖B t x‖ ≤ σB) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h ∈ Set.Ioc (0 : ℝ) h0, ∀ xref : EuclideanSpace ℝ (Fin n), ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ tref ∈ Set.Icc (0 : ℝ) T,
        (∀ u : EuclideanSpace ℝ (Fin m), ∃! x : EuclideanSpace ℝ (Fin n),
          x - xref = h • (f t (θ • xref + (1 - θ) • x) + B tref xref u)) ∧
        (∀ (u u' : EuclideanSpace ℝ (Fin m)) (x x' : EuclideanSpace ℝ (Fin n)),
          x - xref = h • (f t (θ • xref + (1 - θ) • x) + B tref xref u) →
          x' - xref = h • (f t (θ • xref + (1 - θ) • x') + B tref xref u') →
          ‖x - x'‖ ≤ h * σB / (1 - h * (1 - θ) * Lf) * ‖u - u'‖) ∧
        (∀ (u : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)),
          x - xref = h • (f t (θ • xref + (1 - θ) • x) + B tref xref u) →
          ‖x - xref‖ ≤ h * (ρf * (1 + ‖xref‖) + σB * ‖u‖) / (1 - h * (1 - θ) * ρf)) := by
  refine ⟨1 / (2 * (Lf + ρf)), by positivity, ?_⟩
  intro h hh xref θ hθ t ht tref htref
  have hpos : 0 < h := hh.1
  have hLsum : 0 < Lf + ρf := by linarith
  have hhL : h * Lf ≤ 1 / 2 := by
    have := hh.2
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hhρ : h * ρf ≤ 1 / 2 := by
    have := hh.2
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hθ1 : 0 ≤ 1 - θ := by linarith [hθ.2]
  have hθ2 : 1 - θ ≤ 1 := by linarith [hθ.1]
  have hcL : h * (1 - θ) * Lf ≤ 1 / 2 := by
    have : h * (1 - θ) * Lf ≤ h * Lf := by
      have := mul_le_mul_of_nonneg_left hθ2 (le_of_lt (mul_pos hpos hLf0))
      nlinarith
    linarith
  have hcρ : h * (1 - θ) * ρf ≤ 1 / 2 := by
    have : h * (1 - θ) * ρf ≤ h * ρf := by
      have := mul_le_mul_of_nonneg_left hθ2 (le_of_lt (mul_pos hpos hρf0))
      nlinarith
    linarith
  have hcL0 : 0 ≤ h * (1 - θ) * Lf := by positivity
  -- Lipschitz estimate of the implicit term
  have hfl : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖f t (θ • xref + (1 - θ) • x) - f t (θ • xref + (1 - θ) • y)‖ ≤ Lf * (1 - θ) * ‖x - y‖ := by
    intro x y
    have := hLf t ht t ht (θ • xref + (1 - θ) • x) (θ • xref + (1 - θ) • y)
    have e : (θ • xref + (1 - θ) • x) - (θ • xref + (1 - θ) • y) = (1 - θ) • (x - y) := by
      rw [smul_sub]; abel
    rw [e, sub_self, abs_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ1] at this
    linarith
  have hBop : ∀ v : EuclideanSpace ℝ (Fin m), ‖B tref xref v‖ ≤ σB * ‖v‖ := fun v =>
    le_trans ((B tref xref).le_opNorm v) (mul_le_mul_of_nonneg_right (hσB tref htref xref)
      (norm_nonneg v))
  refine ⟨fun u => ?_, fun u u' x x' hx hx' => ?_, fun u x hx => ?_⟩
  · -- existence by Banach, uniqueness by the contraction estimate
    let Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x =>
      xref + h • (f t (θ • xref + (1 - θ) • x) + B tref xref u)
    have hΦ : ∀ x y, dist (Φ x) (Φ y) ≤ (1 / 2 : ℝ) * dist x y := by
      intro x y
      rw [dist_eq_norm, dist_eq_norm]
      have e : Φ x - Φ y = h • (f t (θ • xref + (1 - θ) • x) - f t (θ • xref + (1 - θ) • y)) := by
        simp only [Φ, smul_add, smul_sub]; abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
      have := hfl x y
      calc h * ‖f t (θ • xref + (1 - θ) • x) - f t (θ • xref + (1 - θ) • y)‖
          ≤ h * (Lf * (1 - θ) * ‖x - y‖) := mul_le_mul_of_nonneg_left this hpos.le
        _ = h * (1 - θ) * Lf * ‖x - y‖ := by ring
        _ ≤ 1 / 2 * ‖x - y‖ := mul_le_mul_of_nonneg_right hcL (norm_nonneg _)
    have hK : ContractingWith (1 / 2 : NNReal) Φ := by
      refine ⟨by norm_num, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
      have := hΦ x y
      simpa using this
    have hfix := ContractingWith.fixedPoint_isFixedPt (f := Φ) hK
    refine ⟨ContractingWith.fixedPoint Φ hK, ?_, ?_⟩
    · have : Φ (ContractingWith.fixedPoint Φ hK) = ContractingWith.fixedPoint Φ hK := hfix
      show ContractingWith.fixedPoint Φ hK - xref = _
      rw [sub_eq_iff_eq_add, add_comm]
      exact this.symm
    · intro y hy
      have hy' : Φ y = y := by simp only [Φ]; rw [← hy]; abel
      exact ContractingWith.fixedPoint_unique hK hy'
  · have e : x - x' = h • (f t (θ • xref + (1 - θ) • x) - f t (θ • xref + (1 - θ) • x')) +
        h • B tref xref (u - u') := by
      have : x - x' = (x - xref) - (x' - xref) := by abel
      rw [this, hx, hx', map_sub]
      simp only [smul_add, smul_sub]
      abel
    have hn : ‖x - x'‖ ≤ h * (1 - θ) * Lf * ‖x - x'‖ + h * σB * ‖u - u'‖ := by
      have a1 := mul_le_mul_of_nonneg_left (hfl x x') hpos.le
      have a2 := mul_le_mul_of_nonneg_left (hBop (u - u')) hpos.le
      calc ‖x - x'‖ = ‖h • (f t (θ • xref + (1 - θ) • x) - f t (θ • xref + (1 - θ) • x')) +
            h • B tref xref (u - u')‖ := by rw [e]
        _ ≤ ‖h • (f t (θ • xref + (1 - θ) • x) - f t (θ • xref + (1 - θ) • x'))‖ +
            ‖h • B tref xref (u - u')‖ := norm_add_le _ _
        _ = h * ‖f t (θ • xref + (1 - θ) • x) - f t (θ • xref + (1 - θ) • x')‖ +
            h * ‖B tref xref (u - u')‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
        _ ≤ h * (1 - θ) * Lf * ‖x - x'‖ + h * σB * ‖u - u'‖ := by nlinarith
    have hc : 0 < 1 - h * (1 - θ) * Lf := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  · have h1 := hρf t ht (θ • xref + (1 - θ) • x)
    have h2 : ‖θ • xref + (1 - θ) • x‖ ≤ ‖xref‖ + (1 - θ) * ‖x - xref‖ := by
      have e : θ • xref + (1 - θ) • x = xref + (1 - θ) • (x - xref) := by
        rw [smul_sub, sub_smul, one_smul, sub_smul, one_smul]; abel
      rw [e]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ1]
    have h3 := hBop u
    have h4 : ‖f t (θ • xref + (1 - θ) • x) + B tref xref u‖ ≤
        ρf * (1 + ‖xref‖) + σB * ‖u‖ + (1 - θ) * ρf * ‖x - xref‖ := by
      refine le_trans (norm_add_le _ _) ?_
      nlinarith
    have hn : ‖x - xref‖ ≤ h * (ρf * (1 + ‖xref‖) + σB * ‖u‖) + h * (1 - θ) * ρf * ‖x - xref‖ := by
      calc ‖x - xref‖ = ‖h • (f t (θ • xref + (1 - θ) • x) + B tref xref u)‖ := by rw [hx]
        _ = h * ‖f t (θ • xref + (1 - θ) • x) + B tref xref u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
        _ ≤ h * (ρf * (1 + ‖xref‖) + σB * ‖u‖ + (1 - θ) * ρf * ‖x - xref‖) :=
          mul_le_mul_of_nonneg_left h4 hpos.le
        _ = _ := by ring
    have hc : 0 < 1 - h * (1 - θ) * ρf := by linarith
    rw [le_div_iff₀ hc]
    nlinarith
