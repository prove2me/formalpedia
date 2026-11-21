-- Prove2me | solution 1 for FiniteEnergyPlane.forall_ne_shiftA_of_forall_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T23:14:53.725786+00:00
-- url     : https://prove2.me/submissions/35354e9c-e5ba-4257-b496-4e9c5a8fd998

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_exists_intersection_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_shiftA
import Theorems.Thm_FiniteEnergyPlane_forall_isolated_of_isBounded_of_isClosed



/-!
# No intersections with translates beyond an exceptional level

`A τ = {(z, w) | u z = (τ · v) w}`. For `τ > τ₀` the set `A τ` is compact (far bound), so its
points are isolated; the set of `τ > τ₀` with `A τ ≠ ∅` is bounded and contains its supremum,
and persistence of isolated intersections gives intersections just above it.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem rdg_fderiv_shiftA_inj {n : ℕ} (u : ℂ → V n) (hu : ContDiff ℝ ∞ u) (c : ℝ) (z : ℂ)
    (h : Function.Injective (fderiv ℝ u z)) : Function.Injective (fderiv ℝ (shiftA c u) z) := by
  have e : shiftA c u = Real.exp (2 * c) • u := rfl
  rw [e, fderiv_const_smul (hu.differentiable (by simp) z)]
  intro a b hab
  simp only [ContinuousLinearMap.smul_apply] at hab
  exact h ((smul_right_injective _ (Real.exp_pos _).ne') hab)

theorem rdg_shiftA_zero {n : ℕ} (u : ℂ → V n) : shiftA 0 u = u := by
  funext z; simp [shiftA]

theorem forall_ne_shiftA_of_forall_norm_lt_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (hv : IsFastPlane H J v)
    (hui : ∀ z, Function.Injective (fderiv ℝ u z)) (hvi : ∀ w, Function.Injective (fderiv ℝ v w))
    (τ₀ : ℝ)
    (hF : ∀ ε > 0, ∃ R : ℝ, ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ v w → ε ≤ |τ - τ₀| →
      ‖z‖ < R ∧ ‖w‖ < R) :
    ∀ τ > τ₀, ∀ z w : ℂ, u z ≠ shiftA τ v w := by
  have hfu := hu.1
  have hfv := hv.1
  have hsu : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfu.1
  have hsv : ContDiff ℝ ∞ v := contDiffOn_univ.1 hfv.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfu.2.1 z trivial
  have hv0 : ∀ z, v z ≠ 0 := fun z => hfv.2.1 z trivial
  have hcu : Continuous u := hsu.continuous
  have hcv : Continuous v := hsv.continuous
  have hsh : ∀ c, IsFiniteEnergyCurve H J Set.univ (shiftA c v) := fun c =>
    (isFastPlane_shiftA H hH J hJ v hv c).1
  have hshi : ∀ c w, Function.Injective (fderiv ℝ (shiftA c v) w) := fun c w =>
    rdg_fderiv_shiftA_inj v hsv c w (hvi w)
  set A : ℝ → Set (ℂ × ℂ) := fun τ => {p : ℂ × ℂ | u p.1 = shiftA τ v p.2} with hA
  have hAcl : ∀ τ, IsClosed (A τ) := fun τ =>
    isClosed_eq (hcu.comp continuous_fst) ((hcv.const_smul (Real.exp (2 * τ))).comp continuous_snd)
  have hAb : ∀ ε > 0, ∃ R : ℝ, ∀ τ, τ₀ + ε ≤ τ → ∀ p ∈ A τ,
      p ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := by
    intro ε hε
    obtain ⟨R, hR⟩ := hF ε hε
    refine ⟨R, fun τ hτ p hp => ?_⟩
    have h := hR τ p.1 p.2 hp (by rw [abs_of_nonneg (by linarith)]; linarith)
    exact ⟨mem_closedBall_zero_iff.2 h.1.le, mem_closedBall_zero_iff.2 h.2.le⟩
  have hiso : ∀ τ > τ₀, ∀ p ∈ A τ, ∃ ε > 0, ∀ z ∈ ball p.1 ε, ∀ w ∈ ball p.2 ε,
      u z = shiftA τ v w → z = p.1 ∧ w = p.2 := by
    intro τ hτ p hp
    obtain ⟨R, hR⟩ := hAb (τ - τ₀) (by linarith)
    have hset : {q : ℂ × ℂ | q ∈ (Set.univ : Set (ℂ × ℂ)) ∧ u q.1 = shiftA τ v q.2} = A τ := by
      ext q; simp [hA]
    have hKc : IsCompact (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :=
      (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    exact forall_isolated_of_isBounded_of_isClosed H hH J hJ u (shiftA τ v) hfu (hsh τ) hui
      (hshi τ) Set.univ isOpen_univ (hset ▸ hAcl τ)
      (hset ▸ hKc.isBounded.subset (fun q hq => hR τ (by linarith) q hq)) p trivial hp
  have hpers : ∀ σ : ℝ, ∀ p ∈ A σ, (∃ ε > 0, ∀ z ∈ ball p.1 ε, ∀ w ∈ ball p.2 ε,
      u z = shiftA σ v w → z = p.1 ∧ w = p.2) → ∀ c : ℕ → ℝ, Tendsto c atTop (𝓝 σ) →
      ∀ᶠ k in atTop, (A (c k)).Nonempty := by
    intro σ p hp hisoσ c hc
    have hcu' : JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => shiftA 0 u) (shiftA 0 u)
        Set.univ :=
      tendstoCInftyLocOn_shiftA u hsu (fun _ => 0) 0 tendsto_const_nhds Set.univ
    rw [rdg_shiftA_zero] at hcu'
    have hcv' := tendstoCInftyLocOn_shiftA v hsv c σ hc Set.univ
    obtain ⟨z, w, -, -, hev⟩ := exists_intersection_of_tendstoCInftyLocOn H hH J hJ Set.univ
      Set.univ isOpen_univ isOpen_univ u (shiftA σ v) (fun _ => u) (fun k => shiftA (c k) v)
      hfu (hsh σ) (fun z _ => hui z) (fun w _ => hshi σ w) (fun _ => hfu) (fun k => hsh (c k))
      hcu' hcv' p.1 p.2 trivial trivial hp hisoσ
    exact hev.mono fun k hk => ⟨(z k, w k), hk⟩
  intro τ₁ hτ₁ z₁ w₁ h₁
  set S : Set ℝ := {τ : ℝ | τ₀ < τ ∧ (A τ).Nonempty} with hS
  have hτ₁S : τ₁ ∈ S := ⟨hτ₁, (z₁, w₁), h₁⟩
  obtain ⟨R₁, hR₁⟩ := hAb 1 one_pos
  obtain ⟨Mx, hMx⟩ := (isCompact_closedBall (0 : ℂ) R₁).exists_bound_of_continuousOn
    (f := u) hcu.continuousOn
  obtain ⟨Mi, hMi⟩ := (isCompact_closedBall (0 : ℂ) R₁).exists_bound_of_continuousOn
    (f := fun z => ‖v z‖⁻¹)
    ((hcv.norm.inv₀ (fun z => norm_ne_zero_iff.2 (hv0 z))).continuousOn)
  have hbdd : BddAbove S := by
    refine ⟨max (τ₀ + 1) (Mx * Mi), fun τ hτ => ?_⟩
    obtain ⟨-, q, hq⟩ := hτ
    by_cases hτ1 : τ₀ + 1 ≤ τ
    · have hqK := hR₁ τ hτ1 q hq
      have hq' : u q.1 = Real.exp (2 * τ) • v q.2 := hq
      have n1 : ‖u q.1‖ = Real.exp (2 * τ) * ‖v q.2‖ := by
        rw [hq', norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      have b1 := hMx q.1 hqK.1
      have b2 := hMi q.2 hqK.2
      rw [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))] at b2
      have hpos2 : 0 < ‖v q.2‖ := norm_pos_iff.2 (hv0 _)
      have e3 : Real.exp (2 * τ) = ‖u q.1‖ * ‖v q.2‖⁻¹ := by
        rw [n1]; field_simp
      have h4 : Real.exp (2 * τ) ≤ Mx * Mi := by
        rw [e3]
        exact mul_le_mul b1 b2 (inv_nonneg.2 (norm_nonneg _)) ((norm_nonneg _).trans b1)
      have := Real.add_one_le_exp (2 * τ)
      have := Real.exp_pos (2 * τ)
      exact le_trans (by linarith) (le_max_right _ _)
    · push_neg at hτ1
      exact le_trans hτ1.le (le_max_left _ _)
  obtain ⟨t, htm, ht, htS⟩ := exists_seq_tendsto_sSup ⟨τ₁, hτ₁S⟩ hbdd
  set σ := sSup S with hσ
  have ht0 : τ₀ < t 0 := (htS 0).1
  have hσpos : τ₀ < σ := lt_of_lt_of_le hτ₁ (le_csSup hbdd hτ₁S)
  obtain ⟨R, hR⟩ := hAb (t 0 - τ₀) (by linarith)
  set KK : Set (ℂ × ℂ) := closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R with hKK
  have hKc : IsCompact KK := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  choose q hq using fun n => (htS n).2
  have hqK : ∀ n, q n ∈ KK := fun n => hR (t n) (by linarith [htm (Nat.zero_le n)]) (q n) (hq n)
  obtain ⟨p, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq hqK
  have hpA : p ∈ A σ := by
    have h1 : Tendsto (fun n => u (q (φ n)).1) atTop (𝓝 (u p.1)) :=
      (hcu.tendsto _).comp ((continuous_fst.tendsto _).comp hlim)
    have h2 : Tendsto (fun n => Real.exp (2 * t (φ n)) • v (q (φ n)).2) atTop
        (𝓝 (Real.exp (2 * σ) • v p.2)) :=
      ((Real.continuous_exp.tendsto _).comp
        (tendsto_const_nhds.mul (ht.comp hφ.tendsto_atTop))).smul
        ((hcv.tendsto _).comp ((continuous_snd.tendsto _).comp hlim))
    exact tendsto_nhds_unique h1 (Tendsto.congr (fun n => (hq (φ n)).symm) h2)
  have hev := hpers σ p hpA (hiso σ hσpos p hpA) (fun k : ℕ => σ + 1 / ((k : ℝ) + 1)) (by
    have := (tendsto_const_nhds (x := σ)).add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at this; exact this)
  obtain ⟨k, hk⟩ := hev.exists
  have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hkS : σ + 1 / ((k : ℝ) + 1) ∈ S := ⟨by linarith, hk⟩
  have := le_csSup hbdd hkS
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (hv : IsFastPlane H J v)
    (hui : ∀ z, Function.Injective (fderiv ℝ u z)) (hvi : ∀ w, Function.Injective (fderiv ℝ v w))
    (τ₀ : ℝ)
    (hF : ∀ ε > 0, ∃ R : ℝ, ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ v w → ε ≤ |τ - τ₀| →
      ‖z‖ < R ∧ ‖w‖ < R) :
    ∀ τ > τ₀, ∀ z w : ℂ, u z ≠ shiftA τ v w :=
  FiniteEnergyPlane.forall_ne_shiftA_of_forall_norm_lt_aux H hH J hJ u v hu hv hui hvi τ₀ hF
