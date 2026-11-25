-- Prove2me | solution 1 for FiniteEnergyPlane.exists_periodic_family_of_transition
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T13:53:53.841976+00:00
-- url     : https://prove2.me/submissions/83d40343-2b16-457e-b21a-640f756e7622

import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_log_eq



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem exists_periodic_family_of_transition_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (l : ℕ) (hl : 1 ≤ l) (L δ η : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hη : 0 < η)
    (U : ℝ × ℂ → E) (hU : ContDiffOn ℝ l U (Set.Ioo (-δ) (L + δ) ×ˢ Set.univ))
    (β c : ℝ → ℝ) (A B : ℝ → ℂ) (hβ : ContDiffOn ℝ l β (ball 0 η))
    (hc : ContDiffOn ℝ l c (ball 0 η)) (hA : ContDiffOn ℝ l A (ball 0 η))
    (hB : ContDiffOn ℝ l B (ball 0 η)) (hβ0 : β 0 = L)
    (hβI : ∀ s ∈ ball (0 : ℝ) η, β s ∈ Set.Ioo (-δ) (L + δ))
    (hβ' : ∀ s ∈ ball (0 : ℝ) η, 0 < deriv β s) (hA0 : ∀ s ∈ ball (0 : ℝ) η, A s ≠ 0)
    (hUβ : ∀ s ∈ ball (0 : ℝ) η, ∀ z,
      U (s, z) = Real.exp (2 * c s) • U (β s, A s * z + B s)) :
    ∃ (W : ℝ × ℂ → E) (κ b : ℝ → ℝ) (a d : ℝ → ℂ), ContDiff ℝ l W ∧
      (∀ θ z, W (θ + 1, z) = W (θ, z)) ∧
      ContDiffOn ℝ l κ (Set.Ioo (-1) 2) ∧ ContDiffOn ℝ l a (Set.Ioo (-1) 2) ∧
      ContDiffOn ℝ l d (Set.Ioo (-1) 2) ∧ κ 0 = 0 ∧ κ 1 = L ∧
      (∀ θ ∈ Set.Ioo (-1 : ℝ) 2, κ θ ∈ Set.Ioo (-δ) (L + δ) ∧ 0 < deriv κ θ ∧ a θ ≠ 0) ∧
      ∀ (n : ℤ) (θ : ℝ), θ - n ∈ Set.Ioo (-1 / 3 : ℝ) 1 → ∀ z,
        W (θ, z) = Real.exp (2 * b (θ - n)) • U (κ (θ - n), a (θ - n) * z + d (θ - n)) := by
  obtain ⟨ρ₁, hρ₁, hρ₁η, f, hf, hfA⟩ := exists_contDiffOn_log_eq hη hA (hA0 0 (mem_ball_self hη))
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), L / 2 < β s :=
    (hβ.continuousOn.continuousAt (ball_mem_nhds 0 hη)) (lt_mem_nhds (by rw [hβ0]; linarith))
  obtain ⟨ρ₂, hρ₂, hs₂⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨σ, hσ, h1, h2, h3, h4⟩ : ∃ σ : ℝ, 0 < σ ∧ 4 * σ ≤ ρ₁ ∧ 4 * σ ≤ ρ₂ ∧ 4 * σ ≤ δ ∧
      4 * σ ≤ L := by
    have m1 := min_le_left (min ρ₁ ρ₂) (min δ L)
    have m2 := min_le_right (min ρ₁ ρ₂) (min δ L)
    have m3 := min_le_left ρ₁ ρ₂
    have m4 := min_le_right ρ₁ ρ₂
    have m5 := min_le_left δ L
    have m6 := min_le_right δ L
    have m7 : 0 < min (min ρ₁ ρ₂) (min δ L) := lt_min (lt_min hρ₁ hρ₂) (lt_min hδ hL)
    exact ⟨min (min ρ₁ ρ₂) (min δ L) / 4, by linarith, by linarith, by linarith, by linarith,
      by linarith⟩
  -- the cutoff and the rescaled parameter
  let φ : ℝ → ℝ := fun θ => Real.smoothTransition (3 * θ - 1)
  have hφ : ContDiff ℝ ∞ φ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hφl : ContDiff ℝ l φ := hφ.of_le (by exact_mod_cast le_top)
  have hφ0 : ∀ θ ≤ 1 / 3, φ θ = 0 := fun θ h =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hφ1 : ∀ θ ≥ 2 / 3, φ θ = 1 := fun θ h =>
    Real.smoothTransition.one_of_one_le (by linarith)
  have hφn : ∀ θ, 0 ≤ φ θ := fun θ => Real.smoothTransition.nonneg _
  have hφl1 : ∀ θ, φ θ ≤ 1 := fun θ => Real.smoothTransition.le_one _
  have hφm : Monotone φ := fun x y h => Real.smoothTransition.monotone (by linarith)
  have hφd : ∀ θ, 0 ≤ deriv φ θ := fun θ => hφm.deriv_nonneg
  let r : ℝ → ℝ := fun θ => σ * (θ - 1)
  have hr : ContDiff ℝ l r := contDiff_const.mul (contDiff_id.sub contDiff_const)
  have hrρ : ∀ ρ, 4 * σ ≤ ρ → ∀ θ ∈ Set.Ioo (-1 : ℝ) 2, r θ ∈ ball (0 : ℝ) ρ := by
    intro ρ hρ θ hθ
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_lt]
    constructor
    · show -ρ < σ * (θ - 1); nlinarith [hθ.1]
    · show σ * (θ - 1) < ρ; nlinarith [hθ.2]
  have hrη := hrρ η (h1.trans hρ₁η)
  let κ : ℝ → ℝ := fun θ => (1 - φ θ) * (σ * θ) + φ θ * β (r θ)
  let b : ℝ → ℝ := fun θ => φ θ * c (r θ)
  let a : ℝ → ℂ := fun θ => Complex.exp ((φ θ : ℂ) * f (r θ))
  let d : ℝ → ℂ := fun θ => (φ θ : ℂ) * B (r θ)
  have hφC : ContDiff ℝ l (fun θ => (φ θ : ℂ)) := Complex.ofRealCLM.contDiff.comp hφl
  have hκ : ContDiffOn ℝ l κ (Set.Ioo (-1) 2) :=
    (((contDiff_const.sub hφl).mul (contDiff_const.mul contDiff_id)).contDiffOn).add
      (hφl.contDiffOn.mul (hβ.comp hr.contDiffOn hrη))
  have hb : ContDiffOn ℝ l b (Set.Ioo (-1) 2) := hφl.contDiffOn.mul (hc.comp hr.contDiffOn hrη)
  have ha : ContDiffOn ℝ l a (Set.Ioo (-1) 2) :=
    (hφC.contDiffOn.mul (hf.comp hr.contDiffOn (hrρ ρ₁ h1))).cexp
  have hd : ContDiffOn ℝ l d (Set.Ioo (-1) 2) := hφC.contDiffOn.mul (hB.comp hr.contDiffOn hrη)
  have hβL : ∀ θ ∈ Set.Ioo (-1 : ℝ) 2, L / 2 < β (r θ) := fun θ hθ => hs₂ _ (hrρ ρ₂ h2 θ hθ)
  have hκI : ∀ θ ∈ Set.Ioo (-1 : ℝ) 2, κ θ ∈ Set.Ioo (-δ) (L + δ) := by
    intro θ hθ
    have hσθ : σ * θ ∈ Set.Ioo (-δ) (L + δ) := ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩
    exact convex_Ioo _ _ hσθ (hβI _ (hrη θ hθ)) (by linarith [hφl1 θ]) (hφn θ) (by ring)
  have hκ' : ∀ θ ∈ Set.Ioo (-1 : ℝ) 2, 0 < deriv κ θ := by
    intro θ hθ
    have e1 : HasDerivAt φ (deriv φ θ) θ := (hφ.differentiable (by simp) θ).hasDerivAt
    have e2 : HasDerivAt r (σ * 1) θ := ((hasDerivAt_id θ).sub_const 1).const_mul σ
    have e3 : HasDerivAt β (deriv β (r θ)) (r θ) :=
      ((hβ.contDiffAt (isOpen_ball.mem_nhds (hrη θ hθ))).differentiableAt
        (by exact_mod_cast (by omega : l ≠ 0))).hasDerivAt
    have e4 : HasDerivAt κ (-deriv φ θ * (σ * θ) + (1 - φ θ) * (σ * 1) +
        (deriv φ θ * β (r θ) + φ θ * (deriv β (r θ) * (σ * 1)))) θ :=
      ((e1.const_sub 1).mul ((hasDerivAt_id θ).const_mul σ)).add (e1.mul (e3.comp θ e2))
    rw [e4.deriv]
    have i1 := hφn θ
    have i2 := hφl1 θ
    have i3 := hφd θ
    have i4 := hβ' _ (hrη θ hθ)
    have i5 : 0 ≤ deriv φ θ * (β (r θ) - σ * θ) :=
      mul_nonneg i3 (by nlinarith [hβL θ hθ, hθ.2])
    have i6 : 0 < (1 - φ θ) * σ + φ θ * (deriv β (r θ) * σ) := by
      rcases i1.eq_or_lt with h | h
      · rw [← h]; linarith
      · have := mul_pos h (mul_pos i4 hσ)
        nlinarith
    nlinarith
  let W0 : ℝ × ℂ → E := fun p => Real.exp (2 * b p.1) • U (κ p.1, a p.1 * p.2 + d p.1)
  have hW0 : ContDiffOn ℝ l W0 (Set.Ioo (-1) 2 ×ˢ Set.univ) := by
    have hm : Set.MapsTo (Prod.fst : ℝ × ℂ → ℝ) (Set.Ioo (-1) 2 ×ˢ Set.univ) (Set.Ioo (-1) 2) :=
      fun p hp => hp.1
    refine ContDiffOn.smul ?_ (hU.comp (((hκ.comp contDiffOn_fst hm).prodMk
      (((ha.comp contDiffOn_fst hm).mul contDiffOn_snd).add (hd.comp contDiffOn_fst hm))))
      (fun p hp => ⟨hκI _ hp.1, trivial⟩))
    exact (contDiffOn_const.mul (hb.comp contDiffOn_fst hm)).exp
  have hper : ∀ θ ∈ Set.Ioo (-1 / 3 : ℝ) 0, ∀ z, W0 (θ + 1, z) = W0 (θ, z) := by
    intro θ hθ z
    have hθ1 : φ (θ + 1) = 1 := hφ1 _ (by linarith [hθ.1])
    have hθ0 : φ θ = 0 := hφ0 _ (by linarith [hθ.2])
    have hrθ : r (θ + 1) = σ * θ := by show σ * (θ + 1 - 1) = _; ring
    have hm1 : σ * θ ∈ ball (0 : ℝ) ρ₁ := by
      rw [← hrθ]; exact hrρ ρ₁ h1 _ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hm := ball_subset_ball hρ₁η hm1
    show Real.exp (2 * (φ (θ + 1) * c (r (θ + 1)))) • U ((1 - φ (θ + 1)) * (σ * (θ + 1)) +
        φ (θ + 1) * β (r (θ + 1)), Complex.exp ((φ (θ + 1) : ℂ) * f (r (θ + 1))) * z +
        (φ (θ + 1) : ℂ) * B (r (θ + 1))) = Real.exp (2 * (φ θ * c (r θ))) •
        U ((1 - φ θ) * (σ * θ) + φ θ * β (r θ), Complex.exp ((φ θ : ℂ) * f (r θ)) * z +
        (φ θ : ℂ) * B (r θ))
    rw [hθ1, hθ0, hrθ]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, sub_self, sub_zero,
      add_zero, zero_add, mul_zero, Real.exp_zero, Complex.exp_zero, one_smul]
    rw [hfA _ hm1]
    exact (hUβ _ hm z).symm
  have hWn : ∀ (n : ℤ) (θ : ℝ), θ - n ∈ Set.Ioo (-1 / 3 : ℝ) 1 → ∀ z,
      W0 (Int.fract θ, z) = W0 (θ - n, z) := by
    intro n θ hθ z
    rcases lt_or_ge (θ - n) 0 with h | h
    · have : Int.fract θ = θ - n + 1 := by
        rw [Int.fract_eq_iff]
        exact ⟨by linarith [hθ.1], by linarith, n - 1, by push_cast; ring⟩
      rw [this, hper _ ⟨hθ.1, h⟩]
    · have : Int.fract θ = θ - n := by
        rw [Int.fract_eq_iff]
        exact ⟨h, hθ.2, n, by ring⟩
      rw [this]
  refine ⟨fun p => W0 (Int.fract p.1, p.2), κ, b, a, d, ?_, ?_, hκ, ha, hd, ?_, ?_,
    fun θ hθ => ⟨hκI θ hθ, hκ' θ hθ, Complex.exp_ne_zero _⟩, hWn⟩
  · rw [contDiff_iff_contDiffAt]
    rintro ⟨θ, z⟩
    have hf1 := Int.fract_nonneg θ
    have hf2 := Int.fract_lt_one θ
    rw [Int.fract] at hf1 hf2
    have h5 : ContDiffAt ℝ l (fun p : ℝ × ℂ => W0 (p.1 - ⌊θ⌋, p.2)) (θ, z) := by
      refine ContDiffAt.comp (θ, z) (g := W0)
        (hW0.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨⟨by show (-1 : ℝ) < θ - ⌊θ⌋; linarith, by show θ - ⌊θ⌋ < (2 : ℝ); linarith⟩, trivial⟩)) ?_
      exact ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffAt
    refine h5.congr_of_eventuallyEq ?_
    have h6 : IsOpen {p : ℝ × ℂ | p.1 - ⌊θ⌋ ∈ Set.Ioo (-1 / 3 : ℝ) 1} :=
      isOpen_Ioo.preimage (continuous_fst.sub continuous_const)
    filter_upwards [h6.mem_nhds (show (θ, z) ∈ {p : ℝ × ℂ | p.1 - ⌊θ⌋ ∈ Set.Ioo (-1 / 3 : ℝ) 1}
      from ⟨by show (-1 / 3 : ℝ) < θ - ⌊θ⌋; linarith, hf2⟩)] with p hp
    exact hWn ⌊θ⌋ p.1 hp p.2
  · intro θ z
    show W0 (Int.fract (θ + 1), z) = W0 (Int.fract θ, z)
    rw [Int.fract_add_one]
  · show (1 - φ 0) * (σ * 0) + φ 0 * β (r 0) = 0
    rw [hφ0 0 (by norm_num)]; ring
  · show (1 - φ 1) * (σ * 1) + φ 1 * β (r 1) = L
    rw [hφ1 1 (by norm_num), show r 1 = 0 from by show σ * (1 - 1) = 0; ring, hβ0]; ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (l : ℕ) (hl : 1 ≤ l) (L δ η : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hη : 0 < η)
    (U : ℝ × ℂ → E) (hU : ContDiffOn ℝ l U (Set.Ioo (-δ) (L + δ) ×ˢ Set.univ))
    (β c : ℝ → ℝ) (A B : ℝ → ℂ) (hβ : ContDiffOn ℝ l β (ball 0 η))
    (hc : ContDiffOn ℝ l c (ball 0 η)) (hA : ContDiffOn ℝ l A (ball 0 η))
    (hB : ContDiffOn ℝ l B (ball 0 η)) (hβ0 : β 0 = L)
    (hβI : ∀ s ∈ ball (0 : ℝ) η, β s ∈ Set.Ioo (-δ) (L + δ))
    (hβ' : ∀ s ∈ ball (0 : ℝ) η, 0 < deriv β s) (hA0 : ∀ s ∈ ball (0 : ℝ) η, A s ≠ 0)
    (hUβ : ∀ s ∈ ball (0 : ℝ) η, ∀ z,
      U (s, z) = Real.exp (2 * c s) • U (β s, A s * z + B s)) :
    ∃ (W : ℝ × ℂ → E) (κ b : ℝ → ℝ) (a d : ℝ → ℂ), ContDiff ℝ l W ∧
      (∀ θ z, W (θ + 1, z) = W (θ, z)) ∧
      ContDiffOn ℝ l κ (Set.Ioo (-1) 2) ∧ ContDiffOn ℝ l a (Set.Ioo (-1) 2) ∧
      ContDiffOn ℝ l d (Set.Ioo (-1) 2) ∧ κ 0 = 0 ∧ κ 1 = L ∧
      (∀ θ ∈ Set.Ioo (-1 : ℝ) 2, κ θ ∈ Set.Ioo (-δ) (L + δ) ∧ 0 < deriv κ θ ∧ a θ ≠ 0) ∧
      ∀ (n : ℤ) (θ : ℝ), θ - n ∈ Set.Ioo (-1 / 3 : ℝ) 1 → ∀ z,
        W (θ, z) = Real.exp (2 * b (θ - n)) • U (κ (θ - n), a (θ - n) * z + d (θ - n)) :=
  exists_periodic_family_of_transition_aux l hl L δ η hL hδ hη U hU β c A B hβ hc hA hB hβ0 hβI hβ' hA0 hUβ
