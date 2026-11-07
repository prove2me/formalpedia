-- Prove2me | solution 1 for FiniteEnergyPlane.forall_eq_zero_or_forall_ne_zero_of_mul_crOp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T19:32:50.335006+00:00
-- url     : https://prove2.me/submissions/b1efda90-de88-427a-9c45-1afe73db63c9

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_forall_eq_zero_or_forall_ne_zero_of_hasLoopWind_nonpos
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopEigenWind_of_crOp_eq_zero
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind
import Theorems.Thm_JHolomorphic_eq_zero_of_norm_dbar_le_of_eqOn_zero



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem fas_norm_vecToC (a : CauchyRiemannIndex.Vec 1) : ‖vecToC a‖ = ‖a‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
  simp [vecToC, Fintype.sum_sum_type, sq]

theorem fas_norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem fas_exists_cylInf (z : ℂ) (hz : z ≠ 0) : ∃ s t : ℝ, cylInf s t = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  refine ⟨Real.log ‖z‖ / (2 * π), Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [mul_div_cancel₀ _ hpi, Real.exp_log hn, mul_div_cancel₀ _ hpi]
  exact Complex.norm_mul_exp_arg_mul_I z

theorem fas_re_conj_mul_pos (a b : ℂ) (hlt : ‖b - a‖ < ‖a‖) :
    0 < (starRingEnd ℂ a * b).re := by
  have hapos : 0 < ‖a‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have h1 : starRingEnd ℂ a * b = (‖a‖ ^ 2 : ℝ) + starRingEnd ℂ a * (b - a) := by
    rw [mul_sub, Complex.conj_mul']
    push_cast
    ring
  rw [h1, Complex.add_re, Complex.ofReal_re]
  have h2 : -(‖a‖ * ‖b - a‖) ≤ (starRingEnd ℂ a * (b - a)).re := by
    have := Complex.abs_re_le_norm (starRingEnd ℂ a * (b - a))
    rw [norm_mul, Complex.norm_conj] at this
    exact (abs_le.1 this).1
  nlinarith

lemma fas_vecToC_cont : Continuous vecToC := by
  have e : vecToC = fun a : CauchyRiemannIndex.Vec 1 =>
      ((a (Sum.inl 0) : ℝ) : ℂ) + ((a (Sum.inr 0) : ℝ) : ℂ) * Complex.I :=
    funext fun a => Complex.ext (by simp [vecToC]) (by simp [vecToC])
  rw [e]
  have h1 : Continuous fun a : CauchyRiemannIndex.Vec 1 => a (Sum.inl 0) :=
    (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).continuous
  have h2 : Continuous fun a : CauchyRiemannIndex.Vec 1 => a (Sum.inr 0) :=
    (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).continuous
  exact (Complex.continuous_ofReal.comp h1).add
    ((Complex.continuous_ofReal.comp h2).mul continuous_const)

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

/-- The dichotomy for a generalized analytic function whose product with a solution of winding `1`
is a solution of controlled growth. -/
theorem forall_eq_zero_or_forall_ne_zero_of_mul_crOp_eq_zero_aux (Y : ℂ → ℂ) (hY : ContDiff ℝ ∞ Y)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ Y z 1 + Complex.I * fderiv ℝ Y z Complex.I‖ ≤ M * ‖Y z‖)
    (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (hSper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (δ : ℝ)
    (hwinS : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k →
      (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (νe ν : ℝ × ℝ → CauchyRiemannIndex.Vec 1)
    (hνe : ContDiffOn ℝ ∞ νe (Set.Ioi s₁ ×ˢ Set.univ))
    (hν : ContDiffOn ℝ ∞ ν (Set.Ioi s₁ ×ˢ Set.univ))
    (hνep : ∀ s > s₁, ∀ t : ℝ, νe (s, t + 1) = νe (s, t))
    (hνp : ∀ s > s₁, ∀ t : ℝ, ν (s, t + 1) = ν (s, t))
    (heqe : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S νe (s, t) = 0)
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ν (s, t) = 0)
    (B : ℝ) (hB : ∀ s > s₁, ∀ t : ℝ, ‖νe (s, t)‖ ≤ B)
    (s₂ : ℝ) (hw : ∀ s ≥ s₂, HasLoopWind (fun t => vecToC (νe (s, t))) 1)
    (hrel : ∀ s > s₁, ∀ t : ℝ, vecToC (ν (s, t)) = Y (cylInf s t) * vecToC (νe (s, t)))
    (C₀ c₀ : ℝ) (hgrow : ∀ s > s₁, ∀ t : ℝ,
      ‖ν (s, t)‖ ≤ C₀ * Real.exp (δ * s) + c₀ * ‖νe (s, t)‖) :
    (∀ z, Y z = 0) ∨ ∀ z, Y z ≠ 0 := by
  classical
  by_cases hall : ∀ z, Y z = 0
  · exact Or.inl hall
  refine Or.inr ?_
  have hνne : ∀ s ≥ s₂, ∀ t, vecToC (νe (s, t)) ≠ 0 := fun s hs t => (hw s hs).2.2.1 t
  have hopen : ∀ U : Set ℂ, IsOpen U → U.Nonempty → ¬ ∀ z ∈ U, Y z = 0 := by
    intro U hU hne h0
    refine hall (JHolomorphic.eq_zero_of_norm_dbar_le_of_eqOn_zero
      (fun _ => ContinuousLinearMap.mul ℝ ℂ Complex.I) contDiff_const ?_ Y hY ?_ U hU hne h0)
    · intro _
      ext v
      simp [← mul_assoc]
    · intro z₀
      obtain ⟨ρ, hρ, M, hb⟩ := hM z₀
      exact ⟨ρ, hρ, M, fun z hz => by simpa using hb z hz⟩
  -- the growth of `νe`
  have hne0 : ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, νe (s, t) ≠ 0 := by
    intro s₀
    refine ⟨max s₀ s₂, le_max_left _ _, 0, fun h0 => ?_⟩
    apply hνne _ (le_max_right _ _) 0
    rw [h0]
    apply Complex.ext <;> simp [vecToC]
  obtain ⟨μ₀, k₀, s₃, E, -, hk₀, hE0, hend⟩ := exists_hasLoopEigenWind_of_crOp_eq_zero s₁ S hS Sinf hSinf hSinf' d hd hSas νe hνe
    (fun s hs t => ⟨hSper s hs t, hνep s hs t⟩) heqe hne0 B 0
    (fun s hs t => by simpa using hB s hs t)
  have hk₀1 : k₀ = 1 := by
    have h1 := (hend (max s₃ s₂) (le_max_left _ _)).1
    exact hasLoopWind_unique h1 (hw _ (le_max_right _ _))
  subst hk₀1
  have hμ₀ : μ₀ < δ := by
    rcases hwinS μ₀ 1 hk₀ with h | h
    · exact h.1
    · omega
  set s₄ := max (max s₁ s₃) (max s₂ 0) with hs₄
  have hs41 : s₁ ≤ s₄ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hs43 : s₃ ≤ s₄ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hs42 : s₂ ≤ s₄ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hs40 : 0 ≤ s₄ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hνegrow : ∀ s > s₄, ∀ t, ‖νe (s, t)‖ ≤ E * Real.exp (δ * s) := by
    intro s hs t
    have hs3 : s₃ ≤ s := hs43.trans hs.le
    refine ((hend s hs3).2 t).trans (mul_le_mul_of_nonneg_left ?_ hE0)
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hμ₀.le ?_)
    linarith
  have hsub : Set.Ioi s₄ ×ˢ (Set.univ : Set ℝ) ⊆ Set.Ioi s₁ ×ˢ Set.univ := fun q hq =>
    ⟨lt_of_le_of_lt hs41 hq.1, Set.mem_univ _⟩
  have hge : ∀ s > s₄, s₁ < s := fun s hs => lt_of_le_of_lt hs41 hs
  have hne1 : ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, ν (s, t) ≠ 0 := by
    intro s₀
    by_contra hcon
    push_neg at hcon
    set s₅ := max (max s₀ s₄) (s₄ + 1) with hs₅
    refine hopen {z | Real.exp (2 * π * s₅) < ‖z‖} (isOpen_lt continuous_const continuous_norm)
      ?_ ?_
    · refine ⟨((Real.exp (2 * π * s₅) + 1 : ℝ) : ℂ), ?_⟩
      show Real.exp (2 * π * s₅) < ‖((Real.exp (2 * π * s₅) + 1 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · intro z hz
      have hz' : Real.exp (2 * π * s₅) < ‖z‖ := hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hz'
        exact absurd hz' (not_lt.2 (Real.exp_pos _).le)
      obtain ⟨s, t, rfl⟩ := fas_exists_cylInf z hz0
      rw [fas_norm_cylInf] at hz'
      have hss : s₅ < s := by
        have := Real.exp_lt_exp.1 hz'
        have hp := Real.pi_pos
        nlinarith
      have h0s : s₀ ≤ s := by
        have : s₀ ≤ s₅ := le_trans (le_max_left _ _) (le_max_left _ _)
        linarith
      have h4s : s₄ < s := by
        have : s₄ + 1 ≤ s₅ := le_max_right _ _
        linarith
      have h1 := hrel s (hge s h4s) t
      rw [hcon s h0s t] at h1
      have h2 : vecToC (0 : CauchyRiemannIndex.Vec 1) = 0 := by
        apply Complex.ext <;> simp [vecToC]
      rw [h2] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_right (hνne s (hs42.trans h4s.le) t)
  have hgrow2 : ∀ s > s₄, ∀ t, ‖ν (s, t)‖ ≤ (C₀ + |c₀| * E) * Real.exp (δ * s) := by
    intro s hs t
    have h1 := hgrow s (hge s hs) t
    have h2 := hνegrow s hs t
    have h3 : c₀ * ‖νe (s, t)‖ ≤ |c₀| * (E * Real.exp (δ * s)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self c₀) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    calc _ ≤ _ := h1
      _ ≤ C₀ * Real.exp (δ * s) + |c₀| * (E * Real.exp (δ * s)) := by linarith
      _ = _ := by ring
  obtain ⟨μ, k, s₆, E', hμδ, hk, -, hend2⟩ := exists_hasLoopEigenWind_of_crOp_eq_zero s₄ S (fun i j => (hS i j).mono hsub) Sinf hSinf
    hSinf' d hd hSas ν (hν.mono hsub) (fun s hs t => ⟨hSper s (hge s hs) t, hνp s (hge s hs) t⟩)
    (fun s hs t => heq s (hge s hs) t) hne1 _ δ hgrow2
  have hk1 : k ≤ 1 := by
    rcases hwinS μ k hk with h | h
    · exact h.2
    · linarith [h.1]
  set s₇ := max s₆ (s₄ + 1) with hs₇
  have hs76 : s₆ ≤ s₇ := le_max_left _ _
  have hs74 : s₄ < s₇ := by
    have : s₄ + 1 ≤ s₇ := le_max_right _ _
    linarith
  set R := Real.exp (2 * π * s₇) with hRdef
  have hR : 0 < R := Real.exp_pos _
  have hnon : ∀ z, R ≤ ‖z‖ → Y z ≠ 0 := by
    intro z hz h0
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hz
      linarith
    obtain ⟨s, t, rfl⟩ := fas_exists_cylInf z hz0
    rw [fas_norm_cylInf] at hz
    have hss : s₇ ≤ s := by
      have := Real.exp_le_exp.1 hz
      have hp := Real.pi_pos
      nlinarith
    have h1 := hrel s (hge s (lt_of_lt_of_le hs74 hss)) t
    rw [h0, zero_mul] at h1
    exact (hend2 s (hs76.trans hss)).1.2.2.1 t h1
  have hcl : Continuous (ccwLoop R) := by
    unfold ccwLoop
    fun_prop
  have hper : Function.Periodic (ccwLoop R) 1 := by
    intro t
    unfold ccwLoop
    congr 1
    have : (((2 * π * (t + 1) : ℝ) : ℂ) * Complex.I) =
        ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hnormR : ∀ t, ‖ccwLoop R t‖ = R := fun t => by
    have := fas_norm_cylInf s₇ t
    simpa [cylInf, hRdef] using this
  obtain ⟨m, hm⟩ := exists_hasLoopWind (fun t => Y (ccwLoop R t)) (hY.continuous.comp hcl)
    (fun t => by simp only [hper t]) (fun t => hnon _ (hnormR t).ge)
  have hprod := hasLoopWind_mul hm (hw s₇ (hs42.trans hs74.le))
  have hfun : (fun t => Y (ccwLoop R t) * vecToC (νe (s₇, t))) = fun t => vecToC (ν (s₇, t)) :=
    funext fun t => (hrel s₇ (hge s₇ hs74) t).symm
  rw [hfun] at hprod
  have hkm := hasLoopWind_unique hprod (hend2 s₇ hs76).1
  rcases forall_eq_zero_or_forall_ne_zero_of_hasLoopWind_nonpos Y hY hM R hR hnon m (by omega) hm
    with h | h
  · exact absurd h hall
  · exact h

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution (Y : ℂ → ℂ) (hY : ContDiff ℝ ∞ Y)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ Y z 1 + Complex.I * fderiv ℝ Y z Complex.I‖ ≤ M * ‖Y z‖)
    (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (hSper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (δ : ℝ)
    (hwinS : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k →
      (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (νe ν : ℝ × ℝ → CauchyRiemannIndex.Vec 1)
    (hνe : ContDiffOn ℝ ∞ νe (Set.Ioi s₁ ×ˢ Set.univ))
    (hν : ContDiffOn ℝ ∞ ν (Set.Ioi s₁ ×ˢ Set.univ))
    (hνep : ∀ s > s₁, ∀ t : ℝ, νe (s, t + 1) = νe (s, t))
    (hνp : ∀ s > s₁, ∀ t : ℝ, ν (s, t + 1) = ν (s, t))
    (heqe : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S νe (s, t) = 0)
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ν (s, t) = 0)
    (B : ℝ) (hB : ∀ s > s₁, ∀ t : ℝ, ‖νe (s, t)‖ ≤ B)
    (s₂ : ℝ) (hw : ∀ s ≥ s₂, HasLoopWind (fun t => vecToC (νe (s, t))) 1)
    (hrel : ∀ s > s₁, ∀ t : ℝ, vecToC (ν (s, t)) = Y (cylInf s t) * vecToC (νe (s, t)))
    (C₀ c₀ : ℝ) (hgrow : ∀ s > s₁, ∀ t : ℝ,
      ‖ν (s, t)‖ ≤ C₀ * Real.exp (δ * s) + c₀ * ‖νe (s, t)‖) :
    (∀ z, Y z = 0) ∨ ∀ z, Y z ≠ 0 :=
  forall_eq_zero_or_forall_ne_zero_of_mul_crOp_eq_zero_aux Y hY hM s₁ S hS hSper Sinf hSinf hSinf' d hd hSas δ hwinS νe ν hνe hν hνep hνp heqe heq B hB s₂ hw hrel C₀ c₀ hgrow
