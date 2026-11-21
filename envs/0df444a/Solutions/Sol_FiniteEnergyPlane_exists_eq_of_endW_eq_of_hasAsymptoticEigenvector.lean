-- Prove2me | solution 1 for FiniteEnergyPlane.exists_eq_of_endW_eq_of_hasAsymptoticEigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T21:12:55.425598+00:00
-- url     : https://prove2.me/submissions/7b7b4327-6c30-4d36-8884-cf06dcd02517

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_and_norm_sub_le_of_tendstoZeroCInfty
import Theorems.Thm_FiniteEnergyPlane_mul_abs_sub_le_norm_sub_of_exp_smul_eq
import Theorems.Thm_FiniteEnergyPlane_eq_of_proj_add_eq_proj_add
import Theorems.Thm_FiniteEnergyPlane_exists_mul_abs_sub_le_norm_sub_of_isPrime
import Theorems.Thm_FiniteEnergyPlane_isAsymptoticEigen_apply_ne_zero



/-! F helper H3: far-region injectivity. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma pef_cylInf_add_int (s t : ℝ) (k : ℤ) : cylInf s (t + k) = cylInf s t := by
  unfold cylInf ccwLoop
  congr 1
  have : ((2 * π * (t + k) : ℝ) : ℂ) * Complex.I =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + (k : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

set_option maxHeartbeats 1600000 in
/-- Far-far case. -/
theorem exists_eq_of_endW_eq_of_hasAsymptoticEigenvector_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (u : ℂ → V n)
    (huP : IsNondegenerateEnd H u cylInf P 1) (μ : ℝ) (v : ℝ → V n)
    (hv : HasAsymptoticEigenvector H J u cylInf P 1 μ v) :
    ∃ S : ℝ, ∀ s s' t t' : ℝ, S ≤ s → S ≤ s' →
      endW H u cylInf (s, t) = endW H u cylInf (s', t') → cylInf s t = cylInf s' t' := by
  obtain ⟨hvE, hμ1, c, τ, r, s₀, hτ, hr, hrep⟩ := hv
  have hμ : μ < 0 := by linarith
  obtain ⟨d, c₁, b, hb, -, hw⟩ := huP
  have hT := P.T_pos
  have hvc : Continuous v := hvE.1.1.continuous
  have hvper : Function.Periodic v 1 := hvE.1.2.1
  obtain ⟨m, hm, hvm⟩ : ∃ m > 0, ∀ θ, m ≤ ‖v θ‖ := by
    obtain ⟨x₀, -, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
      (Set.nonempty_Icc.2 zero_le_one) (hvc.norm.continuousOn)
    refine ⟨‖v x₀‖, norm_pos_iff.2 (isAsymptoticEigen_apply_ne_zero H hH J hJ P μ v hvE x₀),
      fun θ => ?_⟩
    obtain ⟨y, hy, hfy⟩ := hvper.exists_mem_Ico₀ one_pos θ
    rw [hfy]; exact hmin (Set.Ico_subset_Icc_self hy)
  obtain ⟨Mv, hMv⟩ : ∃ Mv, ∀ θ, ‖v θ‖ ≤ Mv := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hvc.continuousOn
    refine ⟨C, fun θ => ?_⟩
    obtain ⟨y, hy, hfy⟩ := hvper.exists_mem_Ico₀ one_pos θ
    rw [hfy]; exact hC y (Set.Ico_subset_Icc_self hy)
  have hMv0 : 0 ≤ Mv := le_trans (norm_nonneg _) (hMv 0)
  obtain ⟨ε₀, hε₀, ρ₀, hρ₀, htube⟩ := eq_of_proj_add_eq_proj_add H hH P
  obtain ⟨cg, hcg, hgap⟩ := exists_mul_abs_sub_le_norm_sub_of_isPrime H hH P hP
  -- constants
  set K₀ : ℝ := min (-μ * m / 2) P.T with hK₀
  have hK₀pos : 0 < K₀ := lt_min (by nlinarith) hT
  set η : ℝ := min (min (ε₀ / 4) (min 1 (m / 2))) (K₀ / 2) with hη
  have hηpos : 0 < η := lt_min (lt_min (by linarith) (lt_min one_pos (by linarith))) (by linarith)
  have hηε : η ≤ ε₀ / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη1 : η ≤ 1 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hηm : η ≤ m / 2 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hηK : η ≤ K₀ / 2 := min_le_right _ _
  set ηw : ℝ := cg * ε₀ / 4 with hηw
  have hηwpos : 0 < ηw := by positivity
  obtain ⟨s₂, hs₂⟩ := hw ηw hηwpos
  obtain ⟨Sσ, hSσ⟩ := exists_norm_le_and_norm_sub_le_of_tendstoZeroCInfty hτ η hηpos
  obtain ⟨Sr, hSr⟩ := exists_norm_le_and_norm_sub_le_of_tendstoZeroCInfty hr η hηpos
  obtain ⟨Sh, hSh⟩ : ∃ Sh : ℝ, ∀ s ≥ Sh, Real.exp (μ * s) * (Mv + 1) ≤ ρ₀ := by
    have ht : Tendsto (fun s : ℝ => Real.exp (μ * s) * (Mv + 1)) atTop (𝓝 (0 * (Mv + 1))) :=
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hμ)).mul_const _
    rw [zero_mul] at ht
    obtain ⟨Sh, hSh⟩ := eventually_atTop.1 (ht.eventually (ge_mem_nhds hρ₀))
    exact ⟨Sh, hSh⟩
  set S := max (max (max s₀ s₂) (max Sσ Sr)) (max Sh 0) with hS
  have hSs₀ : s₀ ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hSs₂ : s₂ ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hSσle : Sσ ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hSrle : Sr ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hSh' : Sh ≤ S := le_trans (le_max_left _ _) (le_max_right _ _)
  have hS0 : 0 ≤ S := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨S, fun s s' t t' hs hs' hW => ?_⟩
  -- shift t' by an integer
  set k : ℤ := round (t - t') with hk
  set t'' : ℝ := t' + k with ht''
  have htt : |t - t''| ≤ 1 / 2 := by
    rw [ht'', show t - (t' + k) = (t - t') - round (t - t') by rw [hk]; ring]
    exact abs_sub_round _
  have hW'' : endW H u cylInf (s, t) = endW H u cylInf (s', t'') := by
    rw [hW]; simp only [endW, ht'', pef_cylInf_add_int]
  -- C⁰ closeness
  have hclose : ∀ σ ≥ s₂, 0 ≤ σ → ∀ θ : ℝ,
      ‖endW H u cylInf (σ, θ) - P.x (1 * P.T * θ + c₁)‖ ≤ ηw := by
    intro σ hσ hσ0 θ
    have h1 := hs₂ σ hσ θ
    have hexp : 1 ≤ Real.exp (b * σ) := Real.one_le_exp (mul_nonneg hb.le hσ0)
    simp only at h1
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    exact le_trans (le_mul_of_one_le_left (norm_nonneg _) hexp) h1
  have hxx : ‖P.x (1 * P.T * t + c₁) - P.x (1 * P.T * t'' + c₁)‖ ≤ 2 * ηw := by
    have h1 := hclose s (le_trans hSs₂ hs) (le_trans hS0 hs) t
    have h2 := hclose s' (le_trans hSs₂ hs') (le_trans hS0 hs') t''
    rw [hW''] at h1
    calc ‖P.x (1 * P.T * t + c₁) - P.x (1 * P.T * t'' + c₁)‖
        = ‖(endW H u cylInf (s', t'') - P.x (1 * P.T * t'' + c₁)) -
            (endW H u cylInf (s', t'') - P.x (1 * P.T * t + c₁))‖ := by congr 1; abel
      _ ≤ ‖endW H u cylInf (s', t'') - P.x (1 * P.T * t'' + c₁)‖ +
            ‖endW H u cylInf (s', t'') - P.x (1 * P.T * t + c₁)‖ := norm_sub_le _ _
      _ ≤ 2 * ηw := by linarith
  have hTt : P.T * |t - t''| ≤ ε₀ / 2 := by
    have hd : |(1 * P.T * t + c₁) - (1 * P.T * t'' + c₁)| = P.T * |t - t''| := by
      rw [show (1 * P.T * t + c₁) - (1 * P.T * t'' + c₁) = P.T * (t - t'') by ring, abs_mul,
        abs_of_pos hT]
    have hle : |(1 * P.T * t + c₁) - (1 * P.T * t'' + c₁)| ≤ P.T / 2 := by
      rw [hd]; nlinarith
    have := le_trans (hgap _ _ hle) hxx
    rw [hd, hηw] at this
    have : cg * (P.T * |t - t''|) ≤ cg * (ε₀ / 2) := by linarith
    exact le_of_mul_le_mul_left this hcg
  -- tube representation
  obtain ⟨hξ₁, hrep₁⟩ := hrep s (le_trans hSs₀ hs) t
  obtain ⟨hξ₂, hrep₂⟩ := hrep s' (le_trans hSs₀ hs') t''
  set p : ℝ × ℝ := (s, t) with hp
  set p' : ℝ × ℝ := (s', t'') with hp'
  obtain ⟨hσp, -⟩ := hSσ p p' (le_trans hSσle hs) (le_trans hSσle hs')
  obtain ⟨hσp', hσlip⟩ := hSσ p' p (le_trans hSσle hs') (le_trans hSσle hs)
  obtain ⟨hrp, hrlip⟩ := hSr p p' (le_trans hSrle hs) (le_trans hSrle hs')
  obtain ⟨hrp', -⟩ := hSr p' p (le_trans hSrle hs') (le_trans hSrle hs)
  simp only [Real.norm_eq_abs] at hσp hσp' hσlip
  have hττ : |τ p - τ p'| ≤ ε₀ := by
    have e : τ p - τ p' = P.T * (t - t'') + ((τ p - 1 * P.T * p.2 - c) -
        (τ p' - 1 * P.T * p'.2 - c)) := by simp only [hp, hp']; ring
    rw [e]
    calc |P.T * (t - t'') + ((τ p - 1 * P.T * p.2 - c) - (τ p' - 1 * P.T * p'.2 - c))|
        ≤ |P.T * (t - t'')| + (|τ p - 1 * P.T * p.2 - c| + |τ p' - 1 * P.T * p'.2 - c|) :=
          le_trans (abs_add_le _ _) (add_le_add le_rfl (abs_sub _ _))
      _ ≤ ε₀ / 2 + (η + η) := by
          rw [abs_mul, abs_of_pos hT]; exact add_le_add hTt (add_le_add hσp hσp')
      _ ≤ ε₀ := by linarith
  have hhn : ∀ (σ : ℝ) (θ : ℝ) (ρ : V n), Sh ≤ σ → ‖ρ‖ ≤ 1 →
      ‖Real.exp (1 * μ * σ) • (v θ + ρ)‖ ≤ ρ₀ := by
    intro σ θ ρ hσ hρ
    rw [one_mul, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (μ * σ) * ‖v θ + ρ‖ ≤ Real.exp (μ * σ) * (Mv + 1) :=
          mul_le_mul_of_nonneg_left (le_trans (norm_add_le _ _) (add_le_add (hMv θ) hρ))
            (Real.exp_pos _).le
      _ ≤ ρ₀ := hSh σ hσ
  obtain ⟨hτeq, hheq⟩ := htube (τ p) (τ p') _ _ hττ hξ₁ hξ₂
    (hhn s _ _ (le_trans hSh' hs) (le_trans hrp hη1))
    (hhn s' _ _ (le_trans hSh' hs') (le_trans hrp' hη1))
    (by rw [← hrep₁, ← hrep₂]; exact hW'')
  -- contraction
  have ht1 : P.T * |t - t''| ≤ η * ‖p' - p‖ := by
    have e : P.T * (t - t'') = (τ p' - 1 * P.T * p'.2 - c) - (τ p - 1 * P.T * p.2 - c) := by
      simp only [hp, hp']; rw [hτeq]; ring
    have h3 : |P.T * (t - t'')| ≤ η * ‖p' - p‖ := by rw [e]; exact hσlip
    rwa [abs_mul, abs_of_pos hT] at h3
  rw [hτeq] at hheq
  simp only [one_mul] at hheq
  have hs1 := mul_abs_sub_le_norm_sub_of_exp_smul_eq hμ (hvm (τ p' / P.T)) (le_trans hrp hηm) (le_trans hrp' hηm) s s' hheq
  have hs2 : (-μ) * |s - s'| * (m / 2) ≤ η * ‖p' - p‖ := by
    rw [norm_sub_rev] at hrlip; exact le_trans hs1 (by simpa [norm_sub_rev] using hrlip)
  have hnorm : ‖p' - p‖ = max |s - s'| |t - t''| := by
    rw [Prod.norm_def]; simp only [hp, hp', Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    rw [abs_sub_comm s' s, abs_sub_comm t'' t]
  have hK1 : K₀ * |s - s'| ≤ η * ‖p' - p‖ := by
    have : K₀ ≤ -μ * m / 2 := min_le_left _ _
    calc K₀ * |s - s'| ≤ (-μ * m / 2) * |s - s'| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = (-μ) * |s - s'| * (m / 2) := by ring
      _ ≤ _ := hs2
  have hK2 : K₀ * |t - t''| ≤ η * ‖p' - p‖ := by
    have : K₀ ≤ P.T := min_le_right _ _
    exact le_trans (mul_le_mul_of_nonneg_right this (abs_nonneg _)) ht1
  have hmax : K₀ * ‖p' - p‖ ≤ η * ‖p' - p‖ := by
    rw [hnorm, mul_max_of_nonneg _ _ hK₀pos.le]
    rw [← hnorm]
    exact max_le hK1 hK2
  have hzero : ‖p' - p‖ = 0 := by
    have h0 := norm_nonneg (p' - p)
    have h3 : η * ‖p' - p‖ ≤ K₀ / 2 * ‖p' - p‖ := mul_le_mul_of_nonneg_right hηK h0
    by_contra hne
    have hpos : 0 < ‖p' - p‖ := lt_of_le_of_ne h0 (Ne.symm hne)
    have := mul_pos (half_pos hK₀pos) hpos
    linarith
  have hpp : p' = p := sub_eq_zero.1 (norm_eq_zero.1 hzero)
  have hs_eq : s' = s := congrArg Prod.fst hpp
  have ht_eq : t'' = t := congrArg Prod.snd hpp
  rw [← hs_eq, ← ht_eq, ht'', pef_cylInf_add_int]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (u : ℂ → V n)
    (huP : IsNondegenerateEnd H u cylInf P 1) (μ : ℝ) (v : ℝ → V n)
    (hv : HasAsymptoticEigenvector H J u cylInf P 1 μ v) :
    ∃ S : ℝ, ∀ s s' t t' : ℝ, S ≤ s → S ≤ s' →
      endW H u cylInf (s, t) = endW H u cylInf (s', t') → cylInf s t = cylInf s' t' :=
  exists_eq_of_endW_eq_of_hasAsymptoticEigenvector_aux H hH J hJ P hP u huP μ v hv
