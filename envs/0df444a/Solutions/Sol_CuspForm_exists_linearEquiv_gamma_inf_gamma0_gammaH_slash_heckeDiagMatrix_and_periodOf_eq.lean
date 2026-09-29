-- Prove2me | solution 1 for CuspForm.exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3143d675-fd59-5013-ad25-d2b9b85e5551

import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ModularForm

open UpperHalfPlane Complex MeasureTheory Set ModularCurve
open scoped MatrixGroups Topology

namespace W7

theorem exists_ball {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ R r : ℝ, 0 < r ∧ (∀ z : ℂ, ε ≤ z.im → ‖z‖ ≤ C → z ∈ Metric.ball (Complex.I * R) r) ∧
      Metric.ball (Complex.I * (R : ℂ)) r ⊆ {z : ℂ | 0 < z.im} := by
  set R : ℝ := (C ^ 2 + ε ^ 2 + 1) / ε with hR
  have hRε : R * ε = C ^ 2 + ε ^ 2 + 1 := by rw [hR]; field_simp
  have hRgt : ε < R := by
    rw [hR, lt_div_iff₀ hε]; nlinarith
  have key : ∀ z : ℂ, ‖z - Complex.I * R‖ ^ 2 = z.re ^ 2 + (z.im - R) ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, mul_re, Complex.I_re, ofReal_re, zero_mul, Complex.I_im, ofReal_im, mul_zero, sub_zero, sub_im,
      mul_im, one_mul, zero_add]
    ring
  refine ⟨R, R - ε / 2, by linarith, ?_, ?_⟩
  · intro z hzim hzC
    rw [Metric.mem_ball, dist_eq_norm]
    have hnn : 0 ≤ R - ε / 2 := by linarith
    rw [← abs_of_nonneg (norm_nonneg (z - Complex.I * R)), ← abs_of_nonneg hnn, ← sq_lt_sq, key]
    have hz2 : z.re ^ 2 + z.im ^ 2 ≤ C ^ 2 := by
      have h1 : ‖z‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzC 2
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      nlinarith
    nlinarith
  · intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have him : |(z - Complex.I * R).im| ≤ ‖z - Complex.I * R‖ := Complex.abs_im_le_norm _
    simp only [sub_im, mul_im, Complex.I_re, ofReal_im, mul_zero, Complex.I_im, ofReal_re, one_mul, zero_add] at him
    have := (abs_le.mp (him.trans hz.le)).1
    show 0 < z.im
    linarith

theorem integral_segment_eq_sub {B : Set ℂ} (hB : Convex ℝ B) {Φ g : ℂ → ℂ}
    (hΦ : ∀ z ∈ B, HasDerivAt Φ (g z) z) (hg : ContinuousOn g B) {z₀ z₁ : ℂ} (h0 : z₀ ∈ B) (h1 : z₁ ∈ B) :
    ∫ t in (0 : ℝ)..1, g (z₀ + t * (z₁ - z₀)) * (z₁ - z₀) = Φ z₁ - Φ z₀ := by
  set p : ℝ → ℂ := fun t => z₀ + t * (z₁ - z₀) with hp
  have hp_mem : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ B := fun t ht => by
    have := hB.add_smul_sub_mem h0 h1 ht
    simpa [hp, Complex.real_smul] using this
  have hp_deriv : ∀ t : ℝ, HasDerivAt p (z₁ - z₀) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    simpa [hp] using (h1.mul_const (z₁ - z₀)).const_add z₀
  have hp_cont : Continuous p :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (Φ ∘ p) (g (p t) * (z₁ - z₀)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact (hΦ (p t) (hp_mem t ht)).comp t (hp_deriv t)
  have hint : IntervalIntegrable (fun t => g (p t) * (z₁ - z₀)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (hg.comp hp_cont.continuousOn hp_mem).mul continuousOn_const
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [hp] using this

theorem segmentPoint_eq (τ₀ τ₁ : ℍ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    segmentPoint τ₀ τ₁ t = (τ₀ : ℂ) + t * ((τ₁ : ℂ) - τ₀) := by
  rw [segmentPoint, clamp01_of_mem ht]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem periodAlongOf_eq_integral {Γ : Subgroup SL(2, ℤ)} (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) :
    periodAlongOf Γ τ₀ τ₁ f
      = ∫ t in (0 : ℝ)..1, (⇑f ∘ ofComplex) ((τ₀ : ℂ) + t * ((τ₁ : ℂ) - τ₀)) * ((τ₁ : ℂ) - τ₀) := by
  rw [periodAlongOf_apply]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Function.comp_apply]
  rw [← segmentPoint_eq τ₀ τ₁ ht, ← coe_segmentPath, ofComplex_apply]

theorem periodAlongOf_eq_sub {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) {B : Set ℂ} (hB : Convex ℝ B)
    {Φ : ℂ → ℂ} (hΦ : ∀ z ∈ B, HasDerivAt Φ ((⇑f ∘ ofComplex) z) z) (hcont : ContinuousOn (⇑f ∘ ofComplex) B)
    {τ₀ τ₁ : ℍ} (h0 : (τ₀ : ℂ) ∈ B) (h1 : (τ₁ : ℂ) ∈ B) :
    periodAlongOf Γ τ₀ τ₁ f = Φ τ₁ - Φ τ₀ := by
  rw [periodAlongOf_eq_integral, integral_segment_eq_sub hB hΦ hcont h0 h1]

theorem periodAlongOf_smul_eq_periodOf (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ : Γ) (τ₀ : ℍ)
    (f : CuspForm Γ 2) :
    periodAlongOf Γ τ₀ ((γ : SL(2, ℤ)) • τ₀) f = periodOf Γ γ f := by
  have hg_diff : DifferentiableOn ℂ (⇑f ∘ ofComplex) {z : ℂ | 0 < z.im} := mdifferentiable_iff.mp f.holo'

  set τ₁ : ℍ := (γ : SL(2, ℤ)) • τ₀ with hτ₁
  set ε : ℝ := min UpperHalfPlane.I.im (min τ₀.im τ₁.im) with hε
  set C : ℝ := max ‖((UpperHalfPlane.I : ℍ) : ℂ)‖ (max ‖(τ₀ : ℂ)‖ ‖(τ₁ : ℂ)‖) with hC
  have hεpos : 0 < ε := lt_min (UpperHalfPlane.im_pos _) (lt_min τ₀.im_pos τ₁.im_pos)
  obtain ⟨R, r, -, hball, hballH⟩ := exists_ball hεpos ((norm_nonneg _).trans (le_max_left _ _) : (0 : ℝ) ≤ C)
  set B := Metric.ball (Complex.I * (R : ℂ)) r with hB
  have hI : ((UpperHalfPlane.I : ℍ) : ℂ) ∈ B := hball _ (min_le_left _ _) (le_max_left _ _)
  have h0 : (τ₀ : ℂ) ∈ B :=
    hball _ ((min_le_right _ _).trans (min_le_left _ _)) ((le_max_left _ _).trans (le_max_right _ _))
  have h1 : (τ₁ : ℂ) ∈ B :=
    hball _ ((min_le_right _ _).trans (min_le_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))

  have hdiffB : DifferentiableOn ℂ (⇑f ∘ ofComplex) B := hg_diff.mono hballH
  obtain ⟨Φ, hΦ⟩ := hdiffB.isExactOn_ball
  have hcont : ContinuousOn (⇑f ∘ ofComplex) B := hdiffB.continuousOn
  have hconv : Convex ℝ B := convex_ball _ _

  have e1 := periodAlongOf_eq_sub f hconv hΦ hcont h0 h1
  have e2 := periodAlongOf_eq_sub f hconv hΦ hcont hI h1
  have e3 := periodAlongOf_eq_sub f hconv hΦ hcont hI h0
  have key := LinearMap.congr_fun (periodAlongOf_smul_sub_periodAlongOf_eq_periodOf Γ γ τ₀) f
  rw [LinearMap.sub_apply] at key
  rw [← key, e1, e2, e3]
  ring

end W7

namespace E3c

open CongruenceSubgroup CohCarrier

section Groups

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

abbrev Hker : Subgroup (ZMod (q ^ 2 * M'))ˣ :=
  (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker

def Rel (γ γ' : SL(2, ℤ)) : Prop :=
  γ 0 0 = γ' 0 0 ∧ γ 0 1 = q * γ' 0 1 ∧ (q : ℤ) * γ 1 0 = γ' 1 0 ∧ γ 1 1 = γ' 1 1

variable {q M'}

theorem hqdvd : q ∣ q ^ 2 * M' := dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M'

theorem mem_Hker_iff (u : (ZMod (q ^ 2 * M'))ˣ) :
    u ∈ Hker q M' ↔ (ZMod.castHom (hqdvd (q := q) (M' := M')) (ZMod q) (u : ZMod (q ^ 2 * M'))) = 1 := by
  rw [MonoidHom.mem_ker, ZMod.unitsMap_def, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe, Units.val_one]

theorem mem_GammaH_Hker_iff (A : SL(2, ℤ)) :
    A ∈ GammaH (q ^ 2 * M') (Hker q M') ↔
      ((q ^ 2 * M' : ℕ) : ℤ) ∣ A 1 0 ∧ ((A 1 1 : ℤ) : ZMod q) = 1 := by
  rw [mem_GammaH_iff]
  constructor
  · rintro ⟨hA, hH⟩
    refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hA), ?_⟩
    rw [mem_Hker_iff] at hH
    rw [val_gamma0Units] at hH
    change ZMod.castHom hqdvd (ZMod q) (((A 1 1 : ℤ) : ZMod (q ^ 2 * M'))) = 1 at hH
    rwa [map_intCast] at hH
  · rintro ⟨hc, hd⟩
    refine ⟨Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc), ?_⟩
    rw [mem_Hker_iff, val_gamma0Units]
    change ZMod.castHom hqdvd (ZMod q) (((A 1 1 : ℤ) : ZMod (q ^ 2 * M'))) = 1
    rwa [map_intCast]

theorem mem_Gamma_inf_Gamma0_iff (A : SL(2, ℤ)) :
    A ∈ (Gamma q ⊓ Gamma0 M' : Subgroup SL(2, ℤ)) ↔
      (((A 0 0 : ℤ) : ZMod q) = 1 ∧ ((A 0 1 : ℤ) : ZMod q) = 0 ∧ ((A 1 0 : ℤ) : ZMod q) = 0 ∧
        ((A 1 1 : ℤ) : ZMod q) = 1) ∧ ((M' : ℤ) ∣ A 1 0) := by
  rw [Subgroup.mem_inf, Gamma_mem, Gamma0_mem]
  exact and_congr Iff.rfl (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem isCoprime_q_M' : IsCoprime (q : ℤ) (M' : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM'

theorem exists_rel_of_mem_inf (γ : SL(2, ℤ)) (hγ : γ ∈ (Gamma q ⊓ Gamma0 M' : Subgroup SL(2, ℤ))) :
    ∃ γ' : SL(2, ℤ), γ' ∈ GammaH (q ^ 2 * M') (Hker q M') ∧ Rel q γ γ' := by
  obtain ⟨⟨ha, hb, hc, hd⟩, hM⟩ := (mem_Gamma_inf_Gamma0_iff γ).mp hγ
  have hbq : (q : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  have hcq : (q : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  refine ⟨conjUpperMat q γ hbq, ?_, ?_⟩
  · rw [mem_GammaH_Hker_iff]
    refine ⟨?_, ?_⟩
    · rw [conjUpperMat_apply_10]
      have hqM : (q : ℤ) * M' ∣ γ 1 0 := (isCoprime_q_M' hqM').mul_dvd hcq hM
      have : ((q ^ 2 * M' : ℕ) : ℤ) = (q : ℤ) * M' * q := by push_cast; ring
      rw [this]
      exact mul_dvd_mul_right hqM _
    · rw [conjUpperMat_apply_11]; exact hd
  · refine ⟨rfl, ?_, ?_, rfl⟩
    · change γ 0 1 = q * (γ 0 1 / q)
      rw [Int.mul_ediv_cancel' hbq]
    · rw [conjUpperMat_apply_10, mul_comm]

theorem exists_rel_of_mem_GammaH (γ' : SL(2, ℤ)) (hγ' : γ' ∈ GammaH (q ^ 2 * M') (Hker q M')) :
    ∃ γ : SL(2, ℤ), γ ∈ (Gamma q ⊓ Gamma0 M' : Subgroup SL(2, ℤ)) ∧ Rel q γ γ' := by
  obtain ⟨hc, hd⟩ := (mem_GammaH_Hker_iff γ').mp hγ'
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hcq : (q : ℤ) ∣ γ' 1 0 := by
    refine dvd_trans ?_ hc
    exact ⟨q * M', by push_cast; ring⟩

  obtain ⟨t, ht⟩ := hc
  have hdiv : γ' 1 0 / q = q * M' * t := by
    rw [ht]
    have : ((q ^ 2 * M' : ℕ) : ℤ) * t = q * (q * M' * t) := by push_cast; ring
    rw [this, Int.mul_ediv_cancel_left _ hq0]
  refine ⟨conjLowerMat q γ' hcq, ?_, ?_⟩
  · rw [mem_Gamma_inf_Gamma0_iff]
    have h10 : (conjLowerMat q γ' hcq) 1 0 = γ' 1 0 / q := rfl
    have h01 : (conjLowerMat q γ' hcq) 0 1 = γ' 0 1 * q := rfl
    have h00 : (conjLowerMat q γ' hcq) 0 0 = γ' 0 0 := rfl
    have h11 : (conjLowerMat q γ' hcq) 1 1 = γ' 1 1 := rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    ·
      rw [h00]
      have hdet := Matrix.SpecialLinearGroup.det_coe γ'
      rw [Matrix.det_fin_two] at hdet
      have hdet' : ((γ' 0 0 : ℤ) : ZMod q) * ((γ' 1 1 : ℤ) : ZMod q)
          - ((γ' 0 1 : ℤ) : ZMod q) * ((γ' 1 0 : ℤ) : ZMod q) = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
        push_cast at this
        exact this
      rw [hd, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hcq, mul_one, mul_zero, sub_zero] at hdet'
      exact hdet'
    · rw [h01, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact dvd_mul_left _ _
    · rw [h10, hdiv, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨M' * t, by ring⟩
    · rw [h11]; exact hd
    · rw [h10, hdiv]
      exact ⟨q * t, by ring⟩
  · refine ⟨rfl, ?_, ?_, rfl⟩
    · change γ' 0 1 * q = q * γ' 0 1
      rw [mul_comm]
    · change (q : ℤ) * (γ' 1 0 / q) = γ' 1 0
      rw [Int.mul_ediv_cancel' hcq]

end Groups

section Analytic

open ModularForm Matrix.SpecialLinearGroup ConjAct
open scoped Pointwise

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

local notation "Γ₁" => (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ))
local notation "Γ₂" => CohCarrier.GammaH (q ^ 2 * M') (Hker q M')
local notation "δ" => ModularForm.heckeDiagMatrix q

variable {q M'}

theorem hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero

theorem mapGL_mul_delta_eq {γ γ' : SL(2, ℤ)} (h : Rel q γ γ') :
    (mapGL ℝ γ : GL (Fin 2) ℝ) * δ = δ * mapGL ℝ γ' := by
  obtain ⟨h00, h01, h10, h11⟩ := h
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have e00 : ((γ 0 0 : ℤ) : ℝ) = γ' 0 0 := by exact_mod_cast h00
  have e01 : ((γ 0 1 : ℤ) : ℝ) = q * γ' 0 1 := by exact_mod_cast h01
  have e10 : (q : ℝ) * γ 1 0 = γ' 1 0 := by exact_mod_cast h10
  have e11 : ((γ 1 1 : ℤ) : ℝ) = γ' 1 1 := by exact_mod_cast h11
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix hq0]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e11, ← e10] <;> ring

theorem slash_delta_apply (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    (f ∣[(2 : ℤ)] δ) τ = (q : ℂ) * f (δ • τ) := by
  rw [slash_heckeDiagMatrix_apply 2 hq0]; norm_num

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem gammaH_eq_conj :
    ((Γ₂ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = toConjAct (δ)⁻¹ • ((Γ₁ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, toConjAct_smul]
  constructor
  · rintro ⟨γ', hγ', rfl⟩
    obtain ⟨γ, hγ, hrel⟩ := exists_rel_of_mem_GammaH hqM' γ' hγ'
    refine ⟨γ, hγ, ?_⟩
    rw [eq_mul_inv_iff_mul_eq, mapGL_mul_delta_eq hrel]
  · rintro ⟨γ, hγ, hy⟩
    obtain ⟨γ', hγ', hrel⟩ := exists_rel_of_mem_inf hqM' γ hγ
    refine ⟨γ', hγ', ?_⟩
    have h1 : (mapGL ℝ γ : GL (Fin 2) ℝ) * δ = δ * y := by
      rw [hy, inv_mul_cancel_right]
    rw [mapGL_mul_delta_eq hrel] at h1
    exact mul_left_cancel h1

theorem gamma_inf_eq_conj :
    ((Γ₁ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = toConjAct (δ)⁻¹⁻¹ • ((Γ₂ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rw [gammaH_eq_conj hqM', inv_inv, map_inv, smul_inv_smul]

noncomputable def toH (F : CuspForm Γ₁ 2) : CuspForm Γ₂ 2 :=
  CuspForm.mcast rfl (CuspForm.translate F δ) (gammaH_eq_conj hqM')

noncomputable def ofH (G : CuspForm Γ₂ 2) : CuspForm Γ₁ 2 :=
  CuspForm.mcast rfl (CuspForm.translate G (δ)⁻¹) (gamma_inf_eq_conj hqM')

@[scoped simp] theorem coe_toH (F : CuspForm Γ₁ 2) : ⇑(toH hqM' F) = (⇑F) ∣[(2 : ℤ)] δ := rfl
@[scoped simp] theorem coe_ofH (G : CuspForm Γ₂ 2) : ⇑(ofH hqM' G) = (⇑G) ∣[(2 : ℤ)] (δ)⁻¹ := rfl

noncomputable def L : CuspForm Γ₁ 2 ≃ₗ[ℂ] CuspForm Γ₂ 2 where
  toFun := toH hqM'
  invFun := ofH hqM'
  map_add' F G := by
    refine DFunLike.coe_injective ?_
    rw [coe_toH, CuspForm.coe_add, CuspForm.coe_add, coe_toH, coe_toH, SlashAction.add_slash]
  map_smul' c F := by
    refine DFunLike.coe_injective ?_
    funext τ
    simp only [coe_toH, RingHom.id_apply, CuspForm.IsGLPos.smul_apply, slash_delta_apply, smul_eq_mul]
    ring
  left_inv F := by
    refine DFunLike.coe_injective ?_
    rw [coe_ofH, coe_toH, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  right_inv G := by
    refine DFunLike.coe_injective ?_
    rw [coe_toH, coe_ofH, ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

@[scoped simp] theorem coe_L (F : CuspForm Γ₁ 2) : ⇑(L hqM' F) = (⇑F) ∣[(2 : ℤ)] δ := rfl

end Analytic

section Periods

open ModularForm ModularCurve Matrix.SpecialLinearGroup ConjAct UpperHalfPlane
open scoped Pointwise

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

local notation "Γ₁" => (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ))
local notation "Γ₂" => CohCarrier.GammaH (q ^ 2 * M') (Hker q M')
local notation "δ" => ModularForm.heckeDiagMatrix q

variable {q M'}

scoped instance finiteIndex_inf : (Γ₁).FiniteIndex := by
  haveI : NeZero q := ⟨hq0⟩
  infer_instance

theorem coe_delta_smul (τ : ℍ) : ((δ • τ : ℍ) : ℂ) = (q : ℂ) * τ := coe_heckeDiagMatrix_smul hq0 τ

theorem sl_smul_eq_mapGL_smul (g : SL(2, ℤ)) (τ : ℍ) : g • τ = (mapGL ℝ g : GL (Fin 2) ℝ) • τ := rfl

theorem smul_delta_smul {γ γ' : SL(2, ℤ)} (h : Rel q γ γ') (τ : ℍ) :
    γ • (δ • τ) = δ • (γ' • τ) := by
  rw [sl_smul_eq_mapGL_smul, sl_smul_eq_mapGL_smul, ← mul_smul, ← mul_smul, mapGL_mul_delta_eq h]

theorem delta_smul_segmentPath (τ₀ τ₁ : ℍ) (t : ℝ) :
    δ • segmentPath τ₀ τ₁ t = segmentPath (δ • τ₀) (δ • τ₁) t := by
  apply UpperHalfPlane.ext
  rw [coe_delta_smul, coe_segmentPath, coe_segmentPath, segmentPoint, segmentPoint, coe_delta_smul,
    coe_delta_smul]
  simp only [Complex.real_smul]
  ring

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem periodOf_L_eq_periodAlongOf {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Γ₁) (hγ' : γ' ∈ Γ₂) (h : Rel q γ γ')
    (F : CuspForm Γ₁ 2) :
    periodOf Γ₂ ⟨γ', hγ'⟩ (L hqM' F) = periodAlongOf Γ₁ (δ • UpperHalfPlane.I) (γ • (δ • UpperHalfPlane.I)) F := by
  rw [periodOf_apply, periodAlongOf_apply]
  congr 1
  funext t
  change (L hqM' F) (segmentPath UpperHalfPlane.I (γ' • UpperHalfPlane.I) t) * (((γ' • UpperHalfPlane.I : ℍ) : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)) = _
  rw [coe_L, slash_delta_apply, delta_smul_segmentPath, ← smul_delta_smul h, mul_assoc, mul_comm,
    mul_assoc]
  congr 1
  rw [sub_mul, smul_delta_smul h, coe_delta_smul, coe_delta_smul, mul_comm _ (q : ℂ), mul_comm _ (q : ℂ)]

theorem periodOf_L_eq {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Γ₁) (hγ' : γ' ∈ Γ₂) (h : Rel q γ γ') (F : CuspForm Γ₁ 2) :
    periodOf Γ₂ ⟨γ', hγ'⟩ (L hqM' F) = periodOf Γ₁ ⟨γ, hγ⟩ F := by
  rw [periodOf_L_eq_periodAlongOf hqM' hγ hγ' h F]
  exact W7.periodAlongOf_smul_eq_periodOf Γ₁ ⟨γ, hγ⟩ (δ • UpperHalfPlane.I) F

end Periods

theorem main (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    (∀ γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)),
        ∃ γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
          (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ∧
    (∀ γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker),
        ∃ γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
          (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ∧
    ∃ L : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2 ≃ₗ[ℂ]
        CuspForm (CohCarrier.GammaH (q ^ 2 * M')
          (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker) 2,
      (∀ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2,
          ⇑(L F) = (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) ∧
      ∀ (γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)))
        (γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker)),
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 →
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 →
        (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 →
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 →
          ∀ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2,
            ModularCurve.periodOf _ γ' (L F) = ModularCurve.periodOf (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) γ F := by
  refine ⟨fun γ => ?_, fun γ' => ?_, ⟨L hqM', fun F => rfl, fun γ γ' h00 h01 h10 h11 F => ?_⟩⟩
  · obtain ⟨γ', hγ', hrel⟩ := exists_rel_of_mem_inf hqM' γ γ.2
    exact ⟨⟨γ', hγ'⟩, hrel⟩
  · obtain ⟨γ, hγ, hrel⟩ := exists_rel_of_mem_GammaH hqM' γ' γ'.2
    exact ⟨⟨γ, hγ⟩, hrel⟩
  · exact periodOf_L_eq hqM' γ.2 γ'.2 ⟨h00, h01, h10, h11⟩ F

end E3c
p2m_reactivate "P2MW.S_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq.E3c"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    (∀ γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)),
        ∃ γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
          (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ∧
    (∀ γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker),
        ∃ γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
          (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ∧
    ∃ L : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2 ≃ₗ[ℂ]
        CuspForm (CohCarrier.GammaH (q ^ 2 * M')
          (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker) 2,
      (∀ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2,
          ⇑(L F) = (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) ∧
      ∀ (γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)))
        (γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker)),
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 →
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 →
        (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 →
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 →
          ∀ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2,
            ModularCurve.periodOf _ γ' (L F) = ModularCurve.periodOf (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) γ F := by
  exact E3c.main q M' hqM'

end S_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq
end P2MW
export P2MW.S_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq (solution)
