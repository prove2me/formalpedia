-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.twist_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:55.72968+00:00
-- url     : https://prove2.me/submissions/e145af1f-954a-4628-8cc8-949145271aa5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPage
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwist
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_coprime_of_cls
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_count_a
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_eventually_log_cube
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_final_ineq
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_jacobi_separate
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_lower
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_pow_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_page_across
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_twist_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
set_option maxHeartbeats 1000000
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (hP : PNTAPRelW) (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) (hE : Formalism.ZeroFreeDirichlet.ExcBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ (x X : ℝ) (m₀ a₀ : ℕ),
    x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ → a₀.Coprime m₀ →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    ∃ nstar : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊x ^ 400⌋₊ ^ 2 → s ≠ nstar →
      |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤ x ^ (-3 : ℝ) * ((PPset m₀ a₀ X).card : ℝ) := by
  obtain ⟨x₁, hx₁⟩ := count_a hP hE ε hε
  obtain ⟨c₀, hc₀, hpage⟩ := page_across hZ
  obtain ⟨c₃, A₀, C₀, hc₃, H⟩ := hP
  have H' : ∀ M : ℕ, ∃ e : Option (DirichletCharacter ℂ M × ℝ), ∀ (hM : 0 < M), 8 ∣ M →
      (∀ p : DirichletCharacter ℂ M × ℝ, e = some p → @IsExcPair M ⟨hM.ne'⟩ p.1 p.2) ∧
      ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X → b.Coprime M →
        |(piAP X M b : ℝ) - mainAP e b X| ≤
          A₀ * (Real.exp (-(c₃ * Real.log X / Real.log M)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            mainAP e b X := by
    intro M
    by_cases h : 0 < M ∧ 8 ∣ M
    · obtain ⟨e, he1, _, he3⟩ := @H M ⟨h.1.ne'⟩ h.2
      exact ⟨e, fun _ _ => ⟨he1, he3⟩⟩
    · exact ⟨none, fun hM h8 => absurd ⟨hM, h8⟩ h⟩
  choose E hE using H'
  obtain ⟨x₂, hx₂⟩ := eventually_log_cube (200 + 16 / c₃) (ε / 6) (by positivity) (by positivity)
  set L₀ : ℝ := max (max 2 (8 * (ε / 5 + 5 + Real.log 128) / c₀))
    (max (max (8 * (3 + Real.log (32 * (|A₀| + 1))) / c₃) (Real.log (32 * (|A₀| + 1))))
      (8 * |C₀| * (Real.log 806 + ε / 5 + 1))) with hL₀
  refine ⟨max (max x₁ x₂) (Real.exp L₀), ?_⟩
  intro x X m₀ a₀ hx hm h8 ha hX1 hX2 hX3
  have hxx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxL : Real.exp L₀ ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxL
  have hLL : L₀ ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxL
  have hL1 : 2 ≤ Real.log x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hL2 : 8 * (ε / 5 + 5 + Real.log 128) / c₀ ≤ Real.log x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL
  have hL3 : 8 * (3 + Real.log (32 * (|A₀| + 1))) / c₃ ≤ Real.log x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hLL
  have hL4 : Real.log (32 * (|A₀| + 1)) ≤ Real.log x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hLL
  have hL5 : 8 * |C₀| * (Real.log 806 + ε / 5 + 1) ≤ Real.log x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLL
  have hx1 : 1 ≤ x := by
    have := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at this; linarith
  have hu2 : (200 + 16 / c₃) * Real.log x ^ 3 ≤ Real.log X := (hx₂ x hxx₂).trans hX2
  have hu0 : 0 < Real.log X := by
    have : 0 < (200 + 16 / c₃) * Real.log x ^ 3 := by positivity
    linarith
  rcases le_or_gt X 0 with hXn | hXp
  · refine ⟨0, fun s _ _ _ _ _ _ => ?_⟩
    have : PPset m₀ a₀ X = ∅ := by
      unfold PPset; rw [Nat.floor_of_nonpos hXn]; simp
    simp [this]

  have hm8 : 8 ≤ m₀ := Nat.le_of_dvd hm h8
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog8 : 2 ≤ Real.log 8 := by
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hX4 : 4 ≤ X := by
    have h4 : Real.log 4 ≤ Real.log X := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      have : (8 : ℝ) ≤ Real.log x ^ 3 := by nlinarith
      have : 0 ≤ 16 / c₃ * Real.log x ^ 3 := by positivity
      nlinarith
    exact (Real.log_le_log_iff (by norm_num) hXp).mp h4
  set N := ⌊x ^ 400⌋₊ with hN
  have hx400 : 1 ≤ x ^ 400 := one_le_pow₀ hx1
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx400)
  have hNx : (N : ℝ) ≤ x ^ 400 := Nat.floor_le (by linarith)
  have hlogN : Real.log N ≤ 400 * Real.log x := by
    have := Real.log_le_log (by exact_mod_cast hN1) hNx
    rwa [Real.log_pow] at this
  set Z : ℝ := ((m₀ * N ^ 2 : ℕ) : ℝ) with hZdef
  have hZ3 : 3 ≤ Z := by
    have : 8 ≤ m₀ * N ^ 2 := le_trans hm8 (Nat.le_mul_of_pos_right _ (by positivity))
    simp only [hZdef]; exact_mod_cast (show 3 ≤ m₀ * N ^ 2 by omega)
  have hm0 : (0 : ℝ) < m₀ := by exact_mod_cast hm
  have hℓ : Real.log Z ≤ Real.log m₀ + 800 * Real.log x := by
    simp only [hZdef]; push_cast
    rw [Real.log_mul hm0.ne' (by positivity), Real.log_pow]
    push_cast; linarith
  have hℓm : Real.log m₀ ≤ 4 * Real.exp (ε / 5 * Real.log x) := by
    have hxe : x ^ (ε / 5) = Real.exp (ε / 5 * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0, mul_comm]
    have hLp : 0 < Real.log x ^ 2 := by positivity
    have h := hX1.trans hX3
    rw [hxe] at h
    have : Real.log m₀ / 4 * Real.log x ^ 2 ≤ Real.exp (ε / 5 * Real.log x) * Real.log x ^ 2 := by linarith
    have := le_of_mul_le_mul_right this hLp
    linarith
  have hlogu : Real.log (Real.log X) ≤ (ε / 5 + 2) * Real.log x := by
    have hLp : 0 < Real.log x := by linarith
    calc Real.log (Real.log X) ≤ Real.log (x ^ (ε / 5) * Real.log x ^ 2) := Real.log_le_log hu0 hX3
      _ = ε / 5 * Real.log x + 2 * Real.log (Real.log x) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_pow]; push_cast; ring
      _ ≤ _ := by
          have := Real.log_le_sub_one_of_pos hLp
          nlinarith

  let bad : ℕ → Prop := fun s => 1 < s ∧ Odd s ∧ Squarefree s ∧ s.Coprime m₀ ∧ s ≤ N ^ 2 ∧
      ∃ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), E (m₀ * s) = some (χ, β) ∧ 1 - β < c₀ / Real.log Z ∧
        ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)
  have hMZ : ∀ t, t ≤ N ^ 2 → ((m₀ * t : ℕ) : ℝ) ≤ Z := fun t ht => by
    simp only [hZdef]; exact_mod_cast Nat.mul_le_mul_left m₀ ht
  have huniq : ∀ s₁ s₂, bad s₁ → bad s₂ → s₁ = s₂ := by
    rintro s₁ s₂ ⟨h11, ho1, hq1, hc1, hN1', χ₁, β₁, he1, hlt1, hal1⟩ ⟨h12, ho2, hq2, hc2, hN2', χ₂, β₂, he2, hlt2, hal2⟩
    have hM1 : 0 < m₀ * s₁ := Nat.mul_pos hm (by omega)
    have hM2 : 0 < m₀ * s₂ := Nat.mul_pos hm (by omega)
    have : NeZero (m₀ * s₁) := ⟨hM1.ne'⟩
    have : NeZero (m₀ * s₂) := ⟨hM2.ne'⟩
    obtain ⟨sq1, ne1, L1, _, lt1⟩ := (hE (m₀ * s₁) hM1 (dvd_mul_of_dvd_left h8 _)).1 _ he1
    obtain ⟨sq2, ne2, L2, _, lt2⟩ := (hE (m₀ * s₂) hM2 (dvd_mul_of_dvd_left h8 _)).1 _ he2
    have hag := hpage Z (m₀ * s₁) (m₀ * s₂) χ₁ χ₂ β₁ β₂ hZ3 (hMZ _ hN1') (hMZ _ hN2') sq1 sq2 ne1 ne2 L1 L2
      (by linarith) (by linarith) lt1 lt2
    apply jacobi_separate m₀ s₁ s₂ hm ho1 ho2 hq1 hq2 hc1 hc2
    intro u hu hus
    have hum : u.Coprime m₀ := by
      unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq (show u ≡ 1 [MOD m₀] from hu)]; simp
    have hu1 : u.Coprime s₁ := (Nat.coprime_mul_iff_right.mp hus).1
    have hu2' : u.Coprime s₂ := (Nat.coprime_mul_iff_right.mp hus).2
    have hn : u.Coprime ((m₀ * s₁) * (m₀ * s₂)) :=
      Nat.Coprime.mul_right (Nat.Coprime.mul_right hum hu1) (Nat.Coprime.mul_right hum hu2')
    have := hag u hn
    rw [hal1 u hu hu1, hal2 u hu hu2'] at this
    exact_mod_cast this
  refine ⟨if h : ∃ s, bad s then Classical.choose h else 0, ?_⟩
  intro s h1 hodd hsq hcop hsN hne
  have hnb : ¬ bad s := by
    intro hb
    have hex : ∃ s, bad s := ⟨s, hb⟩
    rw [dif_pos hex] at hne
    exact hne (huniq _ _ hb (Classical.choose_spec hex))
  have hM : 0 < m₀ * s := Nat.mul_pos hm (by omega)
  have h8M : 8 ∣ m₀ * s := dvd_mul_of_dvd_left h8 s
  have : NeZero (m₀ * s) := ⟨hM.ne'⟩
  obtain ⟨hEx, hPNT⟩ := hE (m₀ * s) hM h8M
  have hlm0 : 2 ≤ Real.log ((m₀ * s : ℕ) : ℝ) := by
    have : (8 : ℝ) ≤ ((m₀ * s : ℕ) : ℝ) := by
      exact_mod_cast le_trans hm8 (Nat.le_mul_of_pos_right _ (by omega))
    linarith [Real.log_le_log (by norm_num) this]
  have hlm : Real.log ((m₀ * s : ℕ) : ℝ) ≤ Real.log Z :=
    Real.log_le_log (by exact_mod_cast hM) (hMZ s hsN)
  obtain ⟨f1, f2, f3, f4⟩ := final_ineq ε c₀ c₃ A₀ C₀ (Real.log x) (Real.log X) (Real.log ((m₀ * s : ℕ) : ℝ))
    (Real.log m₀) (Real.log Z) hε hc₀ hc₃ hL1 hL2 hL3 hL4 hL5 hX1 hu2 hlogu hℓm hlm0 hlm hℓ
  set η : ℝ := Real.exp (-(3 * Real.log x)) with hη
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hxη : x ^ (-3 : ℝ) = η := by rw [Real.rpow_def_of_pos hx0, hη]; ring_nf
  set ρ : ℝ := Real.exp (-(c₃ * Real.log X / Real.log ((m₀ * s : ℕ) : ℝ))) +
    Real.exp (-Real.sqrt (c₃ * Real.log X)) with hρ
  have hρ0 : 0 < ρ := by positivity
  set k : ℝ := A₀ * ρ with hk
  have hkabs : |k| = |A₀| * ρ := by rw [hk, abs_mul, abs_of_pos hρ0]
  have hk2 : 2 * |k| ≤ η / 8 := by rw [hkabs, ← mul_assoc]; exact f3
  have hk' : |k| ≤ 1 / 2 := by linarith
  set r : ℝ := 4 * Real.log X * Real.exp (-(c₀ / Real.log Z * Real.log X)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr4 : 4 * r ≤ η / 8 := by
    have : 4 * r = 16 * Real.log X * Real.exp (-(c₀ / Real.log Z * Real.log X)) := by rw [hr]; ring
    rw [this]; exact f2
  have hr' : r ≤ 1 / 2 := by linarith
  have hli : 0 < liX X := lt_of_lt_of_le (by positivity) (liX_lower hX4)
  have hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - mainAP (E (m₀ * s)) b X| ≤
      k * mainAP (E (m₀ * s)) b X :=
    fun b hbB => hPNT X b (by linarith) f1 (coprime_of_cls ha hbB)
  have hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), E (m₀ * s) = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X := by
    intro χ β heq hal
    obtain ⟨_, _, _, hβl, _⟩ := hEx (χ, β) heq
    have hβ2 : β ≤ 1 - c₀ / Real.log Z := by
      by_contra hc
      exact hnb ⟨h1, hodd, hsq, hcop, hsN, χ, β, heq, by linarith, hal⟩
    have hβ1 : 1 / 2 ≤ β := by
      have : 1 / (8 * Real.log ((m₀ * s : ℕ) : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      simp only at hβl
      linarith
    exact liX_pow_le hX4 hβ1 hβ2
  have hmain := twist_one m₀ s a₀ hm h1 hodd hsq hcop.symm ha X r k (E (m₀ * s)) hXp.le hr0 hr' hli hk' hb hG
  have hcount := hx₁ x X m₀ a₀ hxx₁ hm h8 ha hX1 hX2 hX3
  set P : ℝ := ((PPset m₀ a₀ X).card : ℝ)
  set d : ℝ := Real.exp (-(2 / 5 * Real.log X))
  have hsq2 : X ^ (1 / 2 : ℝ) ≤ d * P := by
    have e : X ^ (1 / 2 : ℝ) = X ^ (-(2 / 5) : ℝ) * X ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hXp]; norm_num
    have e2 : X ^ (-(2 / 5) : ℝ) = d := by
      rw [Real.rpow_def_of_pos hXp]; show _ = Real.exp _; congr 1; ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hd0 : 0 ≤ d := (Real.exp_pos _).le
  have ha4 : 4 * r + 2 * |k| ≤ η / 4 := by linarith
  have t1 : (4 * r + 2 * |k|) * (P + X ^ (1 / 2 : ℝ)) ≤ η / 4 * (P + d * P) :=
    mul_le_mul ha4 (by linarith) (add_nonneg hP0 (Real.rpow_nonneg hXp.le _)) (by linarith)
  have t2 : d * P ≤ η / 4 * P := mul_le_mul_of_nonneg_right f4 hP0
  have t3 : η / 4 * (d * P) ≤ η / 4 * (1 / 4 * P) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hP0) (by linarith)
  rw [hxη]
  have : η / 4 * (P + d * P) = η / 4 * P + η / 4 * (d * P) := by ring
  have hηP : 0 ≤ η * P := mul_nonneg hη0 hP0
  have e3 : η / 4 * (1 / 4 * P) = η * P / 16 := by ring
  have e4 : η / 4 * P = η * P / 4 := by ring
  have e5 : (-3 : ℝ) = -3 := rfl
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
