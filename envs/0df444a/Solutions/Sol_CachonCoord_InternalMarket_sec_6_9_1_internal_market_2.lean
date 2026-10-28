-- Prove2me | solution 2 for CachonCoord.InternalMarket.sec_6_9_1_internal_market
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:47:51.47838+00:00
-- url     : https://prove2.me/submissions/b689f617-321f-486c-9c56-2d560fac1485

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model
import Theorems.Thm_CachonCoord_InternalMarket_p94_market_allocation

-- carved verbatim out of submission 2f8c2924-f79e-4c15-bcf6-693b47d359dc, lines 488-511

section
open CachonCoord
open CachonCoord.InternalMarket
open MeasureTheory

lemma im_r_pos {η : ℝ} (hη : 1 < η) : 0 < (η - 1) / η := by
  apply div_pos <;> linarith

lemma im_r_sub_one {η : ℝ} (hη : 1 < η) : (η - 1) / η - 1 = -1 / η := by
  field_simp; ring

lemma im_unique_max {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ s f) {x y : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) (hmx : IsMaxOn f s x) (hmy : IsMaxOn f s y) : x = y := by
  by_contra hne
  have h := hf.2 hx hy hne (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num)
    (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  have hmem : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ s :=
    hf.1 hx hy (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have h1 : f ((1/2:ℝ) • x + (1/2:ℝ) • y) ≤ f x := hmx hmem
  have h2 : f y ≤ f x := hmx hy
  have h3 : f x ≤ f y := hmy hx
  simp only [smul_eq_mul] at h h1
  linarith

lemma im_S_pos {η α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) : 0 < α₁ ^ η + α₂ ^ η :=
  add_pos (Real.rpow_pos_of_pos hα₁ _) (Real.rpow_pos_of_pos hα₂ _)

lemma im_one_sub_share {η α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    1 - optShare η α₁ α₂ = α₂ ^ η / (α₁ ^ η + α₂ ^ η) := by
  have := im_S_pos (η := η) hα₁ hα₂
  unfold optShare
  field_simp
  ring

lemma im_pow_term {η a S : ℝ} (hη : 1 < η) (ha : 0 < a) (hS : 0 < S) :
    a * (a ^ η / S) ^ ((η - 1) / η) = a ^ η / S ^ ((η - 1) / η) := by
  rw [Real.div_rpow (Real.rpow_nonneg ha.le _) hS.le, ← Real.rpow_mul ha.le]
  have h1 : η * ((η - 1) / η) = η - 1 := by field_simp
  rw [h1, ← mul_div_assoc]
  congr 1
  rw [show a * a ^ (η - 1) = a ^ (1:ℝ) * a ^ (η - 1) by rw [Real.rpow_one], ← Real.rpow_add ha]
  congr 1; ring

lemma im_coef {η α₁ α₂ : ℝ} (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    α₁ * optShare η α₁ α₂ ^ ((η - 1) / η) + α₂ * (1 - optShare η α₁ α₂) ^ ((η - 1) / η) =
      (α₁ ^ η + α₂ ^ η) ^ (1 / η) := by
  have hS := im_S_pos (η := η) hα₁ hα₂
  rw [im_one_sub_share hα₁ hα₂]
  unfold optShare
  rw [im_pow_term hη hα₁ hS, im_pow_term hη hα₂ hS, ← add_div]
  have : (1 / η) = 1 - (η - 1) / η := by field_simp; ring
  rw [this, Real.rpow_sub hS, Real.rpow_one]

theorem optrev_core (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    optRevenue η α₁ α₂ Q = (α₁ ^ η + α₂ ^ η) ^ (1 / η) * Q ^ ((η - 1) / η) := by
  unfold optRevenue revenue
  rw [im_coef hη hα₁ hα₂]

theorem marginal_core (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 < Q) :
    HasDerivAt (fun Q' => optRevenue η α₁ α₂ Q') (price η α₁ α₂ Q) Q := by
  have h := (Real.hasDerivAt_rpow_const (x := Q) (p := (η - 1) / η) (Or.inl hQ.ne')).const_mul
    ((α₁ ^ η + α₂ ^ η) ^ (1 / η))
  have hf : (fun Q' => optRevenue η α₁ α₂ Q') =
      fun Q' => (α₁ ^ η + α₂ ^ η) ^ (1 / η) * Q' ^ ((η - 1) / η) := by
    funext Q'; exact optrev_core η α₁ α₂ Q' hη hα₁ hα₂
  rw [hf, im_r_sub_one hη] at *
  unfold price
  exact h.congr_deriv (by ring)

end

section
open CachonCoord
open CachonCoord.InternalMarket
open MeasureTheory
open Model
variable {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)

namespace CachonCoord.InternalMarket.Model

lemma im_c_tangent {eo e : ℝ} (heo : 0 < eo) (he : 0 ≤ e) :
    M.c eo + M.c' eo * (e - eo) ≤ M.c e := by
  have hcv := M.c_strictConvex.convexOn
  have hd := M.c_hasDeriv eo heo
  rcases lt_trichotomy e eo with h | h | h
  · have := hcv.slope_le_of_hasDerivAt (show e ∈ Set.Ici (0:ℝ) from he)
      (show eo ∈ Set.Ici (0:ℝ) from heo.le) h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    nlinarith
  · subst h; simp
  · have := hcv.le_slope_of_hasDerivAt (show eo ∈ Set.Ici (0:ℝ) from heo.le)
      (show e ∈ Set.Ici (0:ℝ) from he) h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith

end CachonCoord.InternalMarket.Model

namespace CachonCoord.InternalMarket.Model

lemma im_expOutput (e : ℝ) : M.expOutput e = (∫ ω, M.Y ω ∂M.P) * e := by
  unfold expOutput; exact integral_mul_const e _

end CachonCoord.InternalMarket.Model

namespace CachonCoord.InternalMarket.Model

lemma im_rpow_r_split {η e : ℝ} (hη : 1 < η) (he : 0 < e) :
    e ^ ((η - 1) / η) = e ^ (-1 / η) * e := by
  conv_rhs => rw [show e ^ (-1 / η) * e = e ^ (-1 / η) * e ^ (1:ℝ) by rw [Real.rpow_one]]
  rw [← Real.rpow_add he]
  congr 1; field_simp; ring

end CachonCoord.InternalMarket.Model

namespace CachonCoord.InternalMarket.Model

lemma im_expMarketRevenue (eo : ℝ) (heo : 0 < eo) :
    M.expMarketRevenue eo = (M.η - 1) / M.η * eo ^ ((M.η - 1) / M.η) * M.K := by
  have hη := M.one_lt_η
  unfold expMarketRevenue K
  rw [← integral_const_mul]
  congr 1
  funext ω
  have hY := (M.Y_mem ω).1
  have hQ : 0 ≤ M.Y ω * eo := mul_nonneg hY heo.le
  have key : (M.Y ω * eo) * (M.Y ω * eo) ^ (-1 / M.η) = (M.Y ω * eo) ^ ((M.η - 1) / M.η) := by
    rcases hQ.lt_or_eq with hQ' | hQ'
    · rw [im_rpow_r_split hη hQ']; ring
    · rw [← hQ', Real.zero_rpow (im_r_pos hη).ne']; simp
  unfold price
  calc M.Y ω * eo * ((M.η - 1) / M.η * (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
        (M.Y ω * eo) ^ (-1 / M.η))
      = (M.η - 1) / M.η * (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
        ((M.Y ω * eo) * (M.Y ω * eo) ^ (-1 / M.η)) := by ring
    _ = _ := by rw [key, Real.mul_rpow hY heo.le]; ring

end CachonCoord.InternalMarket.Model

namespace CachonCoord.InternalMarket.Model

theorem eq46_core (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo) :
    M.payRate eo = M.expMarketRevenue eo / M.expOutput eo := by
  rw [M.im_expMarketRevenue eo heo, M.im_expOutput, im_rpow_r_split M.one_lt_η heo]
  unfold payRate
  field_simp

end CachonCoord.InternalMarket.Model

namespace CachonCoord.InternalMarket.Model

theorem zero_profit_core (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo) :
    M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0 := by
  rw [M.im_expMarketRevenue eo heo, M.im_expOutput, im_rpow_r_split M.one_lt_η heo]
  unfold payRate
  field_simp
  ring

end CachonCoord.InternalMarket.Model

namespace CachonCoord.InternalMarket.Model

lemma im_util_eq (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo e : ℝ) :
    M.managerUtility eo e = (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K * e - M.c e := by
  unfold managerUtility payRate
  rw [M.im_expOutput]
  field_simp

end CachonCoord.InternalMarket.Model

namespace CachonCoord.InternalMarket.Model

theorem manager_core (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo)
    (h45 : (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0) :
    (∀ e : ℝ, 0 < e → HasDerivAt (M.managerUtility eo)
      ((M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' e) e) ∧
    IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo ∧
    (∀ e : ℝ, 0 ≤ e → IsMaxOn (M.managerUtility eo) (Set.Ici 0) e → e = eo) ∧
    M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0 := by
  set L := (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K with hL
  have hfun : M.managerUtility eo = fun e => L * e - M.c e := by
    funext e; exact M.im_util_eq hY eo e
  have hmax : IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo := by
    intro e he
    have he' : (0:ℝ) ≤ e := he
    simp only [Set.mem_setOf_eq]
    rw [hfun]
    have hc := M.im_c_tangent heo he'
    have : M.c' eo = L := by linarith
    rw [this] at hc
    simp only
    nlinarith
  have hsc : StrictConcaveOn ℝ (Set.Ici 0) (M.managerUtility eo) := by
    rw [hfun]
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have g2 := M.c_strictConvex.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at g2 ⊢
    nlinarith
  refine ⟨?_, hmax, fun e he hm => im_unique_max hsc he heo.le hm hmax,
    M.zero_profit_core hY eo heo⟩
  intro e he
  rw [hfun]
  exact (((hasDerivAt_id e).const_mul L).sub (M.c_hasDeriv e he)).congr_deriv (by simp)

end CachonCoord.InternalMarket.Model

namespace CachonCoord.InternalMarket.Model

theorem goal_core :
    (∀ α₁ α₂ Q : ℝ, 0 < α₁ → 0 < α₂ → 0 < Q →
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₁ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = optShare M.η α₁ α₂ * Q)) ∧
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₂ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = (1 - optShare M.η α₁ α₂) * Q)) ∧
      (∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ → q₁ + q₂ ≤ Q →
        α₁ * q₁ ^ ((M.η - 1) / M.η) + α₂ * q₂ ^ ((M.η - 1) / M.η) ≤
          α₁ * (optShare M.η α₁ α₂ * Q) ^ ((M.η - 1) / M.η) +
            α₂ * ((1 - optShare M.η α₁ α₂) * Q) ^ ((M.η - 1) / M.η)) ∧
      HasDerivAt (fun Q' => optRevenue M.η α₁ α₂ Q') (price M.η α₁ α₂ Q) Q) ∧
    (Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
        M.Y ω ^ ((M.η - 1) / M.η)) M.P →
      0 < ∫ ω, M.Y ω ∂M.P →
      ∀ eo : ℝ, 0 < eo →
        (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0 →
        IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo ∧
        (∀ e : ℝ, 0 ≤ e → IsMaxOn (M.managerUtility eo) (Set.Ici 0) e → e = eo) ∧
        M.payRate eo = M.expMarketRevenue eo / M.expOutput eo ∧
        M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0) := by
  refine ⟨fun α₁ α₂ Q h1 h2 hQ => ?_, fun _ hY eo heo h45 => ?_⟩
  · obtain ⟨a, b, -, d⟩ := CachonCoord.InternalMarket.p94_market_allocation M.η α₁ α₂ Q M.one_lt_η h1 h2 hQ
    exact ⟨a, b, d, marginal_core M.η α₁ α₂ Q M.one_lt_η h1 h2 hQ⟩
  · obtain ⟨-, b, c, d⟩ := M.manager_core hY eo heo h45
    exact ⟨b, c, M.eq46_core hY eo heo, d⟩

end CachonCoord.InternalMarket.Model

end

section
open CachonCoord.InternalMarket
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) :
    (∀ α₁ α₂ Q : ℝ, 0 < α₁ → 0 < α₂ → 0 < Q →
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₁ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = optShare M.η α₁ α₂ * Q)) ∧
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₂ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = (1 - optShare M.η α₁ α₂) * Q)) ∧
      (∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ → q₁ + q₂ ≤ Q →
        α₁ * q₁ ^ ((M.η - 1) / M.η) + α₂ * q₂ ^ ((M.η - 1) / M.η) ≤
          α₁ * (optShare M.η α₁ α₂ * Q) ^ ((M.η - 1) / M.η) +
            α₂ * ((1 - optShare M.η α₁ α₂) * Q) ^ ((M.η - 1) / M.η)) ∧
      HasDerivAt (fun Q' => optRevenue M.η α₁ α₂ Q') (price M.η α₁ α₂ Q) Q) ∧
    (Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
        M.Y ω ^ ((M.η - 1) / M.η)) M.P →
      0 < ∫ ω, M.Y ω ∂M.P →
      ∀ eo : ℝ, 0 < eo →
        (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0 →
        IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo ∧
        (∀ e : ℝ, 0 ≤ e → IsMaxOn (M.managerUtility eo) (Set.Ici 0) e → e = eo) ∧
        M.payRate eo = M.expMarketRevenue eo / M.expOutput eo ∧
        M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0) := by
  exact Model.goal_core M

end
