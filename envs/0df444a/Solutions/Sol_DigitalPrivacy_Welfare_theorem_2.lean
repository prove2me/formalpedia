-- Prove2me | solution 1 for DigitalPrivacy.Welfare.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:55:39.059582+00:00
-- url     : https://prove2.me/submissions/faa31f8b-742b-48a6-a357-a7f10aac55b2

import Definitions.Def_DigitalPrivacy_Welfare_Setting

open DigitalPrivacy.Welfare
open DigitalPrivacy.Strategy (abar)

private lemma priv_nonneg {β ρ ξ C : ℝ} (hb : β < 1) (hr : 0 ≤ ρ)
    (hx : 0 ≤ ξ) (hC : 0 ≤ C) : 0 ≤ abar β ρ ξ C := by
  have hb' : 0 < 1 - β := sub_pos.mpr hb
  unfold abar
  split_ifs <;> positivity

private lemma priv_rational {β ρ ξ C : ℝ} (hb : β < 1) (hC : 0 < C) :
    abar β ρ ξ C = C * (1 + ρ * ξ) / (C * (1 - β) + ξ ^ 2) := by
  unfold abar
  split_ifs with hx
  · subst ξ
    have hb' : 1 - β ≠ 0 := ne_of_gt (sub_pos.mpr hb)
    field_simp
    ring
  · rfl

private lemma priv_welfare_order (a b α ψ C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (α * (a ^ 2 / 2) + (1 - α) * (a - ψ * C) ≤
      α * (b ^ 2 / 2) + (1 - α) * (b - ψ * C)) ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    have hba : b < a := lt_of_not_ge hab
    have hs : b ^ 2 < a ^ 2 := (sq_lt_sq₀ hb ha).mpr hba
    by_cases heq : α = 1
    · subst α
      nlinarith
    · have ha1 : 0 < 1 - α := sub_pos.mpr (lt_of_le_of_ne hα1 heq)
      have hm := mul_nonneg hα (sub_nonneg.mpr hs.le)
      have hm' := mul_pos ha1 (sub_pos.mpr hba)
      nlinarith
  · intro hab
    have hs : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha hb).mpr hab
    have hm := mul_nonneg hα (sub_nonneg.mpr hs)
    have hm' := mul_nonneg (sub_nonneg.mpr hα1) (sub_nonneg.mpr hab)
    nlinarith

private lemma priv_activity (β ρ ψ P α : ℝ) (h : Standing β ρ ψ P α)
    (ξs Cs ξW CW : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ P ξs Cs)
    (hW : IsSocialOpt β ρ ψ P α ξW CW) :
    abar β ρ ξs Cs ≤ abar β ρ ξW CW := by
  have hp : Pi β ρ ψ P ξW CW ≤ Pi β ρ ψ P ξs Cs := hs.2 ξW CW hW.1
  have hw := hW.2 ξs Cs hs.1
  have hcs : DigitalPrivacy.Strategy.CS β ρ ξs Cs ≤
      DigitalPrivacy.Strategy.CS β ρ ξW CW := by
    apply (mul_le_mul_iff_right₀ h.2.2).mp
    have hm := mul_nonneg (sub_nonneg.mpr h.1.2.2.2.2.2.2.2.2)
      (sub_nonneg.mpr hp)
    dsimp [W] at hw
    nlinarith
  have has := priv_nonneg h.1.2.1 h.1.2.2.1 hs.1.1.1 hs.1.2
  have haw := priv_nonneg h.1.2.1 h.1.2.2.1 hW.1.1.1 hW.1.2
  apply (sq_le_sq₀ has haw).mp
  dsimp [DigitalPrivacy.Strategy.CS] at hcs
  linarith

private lemma priv_fixed (β ρ ψ α : ℝ) (h : PrintedBounds β ρ ψ 0 α) (C : ℝ)
    (hC : 0 ≤ C) (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ ξ' ∈ Set.Icc (0 : ℝ) 1, Pi β ρ ψ 0 ξ' C ≤ Pi β ρ ψ 0 ξ C) ↔
      (∀ ξ' ∈ Set.Icc (0 : ℝ) 1, W β ρ ψ 0 α ξ' C ≤ W β ρ ψ 0 α ξ C) := by
  have ha := priv_nonneg h.2.1 h.2.2.1 hξ.1 hC
  constructor <;> intro hh ξ' hξ'
  · have hb := priv_nonneg h.2.1 h.2.2.1 hξ'.1 hC
    have hc := hh ξ' hξ'
    simp only [Pi, sub_zero, one_mul, zero_mul, add_zero] at hc
    have hab : abar β ρ ξ' C ≤ abar β ρ ξ C := by linarith
    simpa only [W, Pi, DigitalPrivacy.Strategy.CS, sub_zero, one_mul, zero_mul,
      add_zero] using
      (priv_welfare_order _ _ α ψ C hb ha h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2).mpr hab
  · have hb := priv_nonneg h.2.1 h.2.2.1 hξ'.1 hC
    have hc := hh ξ' hξ'
    simp only [W, Pi, DigitalPrivacy.Strategy.CS, sub_zero, one_mul, zero_mul,
      add_zero] at hc
    have hab := (priv_welfare_order _ _ α ψ C hb ha
      h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2).mp hc
    simp only [Pi, sub_zero, one_mul, zero_mul, add_zero]
    linarith

private lemma priv_midpoint (β ρ x y C D : ℝ) (hb : β < 1) (hr : 0 ≤ ρ)
    (hx : 0 ≤ x) (hxy : x < y) (hC : 0 < C) (hD : 0 < D)
    (hy : abar β ρ ((x+y)/2) C ≤ abar β ρ y C)
    (hhx : abar β ρ ((x+y)/2) D ≤ abar β ρ x D) : D < C := by
  have hb' : 0 < 1 - β := sub_pos.mpr hb
  have hcden : ∀ z : ℝ, 0 < C * (1 - β) + z ^ 2 := by
    intro z
    positivity
  have hdden : ∀ z : ℝ, 0 < D * (1 - β) + z ^ 2 := by
    intro z
    positivity
  rw [priv_rational hb hC, priv_rational hb hC] at hy
  rw [priv_rational hb hD, priv_rational hb hD] at hhx
  have hy' := (div_le_div_iff₀ (hcden _) (hcden _)).mp hy
  have hx' := (div_le_div_iff₀ (hdden _) (hdden _)).mp hhx
  have hcm : 0 < C * (y - x) := mul_pos hC (sub_pos.mpr hxy)
  have hdm : 0 < D * (y - x) := mul_pos hD (sub_pos.mpr hxy)
  have hc : (x+y)/2 + y + ρ*((x+y)/2)*y ≤ ρ*C*(1-β) := by
    apply (mul_le_mul_iff_right₀ hcm).mp
    nlinarith only [hy']
  have hd : ρ*D*(1-β) ≤ x + (x+y)/2 + ρ*x*((x+y)/2) := by
    apply (mul_le_mul_iff_right₀ hdm).mp
    nlinarith only [hx']
  have hm : 0 ≤ ρ * ((x+y)/2) * (y-x) :=
    mul_nonneg (mul_nonneg hr (by linarith)) (sub_nonneg.mpr hxy.le)
  have hstrict : ρ*D*(1-β) < ρ*C*(1-β) := by nlinarith
  by_contra hdc
  have hcd : C ≤ D := le_of_not_gt hdc
  have hh := mul_le_mul_of_nonneg_left hcd hr
  have hh' := mul_le_mul_of_nonneg_right hh hb'.le
  linarith

private lemma priv_usage (β ρ ψ α : ℝ) (h : Standing β ρ ψ 0 α) (ξs Cs ξW CW : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ 0 ξs Cs)
    (hW : IsSocialOpt β ρ ψ 0 α ξW CW) (hover : ξW < ξs) : CW < Cs := by
  by_contra hnot
  have hcw : Cs ≤ CW := le_of_not_gt hnot
  have hξs : 0 < ξs := lt_of_le_of_lt hW.1.1.1 hover
  have hb : 0 < 1 - β := sub_pos.mpr h.1.2.1
  have hcs : 0 < Cs := by
    by_contra hc
    have heq : Cs = 0 := le_antisymm (le_of_not_gt hc) hs.1.2
    have h0 := hs.2 0 Cs ⟨⟨le_rfl, zero_le_one⟩, hs.1.2⟩
    simp [DigitalPrivacy.Strategy.profit, abar, heq, ne_of_gt hξs] at h0
    have : 0 < (1 : ℝ) / (1-β) := one_div_pos.mpr hb
    linarith
  have hcw' : 0 < CW := hcs.trans_le hcw
  let m : ℝ := (ξW+ξs)/2
  have hm : m ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [m]
    constructor <;> linarith [hs.1.1.2, hW.1.1.1]
  have hbmid := hs.2 m Cs ⟨hm, hs.1.2⟩
  have hsmid : abar β ρ m Cs ≤ abar β ρ ξs Cs := by
    simpa [DigitalPrivacy.Strategy.profit] using hbmid
  have hsw : ∀ ξ' ∈ Set.Icc (0 : ℝ) 1,
      W β ρ ψ 0 α ξ' CW ≤ W β ρ ψ 0 α ξW CW := by
    intro ξ' hξ'
    exact hW.2 ξ' CW ⟨hξ', hW.1.2⟩
  have hpmid := ((priv_fixed β ρ ψ α h.1 CW hW.1.2 ξW hW.1.1).mpr hsw) m hm
  have hwmid : abar β ρ m CW ≤ abar β ρ ξW CW := by simpa [Pi] using hpmid
  exact (not_lt_of_ge hcw) (priv_midpoint β ρ ξW ξs Cs CW h.1.2.1 h.1.2.2.1
    hW.1.1.1 hover hcs hcw' hsmid hwmid)

private lemma priv_activity_pos (β ρ ψ P α : ℝ) (h : Standing β ρ ψ P α)
    (hP : 0 < P) (ξ C : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ P ξ C) : 0 < abar β ρ ξ C := by
  have hψ := h.2.1
  have hP1 := h.1.2.2.2.2.2.2.1
  have hρ := h.1.2.2.1
  let t := P / (2*(ψ+1))
  have ht : 0 < t := by dsimp [t]; positivity
  have htid : 2*(ψ+1)*t = P := by dsimp [t]; field_simp
  have ht1 : t ≤ 1 := by nlinarith
  have htC : 0 < t^2 := sq_pos_of_pos ht
  have hden : 0 < t^2*(1-β)+t^2 := by
    have hb : 0 < 1-β := sub_pos.mpr h.1.2.1
    positivity
  have hat : (1:ℝ)/2 ≤ abar β ρ t (t^2) := by
    rw [priv_rational h.1.2.1 htC]
    apply (le_div_iff₀ hden).mpr
    have hh := mul_nonneg hρ ht.le
    have hh' := mul_nonneg htC.le hh
    have hb' := mul_nonneg htC.le h.1.1
    nlinarith
  have ha0 : 0 ≤ abar β ρ t (t^2) := le_trans (by norm_num) hat
  have hcost : 0 < P*t/2-ψ*t^2 := by nlinarith [sq_pos_of_pos ht]
  have h1 := mul_nonneg (sub_nonneg.mpr hP1) ha0
  have h2 := mul_le_mul_of_nonneg_left hat (mul_nonneg hP.le ht.le)
  have htest : 0 < DigitalPrivacy.Strategy.profit β ρ ψ P t (t^2) := by
    dsimp [DigitalPrivacy.Strategy.profit]
    nlinarith
  have hopt := hs.2 t (t^2) ⟨⟨ht.le, ht1⟩, htC.le⟩
  have hac := priv_nonneg h.1.2.1 hρ hs.1.1.1 hs.1.2
  by_contra hno
  have haz : abar β ρ ξ C = 0 := le_antisymm (le_of_not_gt hno) hac
  have hcost' := mul_nonneg hψ.le hs.1.2
  dsimp [DigitalPrivacy.Strategy.profit] at hopt
  rw [haz] at hopt
  nlinarith

theorem solution (β ρ ψ P α : ℝ) (h : Standing β ρ ψ P α) (ξs Cs ξW CW : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ P ξs Cs) (hW : IsSocialOpt β ρ ψ P α ξW CW) :
    (P = 0 → ξs ≤ ξW ∧ Cs ≤ CW) ∧
      (0 < P → ¬ (ξs ≤ ξW ∧ CW ≤ Cs ∧ (ξs < ξW ∨ CW < Cs))) := by
  have ha := priv_activity β ρ ψ P α h ξs Cs ξW CW hs hW
  have hp : Pi β ρ ψ P ξW CW ≤ Pi β ρ ψ P ξs Cs := hs.2 ξW CW hW.1
  have hna := priv_nonneg h.1.2.1 h.1.2.2.1 hs.1.1.1 hs.1.2
  have hnw := priv_nonneg h.1.2.1 h.1.2.2.1 hW.1.1.1 hW.1.2
  constructor
  · intro hP
    subst P
    have hc : Cs ≤ CW := by
      simp only [Pi, sub_zero, one_mul, zero_mul, add_zero] at hp
      apply (mul_le_mul_iff_right₀ h.2.1).mp
      linarith
    refine ⟨?_, hc⟩
    by_contra hx
    exact (not_lt_of_ge hc) (priv_usage β ρ ψ α h ξs Cs ξW CW hs hW (lt_of_not_ge hx))
  · rintro hP ⟨hx, hc, hstrict⟩
    have hdata : ξs * abar β ρ ξs Cs ≤ ξW * abar β ρ ξW CW :=
      mul_le_mul hx ha hna hW.1.1.1
    have hu := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr h.1.2.2.2.2.2.2.1)
    have hd := mul_le_mul_of_nonneg_left hdata hP.le
    have hcost := mul_le_mul_of_nonneg_left hc h.2.1.le
    rcases hstrict with hxs | hcs
    ·
      have hapos := priv_activity_pos β ρ ψ P α h hP ξs Cs hs
      have hdt : ξs * abar β ρ ξs Cs < ξW * abar β ρ ξW CW :=
        (mul_lt_mul_of_pos_right hxs hapos).trans_le
          (mul_le_mul_of_nonneg_left ha hW.1.1.1)
      have hpdt := mul_lt_mul_of_pos_left hdt hP
      dsimp [Pi] at hp
      linarith
    · have hct := mul_lt_mul_of_pos_left hcs h.2.1
      dsimp [Pi] at hp
      linarith
