-- Prove2me | solution 1 for CachonCoord.PriceNewsvendor.quantity_discount
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:39:05.677481+00:00
-- url     : https://prove2.me/submissions/53d94c16-774d-4bf8-8927-419ec79a327c

import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model



namespace CachonCoord.PriceNewsvendor

open Model

theorem cp_coordparams_core (M : Model) (lam p : ℝ) :
    p - M.v + M.gr - M.contingentB lam p = lam * (p - M.v + M.g) ∧
    M.contingentW lam p - M.contingentB lam p + M.cr - M.v =
      lam * (M.c - M.v) := by
  simp only [Model.contingentB, Model.contingentW, Model.g, Model.c]
  constructor <;> ring

theorem cp_split_core (M : Model) (lam q p : ℝ) :
    M.buybackRetailer (M.contingentW lam p) (M.contingentB lam p) q p =
      lam * (M.Pi q p + M.g * M.mu p) - M.gr * M.mu p ∧
    M.buybackSupplier (M.contingentW lam p) (M.contingentB lam p) q p =
      (1 - lam) * M.Pi q p - (lam * M.g - M.gr) * M.mu p := by
  simp only [Model.buybackRetailer, Model.buybackSupplier, Model.contingentB,
    Model.contingentW, Model.g, Model.c, Model.Pi]
  constructor <;> ring

theorem cp_pv_pos (M : Model) (p : ℝ) (hp : p ∈ M.demand.prices) : 0 < p - M.v := by
  have h1 := M.price_above_cost p hp
  have h2 := M.salvage_below_cost
  linarith

theorem cp_crs_core (M : Model) (lam q p : ℝ) (hp : p ∈ M.demand.prices) :
    M.revenueRetailer (lam * (M.c - M.v) - M.cr + (lam + (lam * M.g - M.gr) / (p - M.v)) * M.v)
      (lam + (lam * M.g - M.gr) / (p - M.v)) q p =
      lam * (M.Pi q p + M.g * M.mu p) - M.gr * M.mu p := by
  have h := cp_pv_pos M p hp
  simp only [Model.revenueRetailer, Model.Pi]
  have e : (lam + (lam * M.g - M.gr) / (p - M.v)) * (p - M.v) = lam * (p - M.v) + (lam * M.g - M.gr) := by
    field_simp
  have e2 : (lam + (lam * M.g - M.gr) / (p - M.v)) * (p - M.v) + M.gr = lam * (p - M.v + M.g) := by
    rw [e]; ring
  rw [e2]; ring

theorem cp_goal_core (M : Model) (lam : ℝ) (opt : ℝ × ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) M.feasible opt) :
    (∀ x : ℝ × ℝ, x ∈ M.feasible →
      M.buybackRetailer (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2 =
        lam * M.Pi x.1 x.2 ∧
      M.revenueRetailer (M.revenueW lam) lam x.1 x.2 =
        lam * M.Pi x.1 x.2 ∧
      M.buybackSupplier (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2 =
        (1 - lam) * M.Pi x.1 x.2) ∧
    IsMaxOn (fun x : ℝ × ℝ =>
      M.buybackRetailer (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2)
      M.feasible opt ∧
    IsMaxOn (fun x : ℝ × ℝ =>
      M.buybackSupplier (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2)
      M.feasible opt := by
  have hg : M.g = 0 := by simp [Model.g, hgr, hgs]
  have key : ∀ x : ℝ × ℝ,
      M.buybackRetailer (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2 =
        lam * M.Pi x.1 x.2 ∧
      M.revenueRetailer (M.revenueW lam) lam x.1 x.2 =
        lam * M.Pi x.1 x.2 ∧
      M.buybackSupplier (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2 =
        (1 - lam) * M.Pi x.1 x.2 := by
    intro x
    obtain ⟨h1, h2⟩ := cp_split_core M lam x.1 x.2
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, hg, hgr]; ring
    · simp only [Model.revenueRetailer, Model.revenueW, Model.Pi, hgr, hg, Model.c]; ring
    · rw [h2, hg, hgr]; ring
  refine ⟨fun x _ => key x, ?_, ?_⟩
  · intro x hx
    have := hopt hx
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [(key x).1, (key opt).1]
    exact mul_le_mul_of_nonneg_left this hlam0
  · intro x hx
    have := hopt hx
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [(key x).2.2, (key opt).2.2]
    exact mul_le_mul_of_nonneg_left this (by linarith)

/-- derivative of Pi in price in the zero-goodwill regime -/
theorem cp_Pi_deriv (M : Model) (q p Sp : ℝ) (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hS : HasDerivAt (fun t => M.S q t) Sp p) :
    HasDerivAt (fun t => M.Pi q t) (M.S q p + (p - M.v) * Sp) p := by
  have hg : M.g = 0 := by simp [Model.g, hgr, hgs]
  have hf : (fun t => M.Pi q t) = fun t => (t - M.v) * M.S q t - (M.c - M.v) * q := by
    funext t; simp only [Model.Pi, hg]; ring
  rw [hf]
  have h1 : HasDerivAt (fun t : ℝ => t - M.v) 1 p := (hasDerivAt_id p).sub_const _
  have := (h1.mul hS).sub_const ((M.c - M.v) * q)
  exact this.congr_deriv (by ring)

theorem cp_rsp_core (M : Model) (q p phi wr Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0) (hphi : 0 < phi)
    (hS : HasDerivAt (fun t => M.S q t) Sp p) :
    HasDerivAt (fun t => M.Pi q t) (M.S q p + (p - M.v) * Sp) p ∧
    HasDerivAt (fun t => M.revenueRetailer wr phi q t)
      (phi * (M.S q p + (p - M.v) * Sp)) p ∧
    (IsMaxOn (fun t => M.Pi q t) M.demand.prices p ↔
     IsMaxOn (fun t => M.revenueRetailer wr phi q t) M.demand.prices p) := by
  have hg : M.g = 0 := by simp [Model.g, hgr, hgs]
  have hP := cp_Pi_deriv M q p Sp hgr hgs hS
  have hrel : ∀ t, M.revenueRetailer wr phi q t =
      phi * M.Pi q t + (phi * (M.c - M.v) - (wr + M.cr - phi * M.v)) * q := by
    intro t; simp only [Model.revenueRetailer, Model.Pi, hg, hgr]; ring
  have hf : (fun t => M.revenueRetailer wr phi q t) =
      fun t => phi * M.Pi q t + (phi * (M.c - M.v) - (wr + M.cr - phi * M.v)) * q := by
    funext t; exact hrel t
  refine ⟨hP, ?_, ?_⟩
  · rw [hf]; exact (hP.const_mul phi).add_const _
  · constructor
    · intro h x hx
      have := h hx
      simp only [Set.mem_setOf_eq] at this ⊢
      rw [hrel, hrel]
      have := mul_le_mul_of_nonneg_left this hphi.le
      linarith
    · intro h x hx
      have := h hx
      simp only [Set.mem_setOf_eq] at this ⊢
      rw [hrel, hrel] at this
      have h2 : phi * M.Pi q x ≤ phi * M.Pi q p := by linarith
      exact le_of_mul_le_mul_left h2 hphi

theorem cp_deriv_zero (M : Model) (f : ℝ → ℝ) (p d : ℝ) (hp : p ∈ M.demand.prices)
    (hd : HasDerivAt f d p) (hmax : IsMaxOn f M.demand.prices p) : d = 0 := by
  have hloc : IsLocalMax f p :=
    hmax.isLocalMax (M.demand.prices_open.mem_nhds hp)
  exact hloc.hasDerivAt_eq_zero hd

theorem cp_eq14_core (M : Model) (q p Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p)
    (hmax : IsMaxOn (fun t => M.Pi q t) M.demand.prices p) :
    M.S q p + (p - M.v) * Sp = 0 :=
  cp_deriv_zero M _ p _ hp (cp_Pi_deriv M q p Sp hgr hgs hS) hmax

theorem cp_eq16_core (M : Model) (q p wb b Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p) (hSp : Sp ≠ 0)
    (hchain : IsMaxOn (fun t => M.Pi q t) M.demand.prices p)
    (hret : IsMaxOn (fun t => M.buybackRetailer wb b q t) M.demand.prices p) :
    b = -M.gs ∧
    ∀ lam : ℝ, p - M.v + M.gr - b = lam * (p - M.v + M.g) →
      wb - b + M.cr - M.v = lam * (M.c - M.v) → wb = M.cs - M.gs := by
  have hg : M.g = 0 := by simp [Model.g, hgr, hgs]
  have e1 := cp_eq14_core M q p Sp hgr hgs hp hS hchain
  have hf : (fun t => M.buybackRetailer wb b q t) =
      fun t => (t - M.v - b) * M.S q t - (wb - b + M.cr - M.v) * q := by
    funext t; simp only [Model.buybackRetailer, hgr]; ring
  have hd : HasDerivAt (fun t => M.buybackRetailer wb b q t)
      (M.S q p + (p - M.v - b) * Sp) p := by
    rw [hf]
    have h1 : HasDerivAt (fun t : ℝ => t - M.v - b) 1 p :=
      ((hasDerivAt_id p).sub_const _).sub_const _
    exact ((h1.mul hS).sub_const _).congr_deriv (by ring)
  have e2 := cp_deriv_zero M _ p _ hp hd hret
  have hb : b * Sp = 0 := by linarith
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · exact h
    · exact absurd h hSp
  refine ⟨by rw [hb0, hgs]; ring, ?_⟩
  intro lam h5 h6
  have hpv := cp_pv_pos M p hp
  rw [hb0, hgr, hg] at h5
  have hl : lam = 1 := by
    have : (lam - 1) * (p - M.v) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  rw [hl, hb0] at h6
  simp only [Model.c] at h6
  rw [hgs]; linarith

theorem cp_eq15_core (M : Model) (q p wq δ Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hq : 0 < q) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p)
    (hFint : IntervalIntegrable (fun y => M.demand.priceSlope y p) MeasureTheory.volume
      ((1 - δ) * q) q)
    (hI : HasDerivAt (fun t => ∫ y in (1 - δ) * q..q, cdfOf (M.demand.law t) y)
      (∫ y in (1 - δ) * q..q, M.demand.priceSlope y p) p)
    (hchain : IsMaxOn (fun t => M.Pi q t) M.demand.prices p)
    (hret : IsMaxOn (fun t => M.qfRetailer wq δ q t) M.demand.prices p) :
    wq = M.v - M.cr ∨ δ = 0 := by
  have e1 := cp_eq14_core M q p Sp hgr hgs hp hS hchain
  have hf : (fun t => M.qfRetailer wq δ q t) =
      fun t => (t - M.v) * M.S q t - (wq + M.cr - M.v) * q +
        (wq + M.cr - M.v) * (∫ y in (1 - δ) * q..q, cdfOf (M.demand.law t) y) := by
    funext t; simp only [Model.qfRetailer, hgr]; ring
  have hd : HasDerivAt (fun t => M.qfRetailer wq δ q t)
      (M.S q p + (p - M.v) * Sp +
        (wq + M.cr - M.v) * (∫ y in (1 - δ) * q..q, M.demand.priceSlope y p)) p := by
    rw [hf]
    have h1 : HasDerivAt (fun t : ℝ => t - M.v) 1 p := (hasDerivAt_id p).sub_const _
    exact (((h1.mul hS).sub_const _).add (hI.const_mul (wq + M.cr - M.v))).congr_deriv (by ring)
  have e2 := cp_deriv_zero M _ p _ hp hd hret
  rcases eq_or_lt_of_le hδ0 with h | h
  · exact Or.inr h.symm
  · left
    have hpos : 0 < ∫ y in (1 - δ) * q..q, M.demand.priceSlope y p := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on hFint
      · intro x hx
        apply M.demand.price_slope_pos p hp
        have : 0 ≤ (1 - δ) * q := mul_nonneg (by linarith) hq.le
        linarith [hx.1]
      · nlinarith
    have : (wq + M.cr - M.v) * (∫ y in (1 - δ) * q..q, M.demand.priceSlope y p) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith

theorem cp_S_zero (M : Model) (p : ℝ) (hp : p ∈ M.demand.prices) : M.S 0 p = 0 := by
  simp only [Model.S, SupplyChainTheory.expSales]
  have hae : ∀ᵐ d ∂(M.demand.law p), 0 ≤ d := by
    rw [MeasureTheory.ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
    rw [this]; exact M.demand.nonnegative p hp
  have : (fun d : ℝ => min 0 d) =ᵐ[M.demand.law p] fun _ => (0 : ℝ) := by
    filter_upwards [hae] with d hd
    exact min_eq_left hd
  rw [MeasureTheory.integral_congr_ae this]; simp

theorem cp_qdW_mul (M : Model) (lam p0 q : ℝ) (hp0 : p0 ∈ M.demand.prices) :
    M.qdW lam p0 q * q = ((1 - lam) * (p0 - M.v + M.g) - M.gs) * M.S q p0 +
      (lam * (M.c - M.v) - M.cr + M.v) * q := by
  simp only [Model.qdW]
  rcases eq_or_ne q 0 with h | h
  · subst h; rw [cp_S_zero M p0 hp0]; ring
  · have e : M.S q p0 / q * q = M.S q p0 := div_mul_cancel₀ _ h
    linear_combination ((1 - lam) * (p0 - M.v + M.g) - M.gs) * e

theorem cp_qd_core (M : Model) (lam : ℝ) (opt : ℝ × ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hopt_feasible : opt ∈ M.feasible)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) M.feasible opt) :
    (∀ q : ℝ, 0 ≤ q → ∀ p ∈ M.demand.prices,
      M.qdRetailer lam opt.2 q p =
        (p - M.v + M.gr) * M.S q p - lam * (M.c - M.v) * q - M.gr * M.mu p -
          ((1 - lam) * (opt.2 - M.v + M.g) - M.gs) * M.S q opt.2) ∧
    (∀ q : ℝ, 0 ≤ q →
      M.qdRetailer lam opt.2 q opt.2 =
        lam * (M.Pi q opt.2 + M.g * M.mu opt.2) - M.gr * M.mu opt.2) ∧
    (M.gs = 0 → ∀ q : ℝ, 0 ≤ q → ∀ p ∈ M.demand.prices,
      (IsMaxOn (fun t => M.qdRetailer lam opt.2 q t) M.demand.prices p ↔
        IsMaxOn (fun t => M.Pi q t) M.demand.prices p)) ∧
    IsMaxOn (fun q => M.qdRetailer lam opt.2 q opt.2) (Set.Ici 0) opt.1 ∧
    IsMaxOn (fun q => M.qdSupplier lam opt.2 q opt.2) (Set.Ici 0) opt.1 := by
  have hp0 : opt.2 ∈ M.demand.prices := hopt_feasible.2
  have hq0 : opt.1 ∈ Set.Ici (0:ℝ) := hopt_feasible.1
  have R : ∀ q p, M.qdRetailer lam opt.2 q p =
        (p - M.v + M.gr) * M.S q p - lam * (M.c - M.v) * q - M.gr * M.mu p -
          ((1 - lam) * (opt.2 - M.v + M.g) - M.gs) * M.S q opt.2 := by
    intro q p
    have := cp_qdW_mul M lam opt.2 q hp0
    simp only [Model.qdRetailer]
    have e : (M.qdW lam opt.2 q + M.cr - M.v) * q = M.qdW lam opt.2 q * q + (M.cr - M.v) * q := by ring
    rw [e, this]; ring
  have R2 : ∀ q, M.qdRetailer lam opt.2 q opt.2 =
        lam * (M.Pi q opt.2 + M.g * M.mu opt.2) - M.gr * M.mu opt.2 := by
    intro q; rw [R]; simp only [Model.Pi, Model.g]; ring
  have Sup : ∀ q, M.qdSupplier lam opt.2 q opt.2 =
        (1 - lam) * (M.Pi q opt.2 + M.g * M.mu opt.2) - M.gs * M.mu opt.2 := by
    intro q
    have := cp_qdW_mul M lam opt.2 q hp0
    simp only [Model.qdSupplier]
    have e : (M.qdW lam opt.2 q - M.cs) * q = M.qdW lam opt.2 q * q - M.cs * q := by ring
    rw [e, this]; simp only [Model.Pi, Model.g, Model.c]; ring
  refine ⟨fun q _ p _ => R q p, fun q _ => R2 q, ?_, ?_, ?_⟩
  · intro hgs q _ p _
    have hrel : ∀ t, M.qdRetailer lam opt.2 q t = M.Pi q t +
        ((1 - lam) * (M.c - M.v) * q - ((1 - lam) * (opt.2 - M.v + M.g) - M.gs) * M.S q opt.2) := by
      intro t; rw [R]; simp only [Model.Pi, Model.g, hgs]; ring
    constructor
    · intro h x hx
      have := h hx
      simp only [Set.mem_setOf_eq] at this ⊢
      rw [hrel, hrel] at this; linarith
    · intro h x hx
      have := h hx
      simp only [Set.mem_setOf_eq] at this ⊢
      rw [hrel, hrel]; linarith
  · intro q hq
    have : (q, opt.2) ∈ M.feasible := ⟨hq, hp0⟩
    have h := hopt this
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [R2, R2]
    have := mul_le_mul_of_nonneg_left h hlam0
    nlinarith
  · intro q hq
    have : (q, opt.2) ∈ M.feasible := ⟨hq, hp0⟩
    have h := hopt this
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [Sup, Sup]
    have := mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ 1 - lam)
    nlinarith

end CachonCoord.PriceNewsvendor

open CachonCoord.PriceNewsvendor


theorem solution (M : Model) (lam : ℝ) (opt : ℝ × ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hopt_feasible : opt ∈ M.feasible)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) M.feasible opt) :
    (∀ q : ℝ, 0 ≤ q → ∀ p ∈ M.demand.prices,
      M.qdRetailer lam opt.2 q p =
        (p - M.v + M.gr) * M.S q p - lam * (M.c - M.v) * q - M.gr * M.mu p -
          ((1 - lam) * (opt.2 - M.v + M.g) - M.gs) * M.S q opt.2) ∧
    (∀ q : ℝ, 0 ≤ q →
      M.qdRetailer lam opt.2 q opt.2 =
        lam * (M.Pi q opt.2 + M.g * M.mu opt.2) - M.gr * M.mu opt.2) ∧
    (M.gs = 0 → ∀ q : ℝ, 0 ≤ q → ∀ p ∈ M.demand.prices,
      (IsMaxOn (fun t => M.qdRetailer lam opt.2 q t) M.demand.prices p ↔
        IsMaxOn (fun t => M.Pi q t) M.demand.prices p)) ∧
    IsMaxOn (fun q => M.qdRetailer lam opt.2 q opt.2) (Set.Ici 0) opt.1 ∧
    IsMaxOn (fun q => M.qdSupplier lam opt.2 q opt.2) (Set.Ici 0) opt.1 := by
  exact cp_qd_core M lam opt hlam0 hlam1 hopt_feasible hopt
