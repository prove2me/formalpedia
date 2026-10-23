-- Prove2me | solution 1 for CourierDispatch.Endogenous.batch_optimum
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T21:37:36.44819+00:00
-- url     : https://prove2.me/submissions/418f96f8-5c10-4fb0-b544-eb1b0d5bca68

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

open CourierDispatch.Exogenous CourierDispatch.Endogenous
open scoped Pointwise
open Filter Topology

open CourierDispatch.Exogenous CourierDispatch.Endogenous
open scoped Pointwise

namespace CD2Aux

lemma TB_pos : 0 < TB := by unfold TB; positivity

lemma TB_bounds : (8933563:ℝ)/10^7 < TB ∧ TB < 8933565/10^7 := by
  have h1 := Real.pi_gt_d6; have h2 := Real.pi_lt_d6
  unfold TB
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

lemma TB_lt_one : TB < 1 := by linarith [TB_bounds.2]

lemma muB_eq (r : ℝ) (hr : r ≠ 0) : muB r = TB / (2 * r) := by
  unfold muB TB
  have : (32 + 15 * Real.pi) ≠ 0 := by positivity
  field_simp
  ring

lemma muD_eq (r : ℝ) : muD r = TD / r := by
  unfold muD TD; ring

/-- dedicated per-unit wait-cost function at `r = 1` -/
noncomputable def phiD (x : ℝ) : ℝ := 3 / 4 * x ^ 2 / (3 / 4 - x)
/-- batch per-unit wait-cost function at `r = 1` with constants `C`, `T` -/
noncomputable def psiB (C T x : ℝ) : ℝ := 1 / 2 + x / 3 + C * x ^ 2 / (T * (T - x))

noncomputable def hD (α : ℝ) : ℝ := α * CD + TD - √(α * CD * (2 * TD + α * CD))
noncomputable def xD (α : ℝ) : ℝ := TD * (1 - α * CD / √(α * CD * (2 * TD + α * CD)))
noncomputable def hB (C T α : ℝ) : ℝ :=
  α * (2 * C - 1 / 2 - T / 3) + T - 2 / 3 * √(3 * α * C * (3 * T + α * (3 * C - T)))
noncomputable def xB (C T α : ℝ) : ℝ :=
  T * (1 - Real.sqrt 3 * (α * C) / √(α * C * (3 * T + α * (3 * C - T))))

/-! ## Scaling -/

lemma VinfD_eq (c r lam : ℝ) (hr : 0 < r) (hl : lam < muD r) :
    VinfD c r lam = (1 / r) * (lam * r - (c * r) * phiD (lam * r)) := by
  have hl' : lam * r < 3 / 4 := by
    rw [muD_eq] at hl; unfold TD at hl; rwa [lt_div_iff₀ hr] at hl
  unfold VinfD Vinf WD phiD
  rw [muD_eq]; unfold CD TD
  have h1 : (3 / 4 - lam * r) ≠ 0 := by linarith
  have h2 : (3 / 4 / r - lam) ≠ 0 := by
    intro h; apply h1; field_simp at h; linarith
  field_simp
  ring

lemma VinfB_eq (CB c r lam : ℝ) (hr : 0 < r) (hl0 : 0 < lam) (hl : lam < 2 * muB r) :
    VinfB CB c r lam = (1 / r) * (lam * r - (c * r) * psiB CB TB (lam * r)) := by
  have hT := TB_pos
  rw [muB_eq r hr.ne'] at hl
  have hl' : lam * r < TB := by
    have : 2 * (TB / (2 * r)) = TB / r := by field_simp
    rw [this, lt_div_iff₀ hr] at hl; exact hl
  unfold VinfB Vinf WB psiB
  rw [muB_eq r hr.ne']
  have h1 : (TB - lam * r) ≠ 0 := by linarith
  have h2 : (2 * (TB / (2 * r)) - lam) ≠ 0 := by
    intro h; apply h1; field_simp at h; linarith
  have h3 : lam ≠ 0 := hl0.ne'
  field_simp
  ring


/-! ## Dedicated core -/

lemma hDS (α : ℝ) (hα : 0 < α) :
    0 < √(α * CD * (2 * TD + α * CD)) ∧
    (√(α * CD * (2 * TD + α * CD))) ^ 2 = α * CD * (2 * TD + α * CD) := by
  have h : 0 < α * CD * (2 * TD + α * CD) := by unfold CD TD; positivity
  exact ⟨Real.sqrt_pos.2 h, Real.sq_sqrt h.le⟩

lemma phiD_mul (x : ℝ) (hx : x < 3 / 4) : phiD x * (3 / 4 - x) = 3 / 4 * x ^ 2 := by
  unfold phiD
  have hy : (3 / 4 - x) ≠ 0 := by linarith
  exact div_mul_cancel₀ _ hy

lemma ded_key (α x : ℝ) (hα : 0 < α) (hx : x < 3 / 4) :
    hD α - (x - α * phiD x) =
      ((3 / 2 + 9 / 8 * α) * (3 / 4 - x) - 3 / 4 * √(α * CD * (2 * TD + α * CD))) ^ 2 /
        (3 / 2 * (3 / 2 + 9 / 8 * α) * (3 / 4 - x)) := by
  obtain ⟨hS0, hS2⟩ := hDS α hα
  have hphi := phiD_mul x hx
  set S := √(α * CD * (2 * TD + α * CD)) with hS
  have hy : 0 < 3 / 4 - x := by linarith
  have hpos : 0 < 3 / 2 * (3 / 2 + 9 / 8 * α) * (3 / 4 - x) := by positivity
  rw [eq_div_iff hpos.ne']
  unfold hD
  rw [← hS]
  unfold CD TD at hS2 ⊢
  linear_combination (3 / 2 * (3 / 2 + 9 / 8 * α) * α) * hphi + (-(9:ℝ) / 16) * hS2

lemma ded_le (α x : ℝ) (hα : 0 < α) (hx : x < 3 / 4) : x - α * phiD x ≤ hD α := by
  have h := ded_key α x hα hx
  have : 0 ≤ ((3 / 2 + 9 / 8 * α) * (3 / 4 - x) - 3 / 4 * √(α * CD * (2 * TD + α * CD))) ^ 2 /
        (3 / 2 * (3 / 2 + 9 / 8 * α) * (3 / 4 - x)) := by
    apply div_nonneg (sq_nonneg _)
    have : 0 < 3 / 4 - x := by linarith
    positivity
  linarith

lemma xD_mem (α : ℝ) (hα : 0 < α) : 0 < xD α ∧ xD α < 3 / 4 := by
  obtain ⟨hS0, hS2⟩ := hDS α hα
  set S := √(α * CD * (2 * TD + α * CD)) with hS
  have hlt : α * CD < S := by
    rw [hS, Real.lt_sqrt (by unfold CD; positivity)]; unfold CD TD; nlinarith
  unfold xD; rw [← hS]
  unfold CD TD at hS2 ⊢
  unfold CD at hlt
  constructor
  · have : α * (9 / 8) / S < 1 := by rw [div_lt_one hS0]; exact hlt
    nlinarith
  · have : 0 < α * (9 / 8) / S := by positivity
    nlinarith

lemma ded_eq_iff (α x : ℝ) (hα : 0 < α) (hx : x < 3 / 4) :
    x - α * phiD x = hD α ↔ x = xD α := by
  have h := ded_key α x hα hx
  obtain ⟨hS0, hS2⟩ := hDS α hα
  have hy : 0 < 3 / 4 - x := by linarith
  have hpos : 0 < 3 / 2 * (3 / 2 + 9 / 8 * α) * (3 / 4 - x) := by positivity
  set S := √(α * CD * (2 * TD + α * CD)) with hS
  have key : x - α * phiD x = hD α ↔
      (3 / 2 + 9 / 8 * α) * (3 / 4 - x) - 3 / 4 * S = 0 := by
    constructor
    · intro he
      rw [he, sub_self, eq_comm, div_eq_zero_iff] at h
      rcases h with h | h
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      · linarith
    · intro he; rw [he] at h; simp at h; linarith
  rw [key]
  unfold xD; rw [← hS]
  unfold CD TD at hS2 ⊢
  have hp : 0 < 3 / 2 + 9 / 8 * α := by positivity
  constructor
  · intro he
    have h2 : (3 / 2 + 9 / 8 * α) * (S * (3 / 4 - x) - 3 / 4 * (α * (9 / 8))) = 0 := by
      linear_combination S * he + 3 / 4 * hS2
    rcases mul_eq_zero.1 h2 with h2 | h2
    · linarith
    · field_simp
      linarith
  · intro he
    rw [he]
    field_simp
    linear_combination (-(384:ℝ)) * hS2

/-! ## Batch core -/

lemma batchQ_pos (C T α : ℝ) (hC : 0 < C) (hT : 0 < T) (hα : 0 < α) (hα3 : α < 3) :
    0 < 3 * T + α * (3 * C - T) := by nlinarith

lemma hBS (C T α : ℝ) (hC : 0 < C) (hT : 0 < T) (hα : 0 < α) (hα3 : α < 3) :
    0 < √(3 * α * C * (3 * T + α * (3 * C - T))) ∧
    (√(3 * α * C * (3 * T + α * (3 * C - T)))) ^ 2 = 3 * α * C * (3 * T + α * (3 * C - T)) ∧
    0 < √(α * C * (3 * T + α * (3 * C - T))) ∧
    (√(α * C * (3 * T + α * (3 * C - T)))) ^ 2 = α * C * (3 * T + α * (3 * C - T)) ∧
    √(3 * α * C * (3 * T + α * (3 * C - T))) =
      Real.sqrt 3 * √(α * C * (3 * T + α * (3 * C - T))) := by
  have hQ := batchQ_pos C T α hC hT hα hα3
  have h1 : 0 < 3 * α * C * (3 * T + α * (3 * C - T)) := by positivity
  have h2 : 0 < α * C * (3 * T + α * (3 * C - T)) := by positivity
  refine ⟨Real.sqrt_pos.2 h1, Real.sq_sqrt h1.le, Real.sqrt_pos.2 h2, Real.sq_sqrt h2.le, ?_⟩
  rw [← Real.sqrt_mul (by norm_num)]; ring_nf

lemma psiB_mul (C T x : ℝ) (hT : 0 < T) (hxT : x < T) :
    (psiB C T x - 1 / 2 - x / 3) * (T * (T - x)) = C * x ^ 2 := by
  unfold psiB
  have hy : T * (T - x) ≠ 0 := by have : 0 < T - x := by linarith
                                  positivity
  have : 1 / 2 + x / 3 + C * x ^ 2 / (T * (T - x)) - 1 / 2 - x / 3 =
      C * x ^ 2 / (T * (T - x)) := by ring
  rw [this]; exact div_mul_cancel₀ _ hy

lemma batch_key (C T α x : ℝ) (hC : 0 < C) (hT : 0 < T) (hα : 0 < α) (hα3 : α < 3)
    (hxT : x < T) :
    hB C T α - (x - α * psiB C T x) =
      ((3 * T + α * (3 * C - T)) * (T - x) - T * √(3 * α * C * (3 * T + α * (3 * C - T)))) ^ 2 /
        (3 * T * (3 * T + α * (3 * C - T)) * (T - x)) := by
  have hQ := batchQ_pos C T α hC hT hα hα3
  obtain ⟨hS0, hS2, -⟩ := hBS C T α hC hT hα hα3
  have hpsi := psiB_mul C T x hT hxT
  set S := √(3 * α * C * (3 * T + α * (3 * C - T))) with hS
  set Q := 3 * T + α * (3 * C - T) with hQdef
  have hy : 0 < T - x := by linarith
  have hpos : 0 < 3 * T * Q * (T - x) := by positivity
  rw [eq_div_iff hpos.ne']
  unfold hB
  rw [← hS]
  linear_combination (3 * α * Q) * hpsi + (-T ^ 2) * hS2

lemma batch_le (C T α x : ℝ) (hC : 0 < C) (hT : 0 < T) (hα : 0 < α) (hα3 : α < 3)
    (hxT : x < T) : x - α * psiB C T x ≤ hB C T α := by
  have h := batch_key C T α x hC hT hα hα3 hxT
  have hQ := batchQ_pos C T α hC hT hα hα3
  have : 0 ≤ ((3 * T + α * (3 * C - T)) * (T - x) - T * √(3 * α * C * (3 * T + α * (3 * C - T)))) ^ 2 /
        (3 * T * (3 * T + α * (3 * C - T)) * (T - x)) := by
    apply div_nonneg (sq_nonneg _)
    have : 0 < T - x := by linarith
    positivity
  linarith

lemma xB_mem (C T α : ℝ) (hC : 0 < C) (hT : 0 < T) (hα : 0 < α) (hα3 : α < 3) :
    0 < xB C T α ∧ xB C T α < T := by
  have hQ := batchQ_pos C T α hC hT hα hα3
  obtain ⟨-, -, hR0, hR2, -⟩ := hBS C T α hC hT hα hα3
  set R := √(α * C * (3 * T + α * (3 * C - T))) with hR
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  have h33 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlt : Real.sqrt 3 * (α * C) < R := by
    rw [← abs_of_pos hR0, ← abs_of_pos (by positivity : 0 < Real.sqrt 3 * (α * C))]
    apply sq_lt_sq.1
    rw [mul_pow, h33, hR2]; nlinarith [mul_pos hα hC, mul_pos (mul_pos hα hC) hT]
  unfold xB; rw [← hR]
  constructor
  · have : Real.sqrt 3 * (α * C) / R < 1 := by rw [div_lt_one hR0]; exact hlt
    nlinarith
  · have : 0 < Real.sqrt 3 * (α * C) / R := by positivity
    nlinarith

lemma batch_eq_iff (C T α x : ℝ) (hC : 0 < C) (hT : 0 < T) (hα : 0 < α) (hα3 : α < 3)
    (hxT : x < T) : x - α * psiB C T x = hB C T α ↔ x = xB C T α := by
  have h := batch_key C T α x hC hT hα hα3 hxT
  have hQ := batchQ_pos C T α hC hT hα hα3
  obtain ⟨hS0, hS2, hR0, hR2, hSR⟩ := hBS C T α hC hT hα hα3
  have hy : 0 < T - x := by linarith
  have hpos : 0 < 3 * T * (3 * T + α * (3 * C - T)) * (T - x) := by positivity
  set S := √(3 * α * C * (3 * T + α * (3 * C - T))) with hS
  set R := √(α * C * (3 * T + α * (3 * C - T))) with hR
  set Q := 3 * T + α * (3 * C - T) with hQdef
  have h33 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : x - α * psiB C T x = hB C T α ↔ Q * (T - x) - T * S = 0 := by
    constructor
    · intro he
      rw [he, sub_self, eq_comm, div_eq_zero_iff] at h
      rcases h with h | h
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      · linarith
    · intro he; rw [he] at h; simp at h; linarith
  rw [key]
  unfold xB; rw [← hR, hSR]
  constructor
  · intro he
    have h2 : Q * (R * (T - x) - T * (Real.sqrt 3 * (α * C))) = 0 := by
      linear_combination R * he + T * Real.sqrt 3 * hR2
    rcases mul_eq_zero.1 h2 with h2 | h2
    · linarith
    · field_simp
      linarith
  · intro he
    rw [he]
    field_simp
    linear_combination (-T * Real.sqrt 3) * hR2

/-! ## Radius one -/

lemma two_muB_one : 2 * muB 1 = TB := by rw [muB_eq 1 one_ne_zero]; ring

lemma muD_one : muD 1 = 3 / 4 := by unfold muD; norm_num

lemma VD1 (α x : ℝ) (hx : x < 3 / 4) : VinfD α 1 x = x - α * phiD x := by
  rw [VinfD_eq α 1 x one_pos (by rw [muD_one]; exact hx)]; simp

lemma VB1 (CB α x : ℝ) (h0 : 0 < x) (hx : x < TB) :
    VinfB CB α 1 x = x - α * psiB CB TB x := by
  rw [VinfB_eq CB α 1 x one_pos h0 (by rw [two_muB_one]; exact hx)]; simp

lemma memD1 {x : ℝ} : x ∈ domD 1 ↔ 0 ≤ x ∧ x < 3 / 4 := by
  unfold domD; rw [muD_one]; exact Set.mem_Ico

lemma memB1 {x : ℝ} : x ∈ domB 1 ↔ 0 < x ∧ x < TB := by
  unfold domB; rw [two_muB_one]; exact Set.mem_Ioo

lemma greatD1 (α : ℝ) (hα : 0 < α) :
    xD α ∈ domD 1 ∧ IsGreatest (VinfD α 1 '' domD 1) (hD α) ∧ VinfD α 1 (xD α) = hD α := by
  obtain ⟨h0, h1⟩ := xD_mem α hα
  have hv : VinfD α 1 (xD α) = hD α := by
    rw [VD1 α _ h1]; exact (ded_eq_iff α _ hα h1).2 rfl
  refine ⟨memD1.2 ⟨h0.le, h1⟩, ⟨⟨xD α, memD1.2 ⟨h0.le, h1⟩, hv⟩, ?_⟩, hv⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [memD1] at hx
  rw [VD1 α x hx.2]; exact ded_le α x hα hx.2

lemma OptD1 (α : ℝ) (hα : 0 < α) : OptD α 1 = hD α :=
  (greatD1 α hα).2.1.csSup_eq

lemma greatB1 (CB α : ℝ) (hCB : 0 < CB) (hα : 0 < α) (hα3 : α < 3) :
    xB CB TB α ∈ domB 1 ∧ IsGreatest (VinfB CB α 1 '' domB 1) (hB CB TB α) ∧
      VinfB CB α 1 (xB CB TB α) = hB CB TB α := by
  have hT := TB_pos
  obtain ⟨h0, h1⟩ := xB_mem CB TB α hCB hT hα hα3
  have hv : VinfB CB α 1 (xB CB TB α) = hB CB TB α := by
    rw [VB1 CB α _ h0 h1]; exact (batch_eq_iff CB TB α _ hCB hT hα hα3 h1).2 rfl
  refine ⟨memB1.2 ⟨h0, h1⟩, ⟨⟨_, memB1.2 ⟨h0, h1⟩, hv⟩, ?_⟩, hv⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [memB1] at hx
  rw [VB1 CB α x hx.1 hx.2]; exact batch_le CB TB α x hCB hT hα hα3 hx.2

lemma OptB1 (CB α : ℝ) (hCB : 0 < CB) (hα : 0 < α) (hα3 : α < 3) :
    OptB CB α 1 = hB CB TB α :=
  (greatB1 CB α hCB hα hα3).2.1.csSup_eq

lemma OptD1_unique (α x : ℝ) (hα : 0 < α) (hx : x ∈ domD 1) (h : VinfD α 1 x = OptD α 1) :
    x = xD α := by
  rw [memD1] at hx
  rw [OptD1 α hα, VD1 α x hx.2] at h
  exact (ded_eq_iff α x hα hx.2).1 h

lemma OptB1_unique (CB α x : ℝ) (hCB : 0 < CB) (hα : 0 < α) (hα3 : α < 3) (hx : x ∈ domB 1)
    (h : VinfB CB α 1 x = OptB CB α 1) : x = xB CB TB α := by
  rw [memB1] at hx
  rw [OptB1 CB α hCB hα hα3, VB1 CB α x hx.1 hx.2] at h
  exact (batch_eq_iff CB TB α x hCB TB_pos hα hα3 hx.2).1 h

/-- batch revenues are bounded above (by 1) for nonnegative wait cost -/
lemma bddB1 (CB α : ℝ) (hCB : 0 < CB) (hα : 0 ≤ α) : BddAbove (VinfB CB α 1 '' domB 1) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [memB1] at hx
  rw [VB1 CB α x hx.1 hx.2]
  have : 0 ≤ psiB CB TB x := by
    unfold psiB
    have : 0 < TB - x := by linarith [hx.2]
    have := TB_pos
    have : 0 < x := hx.1
    positivity
  have := TB_lt_one
  nlinarith [hx.2]

lemma neB1 (CB α : ℝ) : (VinfB CB α 1 '' domB 1).Nonempty :=
  ⟨_, ⟨TB / 2, memB1.2 ⟨by linarith [TB_pos], by linarith [TB_pos]⟩, rfl⟩⟩

lemma neD1 (α : ℝ) : (VinfD α 1 '' domD 1).Nonempty :=
  ⟨_, ⟨0, memD1.2 ⟨le_refl _, by norm_num⟩, rfl⟩⟩

/-! ## Scaling -/

lemma imageD_scale (c r : ℝ) (hr : 0 < r) :
    VinfD c r '' domD r = (1 / r) • (VinfD (c * r) 1 '' domD 1) := by
  ext v
  simp only [Set.mem_smul_set, Set.mem_image, smul_eq_mul]
  have hmem : ∀ lam, lam ∈ domD r ↔ lam * r ∈ domD 1 := by
    intro lam
    rw [memD1]; unfold domD; rw [muD_eq]; unfold TD
    rw [Set.mem_Ico, lt_div_iff₀ hr]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by positivity, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, h2⟩
  constructor
  · rintro ⟨lam, hl, rfl⟩
    refine ⟨VinfD (c * r) 1 (lam * r), ⟨lam * r, (hmem lam).1 hl, rfl⟩, ?_⟩
    have hl2 : lam < muD r := hl.2
    rw [VinfD_eq c r lam hr hl2, VD1 _ _ (memD1.1 ((hmem lam).1 hl)).2]
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : x / r ∈ domD r := by rw [hmem]; rwa [div_mul_cancel₀ x hr.ne']
    refine ⟨x / r, hx', ?_⟩
    have hl2 : x / r < muD r := hx'.2
    rw [VinfD_eq c r (x / r) hr hl2, div_mul_cancel₀ x hr.ne', VD1 _ _ (memD1.1 hx).2]

lemma imageB_scale (CB c r : ℝ) (hr : 0 < r) :
    VinfB CB c r '' domB r = (1 / r) • (VinfB CB (c * r) 1 '' domB 1) := by
  ext v
  simp only [Set.mem_smul_set, Set.mem_image, smul_eq_mul]
  have h2mu : 2 * muB r = TB / r := by rw [muB_eq r hr.ne']; field_simp
  have hmem : ∀ lam, lam ∈ domB r ↔ lam * r ∈ domB 1 := by
    intro lam
    rw [memB1]; unfold domB; rw [h2mu]
    rw [Set.mem_Ioo, lt_div_iff₀ hr]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by positivity, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, h2⟩
  constructor
  · rintro ⟨lam, hl, rfl⟩
    refine ⟨VinfB CB (c * r) 1 (lam * r), ⟨lam * r, (hmem lam).1 hl, rfl⟩, ?_⟩
    have h1 := memB1.1 ((hmem lam).1 hl)
    rw [VinfB_eq CB c r lam hr hl.1 hl.2, VB1 _ _ _ h1.1 h1.2]
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : x / r ∈ domB r := by rw [hmem]; rwa [div_mul_cancel₀ x hr.ne']
    refine ⟨x / r, hx', ?_⟩
    have h1 := memB1.1 hx
    rw [VinfB_eq CB c r (x / r) hr hx'.1 hx'.2, div_mul_cancel₀ x hr.ne', VB1 _ _ _ h1.1 h1.2]

lemma OptD_scale (c r : ℝ) (hr : 0 < r) : OptD c r = (1 / r) * OptD (c * r) 1 := by
  unfold OptD; rw [imageD_scale c r hr, Real.sSup_smul_of_nonneg (by positivity)]; rfl

lemma OptB_scale (CB c r : ℝ) (hr : 0 < r) : OptB CB c r = (1 / r) * OptB CB (c * r) 1 := by
  unfold OptB; rw [imageB_scale CB c r hr, Real.sSup_smul_of_nonneg (by positivity)]; rfl

lemma G_scale (CB c r : ℝ) (hr : 0 < r) : r * (OptB CB c r - OptD c r) = G CB (c * r) := by
  unfold G; rw [OptB_scale CB c r hr, OptD_scale c r hr]; field_simp

end CD2Aux



namespace CD2Aux

/-! ## Numerical bounds -/

lemma hD_lt (p m : ℝ) (hp : 0 < p) (hk : 0 ≤ p * (9 / 8) + 3 / 4 - m)
    (hsq : (p * (9 / 8) + 3 / 4 - m) ^ 2 < p * (9 / 8) * (2 * (3 / 4) + p * (9 / 8))) :
    hD p < m := by
  unfold hD CD TD
  have := (Real.lt_sqrt hk).2 hsq
  linarith

lemma hB_lt (C T p m : ℝ)
    (hk : 0 ≤ 3 / 2 * (p * (2 * C - 1 / 2 - T / 3) + T - m))
    (hsq : (3 / 2 * (p * (2 * C - 1 / 2 - T / 3) + T - m)) ^ 2 <
      3 * p * C * (3 * T + p * (3 * C - T))) :
    hB C T p < m := by
  unfold hB
  have := (Real.lt_sqrt hk).2 hsq
  linarith

lemma hD_pos (α : ℝ) (hα : 0 < α) : 0 < hD α := by
  unfold hD CD TD
  have : √(α * (9 / 8) * (2 * (3 / 4) + α * (9 / 8))) < α * (9 / 8) + 3 / 4 := by
    rw [Real.sqrt_lt' (by positivity)]; nlinarith
  linarith

lemma phiD_nonneg (x : ℝ) (h0 : 0 ≤ x) (hx : x < 3 / 4) : 0 ≤ phiD x := by
  unfold phiD; have : 0 < 3 / 4 - x := by linarith
  positivity

lemma psiB_upper (CB x : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (h0 : 0 < x)
    (hx : x < 8933563 / 10 ^ 7) :
    psiB CB TB x ≤ 1 / 2 + x / 3 + 59 / 100 * x ^ 2 / (8933563 / 10 ^ 7 * (8933563 / 10 ^ 7 - x)) := by
  unfold psiB
  have hT := TB_bounds
  have h1 : 0 < 8933563 / 10 ^ 7 - x := by linarith
  have h2 : 8933563 / 10 ^ 7 - x ≤ TB - x := by linarith
  have h3 : CB ≤ 59 / 100 := hCB.2
  have : CB * x ^ 2 / (TB * (TB - x)) ≤
      59 / 100 * x ^ 2 / (8933563 / 10 ^ 7 * (8933563 / 10 ^ 7 - x)) := by
    gcongr <;> linarith
  linarith

lemma psiB_lower (CB x : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (h0 : 0 < x)
    (hx : x < TB) :
    1 / 2 + x / 3 + 58 / 100 * x ^ 2 / (8933565 / 10 ^ 7 * (8933565 / 10 ^ 7 - x)) ≤
      psiB CB TB x := by
  unfold psiB
  have hT := TB_bounds
  have h1 : 0 < TB - x := by linarith
  have h3 : 58 / 100 ≤ CB := hCB.1
  have hpos : 0 < TB * (TB - x) := by have := TB_pos; positivity
  have : 58 / 100 * x ^ 2 / (8933565 / 10 ^ 7 * (8933565 / 10 ^ 7 - x)) ≤
      CB * x ^ 2 / (TB * (TB - x)) := by
    gcongr <;> linarith
  linarith

lemma CB_pos (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) : 0 < CB := by
  linarith [hCB.1]

lemma OptB_ge (CB α x : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (hα : 0 ≤ α)
    (hx : x ∈ domB 1) : VinfB CB α 1 x ≤ OptB CB α 1 :=
  le_csSup (bddB1 CB α (CB_pos CB hCB) hα) ⟨x, hx, rfl⟩

lemma affine_neg {A0 A1 p q α : ℝ} (hp : p ≤ α) (hq : α ≤ q) (h1 : A0 - p * A1 < 0)
    (h2 : A0 - q * A1 < 0) : A0 - α * A1 < 0 := by
  rcases eq_or_lt_of_le hp with h | h
  · subst h; exact h1
  · nlinarith [mul_nonneg (sub_nonneg.2 hq) (le_of_lt (neg_pos.2 h1)),
      mul_nonneg (sub_nonneg.2 hp) (le_of_lt (neg_pos.2 h2))]

/-- (N1) very small wait cost. -/
lemma G_pos_small (CB α : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (hα : 0 < α)
    (hα' : α ≤ 1 / 200) : 0 < G CB α := by
  unfold G
  obtain ⟨hm, -, hv⟩ := greatD1 α hα
  rw [OptD1 α hα, ← hv]
  have hx := memD1.1 hm
  rw [VD1 α _ hx.2]
  have hphi := phiD_nonneg _ hx.1 hx.2
  have hmB : (82 / 100 : ℝ) ∈ domB 1 := memB1.2 ⟨by norm_num, by linarith [TB_bounds.1]⟩
  have hB := OptB_ge CB α (82 / 100) hCB hα.le hmB
  rw [VB1 CB α _ (by norm_num) (by linarith [TB_bounds.1])] at hB
  have hpsi := psiB_upper CB (82 / 100) hCB (by norm_num) (by norm_num)
  have hpsi0 : 0 ≤ psiB CB TB (82 / 100) := by
    unfold psiB
    have h1 : 0 < TB - 82 / 100 := by linarith [TB_bounds.1]
    have := div_nonneg (mul_nonneg (CB_pos CB hCB).le (sq_nonneg (82 / 100 : ℝ)))
      (mul_pos TB_pos h1).le
    linarith
  have hnum : (3 / 4 : ℝ) < 82 / 100 - 1 / 200 * (1 / 2 + (82 / 100) / 3 +
      59 / 100 * (82 / 100) ^ 2 / (8933563 / 10 ^ 7 * (8933563 / 10 ^ 7 - 82 / 100))) := by
    norm_num
  have : α * psiB CB TB (82 / 100) ≤ 1 / 200 * (1 / 2 + (82 / 100) / 3 +
      59 / 100 * (82 / 100) ^ 2 / (8933563 / 10 ^ 7 * (8933563 / 10 ^ 7 - 82 / 100))) := by
    apply mul_le_mul hα' hpsi hpsi0 (by norm_num)
  have := mul_nonneg hα.le hphi
  linarith

/-- (N2) moderate small wait cost. -/
lemma G_pos_mid (CB α : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (hα : 1 / 200 ≤ α)
    (hα' : α ≤ 11 / 100) : 0 < G CB α := by
  have hα0 : 0 < α := by linarith
  unfold G
  obtain ⟨hm, -, hv⟩ := greatD1 α hα0
  rw [OptD1 α hα0, ← hv]
  have hx := memD1.1 hm
  rw [VD1 α _ hx.2]
  set xd := xD α
  have hxh : (69 / 100 : ℝ) < TB := by linarith [TB_bounds.1]
  have hmB : (69 / 100 : ℝ) ∈ domB 1 := memB1.2 ⟨by norm_num, hxh⟩
  have hB := OptB_ge CB α (69 / 100) hCB hα0.le hmB
  rw [VB1 CB α _ (by norm_num) hxh] at hB
  obtain ⟨Ψ, hpsi, hΨ⟩ : ∃ Ψ : ℝ, psiB CB TB (69 / 100) ≤ Ψ ∧ Ψ = 1 / 2 + (69 / 100) / 3 +
      59 / 100 * (69 / 100) ^ 2 / (8933563 / 10 ^ 7 * (8933563 / 10 ^ 7 - 69 / 100)) :=
    ⟨_, psiB_upper CB (69 / 100) hCB (by norm_num) (by norm_num), rfl⟩
  have e1 : xd - 1 / 200 * phiD xd < 69 / 100 - 1 / 200 * psiB CB TB (69 / 100) := by
    have := ded_le (1 / 200) xd (by norm_num) hx.2
    have h2 : hD (1 / 200) < 69 / 100 - 1 / 200 * Ψ := by
      apply hD_lt _ _ (by norm_num) <;> norm_num [hΨ]
    linarith
  have e2 : xd - 11 / 100 * phiD xd < 69 / 100 - 11 / 100 * psiB CB TB (69 / 100) := by
    have := ded_le (11 / 100) xd (by norm_num) hx.2
    have h2 : hD (11 / 100) < 69 / 100 - 11 / 100 * Ψ := by
      apply hD_lt _ _ (by norm_num) <;> norm_num [hΨ]
    linarith
  have := affine_neg (A0 := xd - 69 / 100) (A1 := phiD xd - psiB CB TB (69 / 100)) hα hα'
    (by linarith) (by linarith)
  linarith
/-- (N3) moderate large wait cost. -/
lemma G_neg_mid (CB α : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (hα : 4 / 25 ≤ α)
    (hα' : α ≤ 6 / 5) : G CB α < 0 := by
  have hα0 : 0 < α := by linarith
  have hCB0 := CB_pos CB hCB
  have hT := TB_bounds
  unfold G
  obtain ⟨hm, -, hv⟩ := greatB1 CB α hCB0 hα0 (by linarith)
  rw [OptB1 CB α hCB0 hα0 (by linarith), ← hv]
  have hx := memB1.1 hm
  rw [VB1 CB α _ hx.1 hx.2]
  set xb := xB CB TB α
  have hmD : (1 / 2 : ℝ) ∈ domD 1 := memD1.2 ⟨by norm_num, by norm_num⟩
  have hD' : VinfD α 1 (1 / 2) ≤ OptD α 1 := by
    rw [OptD1 α hα0]; exact (greatD1 α hα0).2.1.2 ⟨_, hmD, rfl⟩
  rw [VD1 α _ (by norm_num)] at hD'
  have hphi : phiD (1 / 2) = 3 / 4 := by unfold phiD; norm_num
  rw [hphi] at hD'
  have hpl := psiB_lower CB xb hCB hx.1 hx.2
  have bnd : ∀ p : ℝ, 0 < p → p < 3 → xb - p * psiB CB TB xb ≤
      hB (58 / 100) (8933565 / 10 ^ 7) p := by
    intro p hp hp3
    have h1 := batch_le (58 / 100) (8933565 / 10 ^ 7) p xb (by norm_num) (by norm_num) hp hp3
      (by linarith)
    have h2 : psiB (58 / 100) (8933565 / 10 ^ 7) xb ≤ psiB CB TB xb := by
      unfold psiB at hpl ⊢; linarith
    nlinarith
  have e1 : xb - 4 / 25 * psiB CB TB xb < 1 / 2 - 4 / 25 * (3 / 4) := by
    have := bnd (4 / 25) (by norm_num) (by norm_num)
    have h2 : hB (58 / 100) (8933565 / 10 ^ 7) (4 / 25) < 1 / 2 - 4 / 25 * (3 / 4) := by
      apply hB_lt <;> norm_num
    linarith
  have e2 : xb - 6 / 5 * psiB CB TB xb < 1 / 2 - 6 / 5 * (3 / 4) := by
    have := bnd (6 / 5) (by norm_num) (by norm_num)
    have h2 : hB (58 / 100) (8933565 / 10 ^ 7) (6 / 5) < 1 / 2 - 6 / 5 * (3 / 4) := by
      apply hB_lt <;> norm_num
    linarith
  have := affine_neg (A0 := xb - 1 / 2) (A1 := psiB CB TB xb - 3 / 4) hα hα'
    (by linarith) (by linarith)
  linarith

/-- (N4) large wait cost. -/
lemma G_neg_large (CB α : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (hα : 6 / 5 ≤ α) :
    G CB α < 0 := by
  have hα0 : 0 < α := by linarith
  have hCB0 := CB_pos CB hCB
  unfold G
  rw [OptD1 α hα0]
  have hpos := hD_pos α hα0
  have : OptB CB α 1 ≤ 0 := by
    apply csSup_le (neB1 CB α)
    rintro _ ⟨x, hx, rfl⟩
    rw [memB1] at hx
    rw [VB1 CB α x hx.1 hx.2]
    unfold psiB
    have h1 : 0 ≤ CB * x ^ 2 / (TB * (TB - x)) := by
      have : 0 < TB - x := by linarith [hx.2]
      have := TB_pos
      positivity
    have := TB_lt_one
    nlinarith [hx.2, hx.1]
  linarith

/-! ## Monotone stretch -/

lemma xD_le (α : ℝ) (hα : 11 / 100 ≤ α) : xD α ≤ 55 / 100 := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hS0, hS2⟩ := hDS α hα0
  set S := √(α * CD * (2 * TD + α * CD)) with hS
  unfold xD; rw [← hS]
  unfold CD TD at hS2 ⊢
  have h4 : 4 * S ≤ 15 * (α * (9 / 8)) := by
    by_contra h; have h := not_le.1 h; nlinarith
  have : 4 / 15 ≤ α * (9 / 8) / S := by
    rw [le_div_iff₀ hS0]; linarith
  nlinarith

lemma xB_ge (CB α : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (hα : 0 < α)
    (hα' : α ≤ 4 / 25) : 6 / 10 ≤ xB CB TB α := by
  have hCB0 := CB_pos CB hCB
  have hT := TB_bounds
  have hT0 := TB_pos
  obtain ⟨-, -, hR0, hR2, -⟩ := hBS CB TB α hCB0 hT0 hα (by linarith)
  set R := √(α * CB * (3 * TB + α * (3 * CB - TB))) with hR
  have h33 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  set w : ℝ := 1 - 6 / 10 / (8933563 / 10 ^ 7)
  have hw : w = 1 - 6 / 10 / (8933563 / 10 ^ 7) := rfl
  have hw0 : 0 < w := by norm_num [hw]
  -- 3 α CB ≤ w² Q
  have hac : α * CB ≤ 4 / 25 * (59 / 100) := mul_le_mul hα' hCB.2 hCB0.le (by norm_num)
  have htb : 8933563 / 10 ^ 7 * (3 - 4 / 25) ≤ TB * (3 - α) :=
    mul_le_mul hT.1.le (by linarith) (by norm_num) hT0.le
  have hkey : 3 * (α * CB) ≤ w ^ 2 * (3 * TB + α * (3 * CB - TB)) := by
    have : 3 * (α * CB) * (1 - w ^ 2) ≤ w ^ 2 * (TB * (3 - α)) := by
      have hw2 : 0 ≤ 1 - w ^ 2 := by norm_num [hw]
      calc 3 * (α * CB) * (1 - w ^ 2) ≤ 3 * (4 / 25 * (59 / 100)) * (1 - w ^ 2) := by gcongr
        _ ≤ w ^ 2 * (8933563 / 10 ^ 7 * (3 - 4 / 25)) := by norm_num [hw]
        _ ≤ w ^ 2 * (TB * (3 - α)) := by gcongr
    nlinarith
  have hle : Real.sqrt 3 * (α * CB) ≤ w * R := by
    rw [← abs_of_pos (by positivity : 0 < w * R),
      ← abs_of_pos (by positivity : 0 < Real.sqrt 3 * (α * CB))]
    apply sq_le_sq.1
    have e1 : (Real.sqrt 3 * (α * CB)) ^ 2 = 3 * (α * CB) ^ 2 := by rw [mul_pow, h33]
    have e2 : (w * R) ^ 2 = w ^ 2 * (α * CB * (3 * TB + α * (3 * CB - TB))) := by
      rw [mul_pow, hR2]
    rw [e1, e2]
    have := mul_pos hα hCB0
    have : 3 * (α * CB) ^ 2 = (α * CB) * (3 * (α * CB)) := by ring
    rw [this]
    calc (α * CB) * (3 * (α * CB)) ≤ (α * CB) * (w ^ 2 * (3 * TB + α * (3 * CB - TB))) := by
          gcongr
      _ = _ := by ring
  have hfrac : Real.sqrt 3 * (α * CB) / R ≤ w := by rw [div_le_iff₀ hR0]; linarith
  unfold xB; rw [← hR]
  have : 1 - w ≤ 1 - Real.sqrt 3 * (α * CB) / R := by linarith
  have h6 : 6 / 10 ≤ TB * (1 - w) := by
    rw [hw]; have : TB * (6 / 10 / (8933563 / 10 ^ 7)) ≥ 6 / 10 := by
      rw [ge_iff_le, ← mul_div_assoc, le_div_iff₀ (by norm_num)]; nlinarith
    nlinarith
  nlinarith

lemma G_strictAnti (CB α β : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB)
    (hα : 11 / 100 ≤ α) (hab : α < β) (hβ : β ≤ 4 / 25) : G CB β < G CB α := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hCB0 := CB_pos CB hCB
  unfold G
  -- batch
  obtain ⟨hmB, -, hvB⟩ := greatB1 CB β hCB0 hβ0 (by linarith)
  have hxB := memB1.1 hmB
  have hB1 : VinfB CB α 1 (xB CB TB β) ≤ OptB CB α 1 := OptB_ge CB α _ hCB hα0.le hmB
  rw [VB1 CB α _ hxB.1 hxB.2] at hB1
  rw [OptB1 CB β hCB0 hβ0 (by linarith), ← hvB, VB1 CB β _ hxB.1 hxB.2]
  -- dedicated
  obtain ⟨hmD, hgD, hvD⟩ := greatD1 α hα0
  have hxD := memD1.1 hmD
  have hD1 : VinfD β 1 (xD α) ≤ OptD β 1 := by
    rw [OptD1 β hβ0]; exact (greatD1 β hβ0).2.1.2 ⟨_, hmD, rfl⟩
  rw [VD1 β _ hxD.2] at hD1
  rw [OptD1 α hα0, ← hvD, VD1 α _ hxD.2]
  -- the two wait-cost bounds
  have hpsi : 1 / 2 + (6 / 10) / 3 + 58 / 100 * (6 / 10) ^ 2 /
      (8933565 / 10 ^ 7 * (8933565 / 10 ^ 7 - 6 / 10)) ≤ psiB CB TB (xB CB TB β) := by
    have hge := xB_ge CB β hCB hβ0 hβ
    have hl := psiB_lower CB _ hCB hxB.1 hxB.2
    have : 58 / 100 * (6 / 10) ^ 2 / (8933565 / 10 ^ 7 * (8933565 / 10 ^ 7 - 6 / 10)) ≤
        58 / 100 * (xB CB TB β) ^ 2 /
          (8933565 / 10 ^ 7 * (8933565 / 10 ^ 7 - xB CB TB β)) := by
      have : xB CB TB β < 8933565 / 10 ^ 7 := by linarith [TB_bounds.2]
      gcongr <;> linarith
    linarith
  have hphi : phiD (xD α) ≤ 3 / 4 * (55 / 100) ^ 2 / (3 / 4 - 55 / 100) := by
    have hle := xD_le α hα
    unfold phiD
    gcongr <;> linarith [xD_mem α hα0]
  have hnum : 3 / 4 * (55 / 100 : ℝ) ^ 2 / (3 / 4 - 55 / 100) < 1 / 2 + (6 / 10) / 3 +
      58 / 100 * (6 / 10) ^ 2 / (8933565 / 10 ^ 7 * (8933565 / 10 ^ 7 - 6 / 10)) := by norm_num
  nlinarith

lemma hD_cont : Continuous hD := by unfold hD; fun_prop

lemma hB_cont (C T : ℝ) : Continuous (hB C T) := by unfold hB; fun_prop

lemma single_crossing_core (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) :
    ∃ αs : ℝ, 11 / 100 < αs ∧ αs < 4 / 25 ∧ G CB αs = 0 ∧
      (∀ α : ℝ, 0 < α → α < αs → 0 < G CB α) ∧
      (∀ α : ℝ, αs < α → G CB α < 0) := by
  have hCB0 := CB_pos CB hCB
  have hcont : ContinuousOn (G CB) (Set.Icc (11 / 100) (4 / 25)) := by
    have : Set.EqOn (fun α => hB CB TB α - hD α) (G CB) (Set.Icc (11 / 100) (4 / 25)) := by
      intro α hα
      simp only [G]
      rw [OptB1 CB α hCB0 (by linarith [hα.1]) (by linarith [hα.2]),
        OptD1 α (by linarith [hα.1])]
    exact ((hB_cont CB TB).sub hD_cont).continuousOn.congr this.symm
  have ha := G_pos_mid CB (11 / 100) hCB (by norm_num) le_rfl
  have hb := G_neg_mid CB (4 / 25) hCB le_rfl (by norm_num)
  obtain ⟨αs, hαs, hz⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨hb.le, ha.le⟩
  have h1 : 11 / 100 < αs := by
    rcases eq_or_lt_of_le hαs.1 with h | h
    · rw [← h] at hz; linarith
    · exact h
  have h2 : αs < 4 / 25 := by
    rcases eq_or_lt_of_le hαs.2 with h | h
    · rw [h] at hz; linarith
    · exact h
  refine ⟨αs, h1, h2, hz, ?_, ?_⟩
  · intro α hα0 hα
    by_cases hs : α ≤ 1 / 200
    · exact G_pos_small CB α hCB hα0 hs
    by_cases hm : α ≤ 11 / 100
    · exact G_pos_mid CB α hCB (by linarith) hm
    have := G_strictAnti CB α αs hCB (by linarith) hα h2.le
    linarith
  · intro α hα
    by_cases hl : 6 / 5 ≤ α
    · exact G_neg_large CB α hCB hl
    by_cases hm : 4 / 25 ≤ α
    · exact G_neg_mid CB α hCB hm (by linarith)
    have := G_strictAnti CB αs α hCB h1.le hα (by linarith)
    linarith

end CD2Aux


open Filter Topology

namespace CD2Aux

/-! ## Attainment and uniqueness at general radius -/

lemma memD_scale (r lam : ℝ) (hr : 0 < r) : lam ∈ domD r ↔ lam * r ∈ domD 1 := by
  rw [memD1]; unfold domD; rw [muD_eq]; unfold TD
  rw [Set.mem_Ico, lt_div_iff₀ hr]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by positivity, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, h2⟩

lemma memB_scale (r lam : ℝ) (hr : 0 < r) : lam ∈ domB r ↔ lam * r ∈ domB 1 := by
  have h2mu : 2 * muB r = TB / r := by rw [muB_eq r hr.ne']; field_simp
  rw [memB1]; unfold domB; rw [h2mu]
  rw [Set.mem_Ioo, lt_div_iff₀ hr]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by positivity, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, h2⟩

lemma VinfD_scale (c r lam : ℝ) (hr : 0 < r) (hl : lam ∈ domD r) :
    VinfD c r lam = (1 / r) * VinfD (c * r) 1 (lam * r) := by
  have h1 := memD1.1 ((memD_scale r lam hr).1 hl)
  rw [VinfD_eq c r lam hr hl.2, VD1 _ _ h1.2]

lemma VinfB_scale (CB c r lam : ℝ) (hr : 0 < r) (hl : lam ∈ domB r) :
    VinfB CB c r lam = (1 / r) * VinfB CB (c * r) 1 (lam * r) := by
  have h1 := memB1.1 ((memB_scale r lam hr).1 hl)
  rw [VinfB_eq CB c r lam hr hl.1 hl.2, VB1 _ _ _ h1.1 h1.2]

lemma attD (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    xD (c * r) / r ∈ domD r ∧ VinfD c r (xD (c * r) / r) = OptD c r := by
  have hα : 0 < c * r := mul_pos hc hr
  obtain ⟨hm, -, hv⟩ := greatD1 (c * r) hα
  have hm' : xD (c * r) / r ∈ domD r := by
    rw [memD_scale _ _ hr, div_mul_cancel₀ _ hr.ne']; exact hm
  refine ⟨hm', ?_⟩
  rw [VinfD_scale c r _ hr hm', div_mul_cancel₀ _ hr.ne', hv, OptD_scale c r hr, OptD1 _ hα]

lemma attB (CB c r : ℝ) (hCB : 0 < CB) (hc : 0 < c) (hr : 0 < r) (h3 : c * r < 3) :
    xB CB TB (c * r) / r ∈ domB r ∧ VinfB CB c r (xB CB TB (c * r) / r) = OptB CB c r := by
  have hα : 0 < c * r := mul_pos hc hr
  obtain ⟨hm, -, hv⟩ := greatB1 CB (c * r) hCB hα h3
  have hm' : xB CB TB (c * r) / r ∈ domB r := by
    rw [memB_scale _ _ hr, div_mul_cancel₀ _ hr.ne']; exact hm
  refine ⟨hm', ?_⟩
  rw [VinfB_scale CB c r _ hr hm', div_mul_cancel₀ _ hr.ne', hv, OptB_scale CB c r hr,
    OptB1 CB _ hCB hα h3]

lemma uniqD (c r lam : ℝ) (hc : 0 < c) (hr : 0 < r) (hl : lam ∈ domD r)
    (hv : VinfD c r lam = OptD c r) : lam * r = xD (c * r) := by
  rw [VinfD_scale c r lam hr hl, OptD_scale c r hr] at hv
  have hv' : VinfD (c * r) 1 (lam * r) = OptD (c * r) 1 := by
    have : (1 / r) ≠ 0 := by positivity
    exact mul_left_cancel₀ this hv
  exact OptD1_unique _ _ (mul_pos hc hr) ((memD_scale r lam hr).1 hl) hv'

lemma uniqB (CB c r lam : ℝ) (hCB : 0 < CB) (hc : 0 < c) (hr : 0 < r) (h3 : c * r < 3)
    (hl : lam ∈ domB r) (hv : VinfB CB c r lam = OptB CB c r) : lam * r = xB CB TB (c * r) := by
  rw [VinfB_scale CB c r lam hr hl, OptB_scale CB c r hr] at hv
  have hv' : VinfB CB (c * r) 1 (lam * r) = OptB CB (c * r) 1 := by
    have : (1 / r) ≠ 0 := by positivity
    exact mul_left_cancel₀ this hv
  exact OptB1_unique CB _ _ hCB (mul_pos hc hr) h3 ((memB_scale r lam hr).1 hl) hv'

/-! ## Sign of the revenue gap -/

def CoreProp (CB αs : ℝ) : Prop :=
  11 / 100 < αs ∧ αs < 4 / 25 ∧ G CB αs = 0 ∧
    (∀ α : ℝ, 0 < α → α < αs → 0 < G CB α) ∧ (∀ α : ℝ, αs < α → G CB α < 0)

lemma sign_iff (CB αs : ℝ) (h : CoreProp CB αs) (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    (OptD c r < OptB CB c r ↔ c * r < αs) ∧ (OptB CB c r < OptD c r ↔ αs < c * r) := by
  obtain ⟨-, -, h0, hlt, hgt⟩ := h
  have hG := G_scale CB c r hr
  have hα : 0 < c * r := mul_pos hc hr
  have e1 : OptD c r < OptB CB c r ↔ 0 < G CB (c * r) := by
    rw [← hG]; constructor
    · intro h; exact mul_pos hr (by linarith)
    · intro h; have := (pos_iff_pos_of_mul_pos h).1 hr; linarith
  have e2 : OptB CB c r < OptD c r ↔ G CB (c * r) < 0 := by
    rw [← hG]; constructor
    · intro h; exact mul_neg_of_pos_of_neg hr (by linarith)
    · intro h
      by_contra hn
      have : 0 ≤ r * (OptB CB c r - OptD c r) := mul_nonneg hr.le (by linarith)
      linarith
  rw [e1, e2]
  constructor
  · constructor
    · intro hp
      rcases lt_trichotomy (c * r) αs with h | h | h
      · exact h
      · rw [h] at hp; linarith
      · linarith [hgt _ h]
    · intro h; exact hlt _ hα h
  · constructor
    · intro hp
      rcases lt_trichotomy (c * r) αs with h | h | h
      · linarith [hlt _ hα h]
      · rw [h] at hp; linarith
      · exact h
    · intro h; exact hgt _ h

/-! ## Continuity of the closed forms -/

lemma xB_contAt (C T a : ℝ) (h : 0 < a * C * (3 * T + a * (3 * C - T))) :
    ContinuousAt (xB C T) a := by
  unfold xB
  apply ContinuousAt.mul continuousAt_const
  apply ContinuousAt.sub continuousAt_const
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (Real.sqrt_pos.2 h).ne'

lemma xD_contAt (a : ℝ) (h : 0 < a * CD * (2 * TD + a * CD)) : ContinuousAt xD a := by
  unfold xD
  apply ContinuousAt.mul continuousAt_const
  apply ContinuousAt.sub continuousAt_const
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (Real.sqrt_pos.2 h).ne'

/-! ## Generic switch -/

lemma exists_sel (CB αs : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (h : CoreProp CB αs)
    (cf rf : ℝ → ℝ) (hpos : ∀ t, 0 < t → 0 < cf t ∧ 0 < rf t) :
    ∃ ls : ℝ → ℝ, ∀ t, 0 < t → IsOptDemand CB (cf t) (rf t) (ls t) := by
  refine ⟨fun t => if OptD (cf t) (rf t) < OptB CB (cf t) (rf t) then
    xB CB TB (cf t * rf t) / rf t else xD (cf t * rf t) / rf t, ?_⟩
  intro t ht
  obtain ⟨hc, hr⟩ := hpos t ht
  dsimp only
  unfold IsOptDemand
  split_ifs with hs
  · have h3 : cf t * rf t < 3 := by
      have := ((sign_iff CB αs h _ _ hc hr).1).1 hs; linarith [h.2.1]
    exact attB CB _ _ (CB_pos CB hCB) hc hr h3
  · exact attD _ _ hc hr

lemma jump_gen (CB αs : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (h : CoreProp CB αs)
    (cf rf : ℝ → ℝ) (t0 : ℝ) (ht0 : 0 < t0)
    (hpos : ∀ t, 0 < t → 0 < cf t ∧ 0 < rf t)
    (hlt : ∀ t, 0 < t → t < t0 → cf t * rf t < αs) (hgt : ∀ t, t0 < t → αs < cf t * rf t)
    (hat : cf t0 * rf t0 = αs) (hcf : Continuous cf) (hrf : Continuous rf)
    (ls : ℝ → ℝ) (hls : ∀ t, 0 < t → IsOptDemand CB (cf t) (rf t) (ls t)) :
    ∃ L R PL PR : ℝ, R < L ∧ PL < PR ∧
      Tendsto ls (𝓝[<] t0) (𝓝 L) ∧ Tendsto ls (𝓝[>] t0) (𝓝 R) ∧
      Tendsto (fun t => optPrice CB (cf t) (rf t) (ls t)) (𝓝[<] t0) (𝓝 PL) ∧
      Tendsto (fun t => optPrice CB (cf t) (rf t) (ls t)) (𝓝[>] t0) (𝓝 PR) := by
  have hCB0 := CB_pos CB hCB
  obtain ⟨hs1, hs2, hG0, -, -⟩ := id h
  have hαs0 : 0 < αs := by linarith
  have hr0 : 0 < rf t0 := (hpos t0 ht0).2
  -- the left side: batch
  have left : ∀ t ∈ Set.Ioo 0 t0, ls t = xB CB TB (cf t * rf t) / rf t ∧
      optPrice CB (cf t) (rf t) (ls t) = hB CB TB (cf t * rf t) / xB CB TB (cf t * rf t) := by
    rintro t ⟨ht, ht'⟩
    obtain ⟨hc, hr⟩ := hpos t ht
    have hα := hlt t ht ht'
    have h3 : cf t * rf t < 3 := by linarith
    have hs : OptD (cf t) (rf t) < OptB CB (cf t) (rf t) :=
      ((sign_iff CB αs h _ _ hc hr).1).2 hα
    have hsel := hls t ht
    unfold IsOptDemand at hsel; rw [if_pos hs] at hsel
    have hu := uniqB CB _ _ _ hCB0 hc hr h3 hsel.1 hsel.2
    have hl : ls t = xB CB TB (cf t * rf t) / rf t := by rw [← hu]; field_simp
    refine ⟨hl, ?_⟩
    unfold optPrice; rw [if_pos hs]
    have hv := hsel.2
    have hxpos := (xB_mem CB TB _ hCB0 TB_pos (mul_pos hc hr) h3).1
    have hlpos : 0 < ls t := by rw [hl]; positivity
    unfold VinfB Vinf at hv
    rw [OptB_scale CB _ _ hr, OptB1 CB _ hCB0 (mul_pos hc hr) h3] at hv
    rw [hl] at hv
    field_simp at hv
    rw [hl]
    field_simp
    linarith
  have right : ∀ t ∈ Set.Ioi t0, ls t = xD (cf t * rf t) / rf t ∧
      optPrice CB (cf t) (rf t) (ls t) = hD (cf t * rf t) / xD (cf t * rf t) := by
    intro t ht
    have ht' : 0 < t := lt_trans ht0 ht
    obtain ⟨hc, hr⟩ := hpos t ht'
    have hα := hgt t ht
    have hs : ¬ OptD (cf t) (rf t) < OptB CB (cf t) (rf t) := by
      have := ((sign_iff CB αs h _ _ hc hr).2).2 hα; intro h'; linarith
    have hsel := hls t ht'
    unfold IsOptDemand at hsel; rw [if_neg hs] at hsel
    have hu := uniqD _ _ _ hc hr hsel.1 hsel.2
    have hl : ls t = xD (cf t * rf t) / rf t := by rw [← hu]; field_simp
    refine ⟨hl, ?_⟩
    unfold optPrice; rw [if_neg hs]
    have hv := hsel.2
    have hxpos := (xD_mem _ (mul_pos hc hr)).1
    unfold VinfD Vinf at hv
    rw [OptD_scale _ _ hr, OptD1 _ (mul_pos hc hr)] at hv
    rw [hl] at hv
    field_simp at hv
    rw [hl]
    field_simp
    linarith
  -- continuity
  have hαc : Continuous fun t => cf t * rf t := hcf.mul hrf
  have hQ : 0 < αs * CB * (3 * TB + αs * (3 * CB - TB)) := by
    have := batchQ_pos CB TB αs hCB0 TB_pos hαs0 (by linarith); positivity
  have hQD : 0 < αs * CD * (2 * TD + αs * CD) := by unfold CD TD; positivity
  have cxB : ContinuousAt (fun t => xB CB TB (cf t * rf t)) t0 := by
    apply ContinuousAt.comp (g := xB CB TB) _ hαc.continuousAt
    rw [hat]; exact xB_contAt CB TB αs hQ
  have cxD : ContinuousAt (fun t => xD (cf t * rf t)) t0 := by
    apply ContinuousAt.comp (g := xD) _ hαc.continuousAt
    rw [hat]; exact xD_contAt αs hQD
  have hxBs := xB_mem CB TB αs hCB0 TB_pos hαs0 (by linarith)
  have hxDs := xD_mem αs hαs0
  have hxB0 : xB CB TB (cf t0 * rf t0) ≠ 0 := by rw [hat]; exact hxBs.1.ne'
  have hxD0 : xD (cf t0 * rf t0) ≠ 0 := by rw [hat]; exact hxDs.1.ne'
  have cL : ContinuousAt (fun t => xB CB TB (cf t * rf t) / rf t) t0 :=
    cxB.div hrf.continuousAt hr0.ne'
  have cR : ContinuousAt (fun t => xD (cf t * rf t) / rf t) t0 :=
    cxD.div hrf.continuousAt hr0.ne'
  have cPL : ContinuousAt (fun t => hB CB TB (cf t * rf t) / xB CB TB (cf t * rf t)) t0 :=
    ((hB_cont CB TB).comp hαc).continuousAt.div cxB hxB0
  have cPR : ContinuousAt (fun t => hD (cf t * rf t) / xD (cf t * rf t)) t0 :=
    (hD_cont.comp hαc).continuousAt.div cxD hxD0
  -- values
  have hxle : xD αs ≤ 55 / 100 := xD_le αs hs1.le
  have hxge : 6 / 10 ≤ xB CB TB αs := xB_ge CB αs hCB hαs0 hs2.le
  have hvals : hB CB TB αs = hD αs := by
    unfold G at hG0
    rw [OptB1 CB αs hCB0 hαs0 (by linarith), OptD1 αs hαs0] at hG0; linarith
  have hDp := hD_pos αs hαs0
  refine ⟨xB CB TB αs / rf t0, xD αs / rf t0, hB CB TB αs / xB CB TB αs,
    hD αs / xD αs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply div_lt_div_of_pos_right _ hr0; linarith
  · rw [hvals]; apply div_lt_div_of_pos_left hDp hxDs.1; linarith
  · have := cL.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio t0))
    simp only [hat] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht0] with t ht
    exact (left t ht).1.symm
  · have := cR.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi t0))
    simp only [hat] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (right t ht).1.symm
  · have := cPL.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio t0))
    simp only [hat] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht0] with t ht
    exact (left t ht).2.symm
  · have := cPR.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi t0))
    simp only [hat] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (right t ht).2.symm

lemma main_core (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) :
    ∃ αs : ℝ, 0 < αs ∧
      (∀ c r : ℝ, 0 < c → 0 < r →
        (OptD c r < OptB CB c r ↔ c * r < αs) ∧
        (OptB CB c r < OptD c r ↔ αs < c * r)) ∧
      (∀ r : ℝ, 0 < r → CostJump CB r (αs / r)) ∧
      (∀ c : ℝ, 0 < c → RadiusJump CB c (αs / c)) := by
  obtain ⟨αs, h1, h2, h3, h4, h5⟩ := single_crossing_core CB hCB
  have h : CoreProp CB αs := ⟨h1, h2, h3, h4, h5⟩
  have hαs0 : 0 < αs := by linarith
  refine ⟨αs, hαs0, fun c r hc hr => sign_iff CB αs h c r hc hr, ?_, ?_⟩
  · intro r hr
    have hpos : ∀ t : ℝ, 0 < t → 0 < (fun c : ℝ => c) t ∧ 0 < (fun _ => r) t := fun t ht => ⟨ht, hr⟩
    refine ⟨exists_sel CB αs hCB h (fun c => c) (fun _ => r) hpos, ?_⟩
    intro ls hls
    exact jump_gen CB αs hCB h (fun c => c) (fun _ => r) (αs / r) (by positivity) hpos
      (fun t _ ht => by rwa [lt_div_iff₀ hr] at ht)
      (fun t ht => by rwa [div_lt_iff₀ hr] at ht)
      (by field_simp) continuous_id continuous_const ls hls
  · intro c hc
    have hpos : ∀ t : ℝ, 0 < t → 0 < (fun _ : ℝ => c) t ∧ 0 < (fun r => r) t := fun t ht => ⟨hc, ht⟩
    refine ⟨exists_sel CB αs hCB h (fun _ => c) (fun r => r) hpos, ?_⟩
    intro ls hls
    exact jump_gen CB αs hCB h (fun _ => c) (fun r => r) (αs / c) (by positivity) hpos
      (fun t _ ht => by rw [lt_div_iff₀ hc] at ht; linarith)
      (fun t ht => by rw [div_lt_iff₀ hc] at ht; linarith)
      (by field_simp) continuous_const continuous_id ls hls

end CD2Aux




namespace CD2Aux

lemma ms_dedicated_optimum (c r : ℝ) (hc : 0 < c) (hr : 0 < r)
    (hsmall : c * r < CourierDispatch.Exogenous.TB) :
    let lF := CourierDispatch.Exogenous.TD / r * (1 - c * r * CourierDispatch.Exogenous.CD / Real.sqrt (c * r * CourierDispatch.Exogenous.CD * (2 * CourierDispatch.Exogenous.TD + c * r * CourierDispatch.Exogenous.CD)))
    lF ∈ CourierDispatch.Endogenous.domD r ∧
    IsGreatest (CourierDispatch.Endogenous.VinfD c r '' CourierDispatch.Endogenous.domD r) (CourierDispatch.Endogenous.VinfD c r lF) ∧
    CourierDispatch.Endogenous.VinfD c r lF = c * CourierDispatch.Exogenous.CD + CourierDispatch.Exogenous.TD / r - 1 / r * Real.sqrt (c * r * CourierDispatch.Exogenous.CD * (2 * CourierDispatch.Exogenous.TD + c * r * CourierDispatch.Exogenous.CD)) := by
  intro lF
  have hlF : lF = xD (c * r) / r := by simp only [lF, xD]; ring
  obtain ⟨hm, hv⟩ := attD c r hc hr
  rw [← hlF] at hm hv
  refine ⟨hm, ⟨⟨lF, hm, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨lam, hl, rfl⟩
    rw [hv, OptD_scale c r hr, OptD1 _ (mul_pos hc hr), VinfD_scale c r lam hr hl]
    have := (greatD1 _ (mul_pos hc hr)).2.1.2 ⟨_, (memD_scale r lam hr).1 hl, rfl⟩
    have : 0 < 1 / r := by positivity
    gcongr
  · rw [hv, OptD_scale c r hr, OptD1 _ (mul_pos hc hr)]
    unfold hD; field_simp


lemma ms_batch_optimum (CB c r : ℝ) (hCB : 0 < CB) (hc : 0 < c) (hr : 0 < r)
    (hsmall : c * r < CourierDispatch.Exogenous.TB) :
    let lB := CourierDispatch.Exogenous.TB / r *
      (1 - Real.sqrt 3 * (c * r * CB) /
        Real.sqrt (c * r * CB * (3 * CourierDispatch.Exogenous.TB + c * r * (3 * CB - CourierDispatch.Exogenous.TB))))
    lB ∈ CourierDispatch.Endogenous.domB r ∧
    IsGreatest (CourierDispatch.Endogenous.VinfB CB c r '' CourierDispatch.Endogenous.domB r) (CourierDispatch.Endogenous.VinfB CB c r lB) ∧
    CourierDispatch.Endogenous.VinfB CB c r lB =
      c * (2 * CB - 1 / 2 - CourierDispatch.Exogenous.TB / 3) + CourierDispatch.Exogenous.TB / r -
        2 / (3 * r) * Real.sqrt (3 * c * r * CB * (3 * CourierDispatch.Exogenous.TB + c * r * (3 * CB - CourierDispatch.Exogenous.TB))) := by
  intro lB
  have h3 : c * r < 3 := by linarith [TB_lt_one]
  have hα := mul_pos hc hr
  have hlB : lB = xB CB TB (c * r) / r := by simp only [lB, xB]; ring
  obtain ⟨hm, hv⟩ := attB CB c r hCB hc hr h3
  rw [← hlB] at hm hv
  refine ⟨hm, ⟨⟨lB, hm, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨lam, hl, rfl⟩
    rw [hv, OptB_scale CB c r hr, OptB1 CB _ hCB hα h3, VinfB_scale CB c r lam hr hl]
    have := (greatB1 CB _ hCB hα h3).2.1.2 ⟨_, (memB_scale r lam hr).1 hl, rfl⟩
    have : 0 < 1 / r := by positivity
    gcongr
  · rw [hv, OptB_scale CB c r hr, OptB1 CB _ hCB hα h3]
    unfold hB
    rw [show 3 * (c * r) * CB * (3 * TB + c * r * (3 * CB - TB)) =
      3 * c * r * CB * (3 * TB + c * r * (3 * CB - TB)) by ring]
    field_simp

lemma ms_single_crossing (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) :
    (∀ c r : ℝ, 0 < c → 0 < r →
      r * (CourierDispatch.Endogenous.OptB CB c r - CourierDispatch.Endogenous.OptD c r) = CourierDispatch.Endogenous.G CB (c * r)) ∧
    ∃ αs : ℝ, 0 < αs ∧ CourierDispatch.Endogenous.G CB αs = 0 ∧
      (∀ α : ℝ, 0 < α → α < αs → 0 < CourierDispatch.Endogenous.G CB α) ∧
      (∀ α : ℝ, αs < α → CourierDispatch.Endogenous.G CB α < 0) := by
  refine ⟨fun c r _ hr => G_scale CB c r hr, ?_⟩
  obtain ⟨αs, h1, -, h3, h4, h5⟩ := single_crossing_core CB hCB
  exact ⟨αs, by linarith, h3, h4, h5⟩

lemma ms_demand_drop_at_switch (CB c r lB lF : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB)
    (hc : 0 < c) (hr : 0 < r) (htie : CourierDispatch.Endogenous.OptB CB c r = CourierDispatch.Endogenous.OptD c r)
    (hB : lB ∈ CourierDispatch.Endogenous.domB r ∧ CourierDispatch.Endogenous.VinfB CB c r lB = CourierDispatch.Endogenous.OptB CB c r)
    (hF : lF ∈ CourierDispatch.Endogenous.domD r ∧ CourierDispatch.Endogenous.VinfD c r lF = CourierDispatch.Endogenous.OptD c r) :
    lF < lB := by
  obtain ⟨αs, h1, h2, h3, h4, h5⟩ := single_crossing_core CB hCB
  have hα := mul_pos hc hr
  have hG : G CB (c * r) = 0 := by rw [← G_scale CB c r hr, htie]; ring
  have heq : c * r = αs := by
    rcases lt_trichotomy (c * r) αs with h | h | h
    · linarith [h4 _ hα h]
    · exact h
    · linarith [h5 _ h]
  have h3' : c * r < 3 := by linarith
  have hb := uniqB CB c r lB (CB_pos CB hCB) hc hr h3' hB.1 hB.2
  have hf := uniqD c r lF hc hr hF.1 hF.2
  have e1 := xD_le (c * r) (by linarith)
  have e2 := xB_ge CB (c * r) hCB hα (by linarith)
  have : lF * r < lB * r := by linarith
  exact lt_of_mul_lt_mul_right this hr.le

lemma ms_proposition_3 (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (r : ℝ) (hr : 0 < r) :
    ∃ cinf : ℝ, 0 < cinf ∧
      (∀ c : ℝ, 0 < c →
        (CourierDispatch.Endogenous.OptD c r < CourierDispatch.Endogenous.OptB CB c r ↔ c < cinf) ∧
        (CourierDispatch.Endogenous.OptB CB c r < CourierDispatch.Endogenous.OptD c r ↔ cinf < c)) ∧
      CourierDispatch.Endogenous.CostJump CB r cinf := by
  obtain ⟨αs, h0, hs, hc, -⟩ := main_core CB hCB
  refine ⟨αs / r, by positivity, fun c hc' => ?_, hc r hr⟩
  rw [(hs c r hc' hr).1, (hs c r hc' hr).2, lt_div_iff₀ hr, div_lt_iff₀ hr]; exact ⟨Iff.rfl, Iff.rfl⟩

lemma ms_proposition_4 (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (c : ℝ) (hc : 0 < c) :
    ∃ rinf : ℝ, 0 < rinf ∧
      (∀ r : ℝ, 0 < r →
        (CourierDispatch.Endogenous.OptD c r < CourierDispatch.Endogenous.OptB CB c r ↔ r < rinf) ∧
        (CourierDispatch.Endogenous.OptB CB c r < CourierDispatch.Endogenous.OptD c r ↔ rinf < r)) ∧
      CourierDispatch.Endogenous.RadiusJump CB c rinf := by
  obtain ⟨αs, h0, hs, -, hr⟩ := main_core CB hCB
  refine ⟨αs / c, by positivity, fun r hr' => ?_, hr c hc⟩
  rw [(hs c r hc hr').1, (hs c r hc hr').2, lt_div_iff₀ hc, div_lt_iff₀ hc, mul_comm r c]; exact ⟨Iff.rfl, Iff.rfl⟩

end CD2Aux

theorem solution (CB c r : ℝ) (hCB : 0 < CB) (hc : 0 < c) (hr : 0 < r)
    (hsmall : c * r < CourierDispatch.Exogenous.TB) :
    let lB := CourierDispatch.Exogenous.TB / r *
      (1 - Real.sqrt 3 * (c * r * CB) /
        Real.sqrt (c * r * CB * (3 * CourierDispatch.Exogenous.TB + c * r * (3 * CB - CourierDispatch.Exogenous.TB))))
    lB ∈ domB r ∧
    IsGreatest (VinfB CB c r '' domB r) (VinfB CB c r lB) ∧
    VinfB CB c r lB =
      c * (2 * CB - 1 / 2 - CourierDispatch.Exogenous.TB / 3) + CourierDispatch.Exogenous.TB / r -
        2 / (3 * r) * Real.sqrt (3 * c * r * CB * (3 * CourierDispatch.Exogenous.TB + c * r * (3 * CB - CourierDispatch.Exogenous.TB))) := by
  exact CD2Aux.ms_batch_optimum CB c r hCB hc hr hsmall
