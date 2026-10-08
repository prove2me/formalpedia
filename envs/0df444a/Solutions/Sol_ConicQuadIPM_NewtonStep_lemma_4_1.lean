-- Prove2me | solution 1 for ConicQuadIPM.NewtonStep.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T04:00:58.518428+00:00
-- url     : https://prove2.me/submissions/ceb3fc65-122a-4455-bb85-3e9ecc1fc075

import Definitions.Def_ConicQuadIPM_NewtonStep_Setting
import Mathlib

namespace P2MInline_Eq25

open Matrix ConicQuadIPM.NewtonStep

theorem proof
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    (∑ i, A i *ᵥ ((1 - γ) • x0 i + dx i)) - ((1 - γ) * τ0 + dτ) • b = 0 ∧
    (∀ i, (A i)ᵀ *ᵥ ((1 - γ) • y0 + dy) + ((1 - γ) • s0 i + ds i)
        - ((1 - γ) * τ0 + dτ) • c i = 0) ∧
    -(∑ i, c i ⬝ᵥ ((1 - γ) • x0 i + dx i)) + b ⬝ᵥ ((1 - γ) • y0 + dy)
        - ((1 - γ) * κ0 + dκ) = 0 := by
  rcases h22 with ⟨hprimal, hdual, hgap, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [mulVec_add, mulVec_smul]
    ext j
    have hj := congrFun hprimal j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      Finset.sum_apply] at hj ⊢
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [hj]
  · intro i
    simp only [mulVec_add, mulVec_smul]
    ext j
    have hj := congrFun (hdual i) j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hj ⊢
    nlinarith [hj]
  · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [hgap]

end P2MInline_Eq25

namespace P2MInline_Eq26

open Matrix ConicQuadIPM.NewtonStep

private lemma homogeneous_gap {m k : ℕ} {n : Fin k → ℕ}
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c x s : (i : Fin k) → Fin (n i) → ℝ) (y : Fin m → ℝ) (τ κ : ℝ)
    (hp : (∑ i, A i *ᵥ x i) - τ • b = 0)
    (hd : ∀ i, (A i)ᵀ *ᵥ y + s i - τ • c i = 0)
    (hg : -(∑ i, c i ⬝ᵥ x i) + b ⬝ᵥ y - κ = 0) :
    0 = (∑ i, x i ⬝ᵥ s i) + τ * κ := by
  have hblock : ∀ i, x i ⬝ᵥ s i =
      τ * (c i ⬝ᵥ x i) - y ⬝ᵥ (A i *ᵥ x i) := by
    intro i
    have hi := congrArg (fun v => x i ⬝ᵥ v) (hd i)
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul,
      dotProduct_zero, dotProduct_transpose_mulVec, dotProduct_comm (x i) (c i)] at hi
    linarith
  have hpr := congrArg (fun v => y ⬝ᵥ v) hp
  simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul,
    dotProduct_zero, dotProduct_comm y b] at hpr
  simp_rw [hblock]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hgm := congrArg (fun z : ℝ => τ * z) hg
  nlinarith [hpr, hgm]
theorem proof
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    0 = (∑ i, ((1 - γ) • x0 i + dx i) ⬝ᵥ ((1 - γ) • s0 i + ds i))
          + ((1 - γ) * τ0 + dτ) * ((1 - γ) * κ0 + dκ) ∧
    (∑ i, ((1 - γ) • x0 i + dx i) ⬝ᵥ ((1 - γ) • s0 i + ds i))
          + ((1 - γ) * τ0 + dτ) * ((1 - γ) * κ0 + dκ)
      = (1 - γ) ^ 2 * ((∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0)
        + (1 - γ) * ((∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i) + τ0 * dκ + κ0 * dτ)
        + ((∑ i, dx i ⬝ᵥ ds i) + dτ * dκ) := by
  obtain ⟨hp, hd, hg⟩ := _root_.P2MInline_Eq25.proof kind n hwf A b c x0 τ0 y0 s0 κ0 γ hγ dx dτ dy ds dκ h22
  constructor
  · exact homogeneous_gap A b c (fun i => (1 - γ) • x0 i + dx i)
      (fun i => (1 - γ) • s0 i + ds i) ((1 - γ) • y0 + dy)
      ((1 - γ) * τ0 + dτ) ((1 - γ) * κ0 + dκ) hp hd hg
  · simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm (dx _) (s0 _), Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

end P2MInline_Eq26

namespace P2MInline_Eq61

open Matrix ConicQuadIPM.Complementarity

private lemma first_dot {d : ℕ} (v : Fin (d + 1) → ℝ) : e1 ⬝ᵥ v = v 0 := by
  simp [e1, dotProduct, Fin.sum_univ_succ]

private lemma arrow_first {d : ℕ} (v w : Fin d → ℝ) :
    e1 ⬝ᵥ (arrow v *ᵥ w) = v ⬝ᵥ w := by
  cases d with
  | zero => simp [dotProduct]
  | succ d =>
      rw [first_dot]
      simp [mulVec, dotProduct, arrow]

private lemma arrow_unit {d : ℕ} (v : Fin d → ℝ) : arrow v *ᵥ e1 = v := by
  cases d with
  | zero => ext i; exact Fin.elim0 i
  | succ d =>
      ext i
      by_cases hi : i = 0
      · subst i
        simp [mulVec, dotProduct, arrow, e1, Fin.sum_univ_succ]
      · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp [mulVec, dotProduct, arrow, e1, Fin.sum_univ_succ, hiv]

private lemma arrow_product {d : ℕ} (v w : Fin d → ℝ) :
    e1 ⬝ᵥ ((arrow v * arrow w) *ᵥ e1) = v ⬝ᵥ w := by
  rw [← mulVec_mulVec, arrow_unit, arrow_first]

private lemma rot_zero (d : ℕ) (v : Fin (d + 2) → ℝ) :
    (Tmat .rot (d + 2) *ᵥ v) 0 =
      (1 / Real.sqrt 2) * v 0 + (1 / Real.sqrt 2) * v (Fin.succ 0) := by
  have hz (i : Fin d) : (0 : Fin (d + 2)) ≠ i.succ.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  simp [mulVec, dotProduct, Tmat, Fin.sum_univ_succ, hz]

private lemma rot_one (d : ℕ) (v : Fin (d + 2) → ℝ) :
    (Tmat .rot (d + 2) *ᵥ v) (Fin.succ 0) =
      (1 / Real.sqrt 2) * v 0 - (1 / Real.sqrt 2) * v (Fin.succ 0) := by
  have h1 (i : Fin d) : (1 : Fin (d + 2)) ≠ i.succ.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_one, Fin.val_succ] at hv
    omega
  simp [mulVec, dotProduct, Tmat, Fin.sum_univ_succ, sub_eq_add_neg, h1]

private lemma rot_tail (d : ℕ) (v : Fin (d + 2) → ℝ) (i : Fin d) :
    (Tmat .rot (d + 2) *ᵥ v) i.succ.succ = v i.succ.succ := by
  simp [mulVec, dotProduct, Tmat, ite_mul]

private lemma rot_dot {d : ℕ} (hd : 2 ≤ d) (v w : Fin d → ℝ) :
    (Tmat .rot d *ᵥ v) ⬝ᵥ (Tmat .rot d *ᵥ w) = v ⬝ᵥ w := by
  obtain ⟨q, rfl⟩ : ∃ q, d = q + 2 := ⟨d - 2, by omega⟩
  have hscale : 2 * (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp only [dotProduct, Fin.sum_univ_succ, rot_zero, rot_one, rot_tail]
  linear_combination (v 0 * w 0 + v (Fin.succ 0) * w (Fin.succ 0)) * hscale

private lemma transformed_dot {d : ℕ} (c : ConeKind) (hwf : BlockWF c d)
    (v w : Fin d → ℝ) : (Tmat c d *ᵥ v) ⬝ᵥ (Tmat c d *ᵥ w) = v ⬝ᵥ w := by
  cases c with
  | nonneg => simp [Tmat]
  | quad => simp [Tmat]
  | rot => exact rot_dot (hwf.2.2 rfl) v w

theorem proof
    {k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (x s : (i : Fin k) → Fin (n i) → ℝ) :
    (∑ i, ConicQuadIPM.Complementarity.e1 ⬝ᵥ ((ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x i) * ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s i))
        *ᵥ ConicQuadIPM.Complementarity.e1))
      = ∑ i, (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s i) ∧
    (∑ i, (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s i))
      = ∑ i, x i ⬝ᵥ s i := by
  constructor
  · exact Finset.sum_congr rfl fun i hi => arrow_product _ _
  · exact Finset.sum_congr rfl fun i hi => transformed_dot (kind i) (hwf i) _ _

end P2MInline_Eq61

namespace P2MInline_First

open Matrix ConicQuadIPM.Complementarity

private lemma first_dot {d : ℕ} (v : Fin (d + 1) → ℝ) : e1 ⬝ᵥ v = v 0 := by
  simp [e1, dotProduct, Fin.sum_univ_succ]

private lemma arrow_first {d : ℕ} (v w : Fin d → ℝ) :
    e1 ⬝ᵥ (arrow v *ᵥ w) = v ⬝ᵥ w := by
  cases d with
  | zero => simp [dotProduct]
  | succ d =>
      rw [first_dot]
      simp [mulVec, dotProduct, arrow]

theorem proof
    {k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (x0 s0 dx ds : (i : Fin k) → Fin (n i) → ℝ) (τ0 κ0 dτ dκ : ℝ) :
    (∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i) + τ0 * dκ + κ0 * dτ
      = (∑ i, ConicQuadIPM.Complementarity.e1 ⬝ᵥ (ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x0 i) *ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ ds i)
            + ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s0 i) *ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ dx i)))
        + τ0 * dκ + κ0 * dτ := by
  simp_rw [dotProduct_add, arrow_first]
  rw [Finset.sum_add_distrib,
    (_root_.P2MInline_Eq61.proof kind n hwf x0 ds).2,
    (_root_.P2MInline_Eq61.proof kind n hwf s0 dx).2]

end P2MInline_First

namespace P2MInline_Chain

set_option autoImplicit false
open Matrix ConicQuadIPM.Complementarity ConicQuadIPM.NewtonStep

private theorem block_dim_pos {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (i : Fin k) : 0 < n i := by
  cases hkind : kind i with
  | nonneg => have h := (hwf i).1 hkind; omega
  | quad => exact (hwf i).2.1 hkind
  | rot => have h := (hwf i).2.2 hkind; omega

private theorem e1_dot_self {d : ℕ} (hd : 0 < d) :
    (e1 : Fin d → ℝ) ⬝ᵥ e1 = 1 := by
  classical
  unfold dotProduct
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp [e1]
  · intro b _ hb
    have hb0 : b.val ≠ 0 := by
      intro he
      exact hb (Fin.ext he)
    simp [e1, hb0]
  · simp

theorem proof
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    (∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i) + τ0 * dκ + κ0 * dτ
      = (γ - 1) * mu0 x0 τ0 s0 κ0 * ((k : ℝ) + 1)  := by
  rw [_root_.P2MInline_First.proof kind n hwf x0 s0 dx ds τ0 κ0 dτ dκ]
  have hcomp := h22.2.2.2.1
  have he (i : Fin k) : (e1 : Fin (n i) → ℝ) ⬝ᵥ e1 = 1 :=
    e1_dot_self (block_dim_pos kind n hwf i)
  simp_rw [hcomp, dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul]
  simp_rw [he, mul_one]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    (_root_.P2MInline_Eq61.proof kind n hwf x0 s0).1, (_root_.P2MInline_Eq61.proof kind n hwf x0 s0).2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmu : mu0 x0 τ0 s0 κ0 * ((k : ℝ) + 1) = (∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0 := by
    unfold mu0
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith only [hmu, h22.2.2.2.2]

end P2MInline_Chain

namespace P2MInline_Orthogonal

set_option autoImplicit false
open Matrix ConicQuadIPM.Complementarity ConicQuadIPM.NewtonStep
theorem proof
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    (∑ i, dx i ⬝ᵥ ds i) + dτ * dκ = 0  := by
  obtain ⟨hz, hexp⟩ := _root_.P2MInline_Eq26.proof kind n hwf A b c x0 τ0 y0 s0 κ0 γ hγ dx dτ dy ds dκ h22
  have hc := _root_.P2MInline_Chain.proof kind n hwf A b c x0 τ0 y0 s0 κ0 γ hγ dx dτ dy ds dκ h22
  have hmu : mu0 x0 τ0 s0 κ0 * ((k : ℝ) + 1) = (∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0 := by
    unfold mu0
    exact div_mul_cancel₀ _ (by positivity)
  rw [mul_assoc, hmu] at hc
  rw [hc] at hexp
  have h := hz.trans hexp
  nlinarith only [h]

end P2MInline_Orthogonal

set_option autoImplicit false
open Matrix ConicQuadIPM.Complementarity ConicQuadIPM.NewtonStep
theorem solution
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (x1 : (i : Fin k) → Fin (n i) → ℝ) (τ1 : ℝ) (y1 : Fin m → ℝ)
    (s1 : (i : Fin k) → Fin (n i) → ℝ) (κ1 : ℝ)
    (hx1 : ∀ i, x1 i = x0 i + α • dx i) (hτ1 : τ1 = τ0 + α * dτ)
    (hy1 : y1 = y0 + α • dy) (hs1 : ∀ i, s1 i = s0 i + α • ds i)
    (hκ1 : κ1 = κ0 + α * dκ) :
    (∑ i, A i *ᵥ x1 i) - τ1 • b = (1 - α * (1 - γ)) • ((∑ i, A i *ᵥ x0 i) - τ0 • b) ∧
    (∀ i, (A i)ᵀ *ᵥ y1 + s1 i - τ1 • c i
        = (1 - α * (1 - γ)) • ((A i)ᵀ *ᵥ y0 + s0 i - τ0 • c i)) ∧
    -(∑ i, c i ⬝ᵥ x1 i) + b ⬝ᵥ y1 - κ1
        = (1 - α * (1 - γ)) * (-(∑ i, c i ⬝ᵥ x0 i) + b ⬝ᵥ y0 - κ0) ∧
    (∑ i, dx i ⬝ᵥ ds i) + dτ * dκ = 0 ∧
    (∑ i, x1 i ⬝ᵥ s1 i) + τ1 * κ1
        = (1 - α * (1 - γ)) * ((∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0)  := by
  have hlin := h22.1
  have hdual := h22.2.1
  have hscalar := h22.2.2.1
  have hdir := _root_.P2MInline_Orthogonal.proof kind n hwf A b c x0 τ0 y0 s0 κ0 γ hγ dx dτ dy ds dκ h22
  have hc := _root_.P2MInline_Chain.proof kind n hwf A b c x0 τ0 y0 s0 κ0 γ hγ dx dτ dy ds dκ h22
  have hmu : mu0 x0 τ0 s0 κ0 * ((k : ℝ) + 1) = (∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0 := by
    unfold mu0
    exact div_mul_cancel₀ _ (by positivity)
  rw [mul_assoc, hmu] at hc
  have hx : (∑ i, A i *ᵥ x1 i) = (∑ i, A i *ᵥ x0 i) + α • (∑ i, A i *ᵥ dx i) := by
    simp_rw [hx1, mulVec_add, mulVec_smul]
    rw [Finset.sum_add_distrib, Finset.smul_sum]
  have hcx : (∑ i, c i ⬝ᵥ x1 i) = (∑ i, c i ⬝ᵥ x0 i) + α * (∑ i, c i ⬝ᵥ dx i) := by
    simp_rw [hx1, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨?_, ?_, ?_, hdir, ?_⟩
  · rw [hx, hτ1]
    ext j
    have h := congrFun hlin j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    linear_combination α * h
  · intro i
    rw [hy1, hs1 i, hτ1, mulVec_add, mulVec_smul]
    ext j
    have h := congrFun (hdual i) j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    linear_combination α * h
  · rw [hcx, hy1, hκ1, dotProduct_add, dotProduct_smul]
    simp only [smul_eq_mul]
    linear_combination α * hscalar
  · have hexp (i : Fin k) :
        (x0 i + α • dx i) ⬝ᵥ (s0 i + α • ds i) =
          x0 i ⬝ᵥ s0 i + α * (x0 i ⬝ᵥ ds i + s0 i ⬝ᵥ dx i) + α ^ 2 * (dx i ⬝ᵥ ds i) := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm (dx i) (s0 i)]
      ring
    have hsum : (∑ i, x1 i ⬝ᵥ s1 i) =
        (∑ i, x0 i ⬝ᵥ s0 i) + α * ((∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i)) +
          α ^ 2 * (∑ i, dx i ⬝ᵥ ds i) := by
      simp_rw [hx1, hs1, hexp]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum, hτ1, hκ1]
    linear_combination α * hc + α ^ 2 * hdir

#print axioms solution
