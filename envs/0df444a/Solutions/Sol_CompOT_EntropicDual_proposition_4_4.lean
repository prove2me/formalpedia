-- Prove2me | solution 1 for CompOT.EntropicDual.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T12:10:21.168819+00:00
-- url     : https://prove2.me/submissions/a3a0fdbe-1da9-42b9-ad5a-1654eabb57a1

import Mathlib
import Definitions.Def_CompOT_EntropicDual_Defs

set_option autoImplicit false

namespace P44Sinkhorn

open CompOT.EntropicDual

/-- One-dimensional concave bound: `x a - ε e^{x/ε} A ≤ ε log(a/A) a - ε a`. -/
lemma phi_le {ε a A x : ℝ} (hε : 0 < ε) (ha : 0 < a) (hA : 0 < A) :
    x * a - ε * (Real.exp (x / ε) * A) ≤ ε * Real.log (a / A) * a - ε * a := by
  set L := Real.log (a / A) with hL
  set y := x / ε - L with hy
  have hexpL : Real.exp L = a / A := Real.exp_log (div_pos ha hA)
  have h1 : Real.exp (x / ε) * A = a * Real.exp y := by
    have : x / ε = y + L := by rw [hy]; ring
    rw [this, Real.exp_add, hexpL]; field_simp
  have hx : x = ε * (y + L) := by rw [hy]; field_simp; ring
  rw [h1, hx]
  have hk := mul_nonneg (mul_pos hε ha).le (sub_nonneg.2 (Real.add_one_le_exp y))
  nlinarith [hk]

lemma phi_eq {ε a A x : ℝ} (hε : 0 < ε) (ha : 0 < a) (hA : 0 < A)
    (h : x * a - ε * (Real.exp (x / ε) * A) = ε * Real.log (a / A) * a - ε * a) :
    Real.exp (x / ε) * A = a := by
  set L := Real.log (a / A) with hL
  set y := x / ε - L with hy
  have hexpL : Real.exp L = a / A := Real.exp_log (div_pos ha hA)
  have h1 : Real.exp (x / ε) * A = a * Real.exp y := by
    have : x / ε = y + L := by rw [hy]; ring
    rw [this, Real.exp_add, hexpL]; field_simp
  have hx : x = ε * (y + L) := by rw [hy]; field_simp; ring
  rw [h1, hx] at h
  have hy0 : y = 0 := by
    by_contra hne
    have := Real.add_one_lt_exp hne
    have hpos := mul_pos (mul_pos hε ha) (sub_pos.2 this)
    nlinarith [hpos]
  rw [h1, hy0, Real.exp_zero, mul_one]

lemma phi_at {ε a A : ℝ} (hε : 0 < ε) (ha : 0 < a) (hA : 0 < A) :
    (ε * Real.log (a / A)) * a - ε * (Real.exp (ε * Real.log (a / A) / ε) * A)
      = ε * Real.log (a / A) * a - ε * a := by
  have : ε * Real.log (a / A) / ε = Real.log (a / A) := by field_simp
  rw [this, Real.exp_log (div_pos ha hA)]
  field_simp

/-- Fenchel-Young defect `x log x - x - x y + e^y`. -/
noncomputable def psi (x y : ℝ) : ℝ := x * Real.log x - x - x * y + Real.exp y

lemma psi_nonneg {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : 0 ≤ psi x y := by
  unfold psi
  rcases hx.eq_or_lt with h | h
  · subst h; simp [Real.exp_pos y |>.le]
  · set t := Real.log x
    have hxt : Real.exp t = x := Real.exp_log h
    have hey : Real.exp y = x * Real.exp (y - t) := by
      rw [← hxt, ← Real.exp_add]; congr 1; ring
    rw [hey]
    have := mul_nonneg h.le (sub_nonneg.2 (Real.add_one_le_exp (y - t)))
    nlinarith [this]

lemma psi_eq_zero {x y : ℝ} (hx : 0 < x) (h : psi x y = 0) : x = Real.exp y := by
  unfold psi at h
  set t := Real.log x
  have hxt : Real.exp t = x := Real.exp_log hx
  have hey : Real.exp y = x * Real.exp (y - t) := by
    rw [← hxt, ← Real.exp_add]; congr 1; ring
  rw [hey] at h
  have hyt : y - t = 0 := by
    by_contra hne
    have := Real.add_one_lt_exp hne
    have := mul_pos hx (sub_pos.2 this)
    nlinarith [this]
  rw [hey, hyt, Real.exp_zero, mul_one]

variable {n m : ℕ}

/-- Row sums of the kernel against `e^{g/ε}`. -/
noncomputable def rowA (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (g : Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ j, gibbs C ε i j * Real.exp (g j / ε)

/-- Column sums of `e^{f/ε}` against the kernel. -/
noncomputable def colB (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (f : Fin n → ℝ) (j : Fin m) : ℝ :=
  ∑ i, Real.exp (f i / ε) * gibbs C ε i j

lemma gibbs_pos (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (i : Fin n) (j : Fin m) :
    0 < gibbs C ε i j := Real.exp_pos _

lemma rowA_pos (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (g : Fin m → ℝ) (hm : 0 < m)
    (i : Fin n) : 0 < rowA C ε g i := by
  unfold rowA
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (gibbs_pos C ε i j) (Real.exp_pos _))
    Finset.univ_nonempty

lemma colB_pos (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (f : Fin n → ℝ) (hn : 0 < n)
    (j : Fin m) : 0 < colB C ε f j := by
  unfold colB
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun i _ => mul_pos (Real.exp_pos _) (gibbs_pos C ε i j))
    Finset.univ_nonempty

lemma dual_rows (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) :
    dualObjEnt C a b ε f g =
      (∑ i, (f i * a i - ε * (Real.exp (f i / ε) * rowA C ε g i))) + ∑ j, g j * b j := by
  unfold dualObjEnt rowA
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have : ∀ i, Real.exp (f i / ε) * ∑ j, gibbs C ε i j * Real.exp (g j / ε)
      = ∑ j, Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε) := by
    intro i; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [this]; ring

lemma dual_cols (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) :
    dualObjEnt C a b ε f g =
      (∑ j, (g j * b j - ε * (Real.exp (g j / ε) * colB C ε f j))) + ∑ i, f i * a i := by
  unfold dualObjEnt colB
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm (f := fun i j =>
    Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε))]
  have : ∀ j, Real.exp (g j / ε) * ∑ i, Real.exp (f i / ε) * gibbs C ε i j
      = ∑ i, Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε) := by
    intro j; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [this]; ring

/-- The `f`-update (row scaling). -/
noncomputable def updF (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (ε : ℝ)
    (g : Fin m → ℝ) (i : Fin n) : ℝ := ε * Real.log (a i / rowA C ε g i)

/-- The `g`-update (column scaling). -/
noncomputable def updG (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : Fin n → ℝ) (j : Fin m) : ℝ := ε * Real.log (b j / colB C ε f j)

lemma dual_le_updF (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hm : 0 < m) (ha_pos : ∀ i, 0 < a i) (f : Fin n → ℝ) (g : Fin m → ℝ) :
    dualObjEnt C a b ε f g ≤ dualObjEnt C a b ε (updF C a ε g) g := by
  rw [dual_rows, dual_rows]
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) le_rfl
  unfold updF
  rw [phi_at hε (ha_pos i) (rowA_pos C ε g hm i)]
  exact phi_le hε (ha_pos i) (rowA_pos C ε g hm i)

lemma dual_le_updG (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hn : 0 < n) (hb_pos : ∀ j, 0 < b j) (f : Fin n → ℝ) (g : Fin m → ℝ) :
    dualObjEnt C a b ε f g ≤ dualObjEnt C a b ε f (updG C b ε f) := by
  rw [dual_cols, dual_cols]
  refine add_le_add (Finset.sum_le_sum fun j _ => ?_) le_rfl
  unfold updG
  rw [phi_at hε (hb_pos j) (colB_pos C ε f hn j)]
  exact phi_le hε (hb_pos j) (colB_pos C ε f hn j)

lemma dual_shift (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) {ε : ℝ}
    (_hε : 0 < ε) (hsa : ∑ i, a i = 1) (hsb : ∑ j, b j = 1) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (c : ℝ) :
    dualObjEnt C a b ε (fun i => f i + c) (fun j => g j - c) = dualObjEnt C a b ε f g := by
  unfold dualObjEnt
  have h1 : ∑ i, (f i + c) * a i = (∑ i, f i * a i) + c := by
    simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hsa]; ring
  have h2 : ∑ j, (g j - c) * b j = (∑ j, g j * b j) - c := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsb]; ring
  have h3 : ∀ i j, Real.exp ((f i + c) / ε) * gibbs C ε i j * Real.exp ((g j - c) / ε)
      = Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε) := by
    intro i j
    have e1 : (f i + c) / ε = f i / ε + c / ε := by ring
    have e2 : (g j - c) / ε = g j / ε - c / ε := by ring
    rw [e1, e2, Real.exp_add, Real.exp_sub]
    have := Real.exp_pos (c / ε)
    field_simp
  rw [h1, h2]
  simp_rw [h3]
  ring

lemma scal_eq (C : Matrix (Fin n) (Fin m) ℝ) {ε : ℝ} (f : Fin n → ℝ) (g : Fin m → ℝ)
    (i : Fin n) (j : Fin m) :
    Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε)
      = Real.exp ((f i + g j - C i j) / ε) := by
  unfold gibbs; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

lemma gap_eq (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) {ε : ℝ}
    (hε : 0 < ε) (Q : Matrix (Fin n) (Fin m) ℝ) (hQ : Q ∈ CompOT.Assignment.couplings a b)
    (f : Fin n → ℝ) (g : Fin m → ℝ) :
    entropicObj C Q ε - dualObjEnt C a b ε f g
      = ∑ i, ∑ j, ε * psi (Q i j) ((f i + g j - C i j) / ε) := by
  obtain ⟨_, hrow, hcol⟩ := hQ
  have hfa : ∑ i, f i * a i = ∑ i, ∑ j, f i * Q i j := by
    simp_rw [← hrow, Finset.mul_sum]
  have hgb : ∑ j, g j * b j = ∑ i, ∑ j, g j * Q i j := by
    rw [Finset.sum_comm]; simp_rw [← hcol, Finset.mul_sum]
  have key : ∀ i j, C i j * Q i j - ε * (Real.negMulLog (Q i j) + Q i j)
      - (f i * Q i j + g j * Q i j)
      + ε * (Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε))
      = ε * psi (Q i j) ((f i + g j - C i j) / ε) := by
    intro i j
    rw [scal_eq]
    have hy : (f i + g j - C i j) / ε * ε = f i + g j - C i j := div_mul_cancel₀ _ hε.ne'
    unfold psi Real.negMulLog
    linear_combination (Q i j) * hy
  unfold entropicObj dualObjEnt CompOT.Assignment.frob CompOT.EntropicLimit.entropy
  rw [hfa, hgb]
  simp_rw [← key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_add]
  ring

lemma weak_dual (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) {ε : ℝ}
    (hε : 0 < ε) (Q : Matrix (Fin n) (Fin m) ℝ) (hQ : Q ∈ CompOT.Assignment.couplings a b)
    (f : Fin n → ℝ) (g : Fin m → ℝ) :
    dualObjEnt C a b ε f g ≤ entropicObj C Q ε := by
  have h := gap_eq C a b hε Q hQ f g
  have : 0 ≤ ∑ i, ∑ j, ε * psi (Q i j) ((f i + g j - C i j) / ε) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg hε.le (psi_nonneg _ (hQ.1 i j))))
  linarith

lemma log_bounds {ε L A M x : ℝ} (hε : 0 < ε) (hA : 0 < A) (ha : 0 < x)
    (hlo : Real.exp (-M / ε) ≤ A) (hhi : A ≤ Real.exp (M / ε)) (hL : L = ε * Real.log (x / A)) :
    ε * Real.log x - M ≤ L ∧ L ≤ ε * Real.log x + M := by
  have h1 : Real.log A ≤ M / ε := (Real.log_le_iff_le_exp hA).2 hhi
  have h2 : -M / ε ≤ Real.log A := (Real.le_log_iff_exp_le hA).2 hlo
  have h1' : Real.log A * ε ≤ M := (le_div_iff₀ hε).1 h1
  have h2' : -M ≤ Real.log A * ε := (div_le_iff₀ hε).1 h2
  rw [hL, Real.log_div ha.ne' hA.ne']
  constructor <;> nlinarith

lemma exp_div_bounds {ε L M x : ℝ} (hε : 0 < ε) (hx : 0 < x)
    (hlo : ε * Real.log x - M ≤ L) (hhi : L ≤ ε * Real.log x + M) :
    x * Real.exp (-M / ε) ≤ Real.exp (L / ε) ∧ Real.exp (L / ε) ≤ x * Real.exp (M / ε) := by
  have e1 : (ε * Real.log x + M) / ε = Real.log x + M / ε := by
    rw [add_div, mul_div_cancel_left₀ _ hε.ne']
  have e2 : (ε * Real.log x - M) / ε = Real.log x + -M / ε := by
    rw [sub_div, mul_div_cancel_left₀ _ hε.ne', neg_div]; ring
  have u : L / ε ≤ Real.log x + M / ε := by
    rw [← e1]; exact (div_le_div_iff_of_pos_right hε).2 hhi
  have l : Real.log x + -M / ε ≤ L / ε := by
    rw [← e2]; exact (div_le_div_iff_of_pos_right hε).2 hlo
  constructor
  · calc x * Real.exp (-M / ε) = Real.exp (Real.log x + -M / ε) := by
          rw [Real.exp_add, Real.exp_log hx]
      _ ≤ _ := Real.exp_le_exp.2 l
  · calc Real.exp (L / ε) ≤ Real.exp (Real.log x + M / ε) := Real.exp_le_exp.2 u
      _ = x * Real.exp (M / ε) := by rw [Real.exp_add, Real.exp_log hx]

theorem exists_scaling (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε) (hsa : ∑ i, a i = 1) (hsb : ∑ j, b j = 1)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ j, 0 < b j) :
    ∃ f : Fin n → ℝ, ∃ g : Fin m → ℝ,
      (∀ i, Real.exp (f i / ε) * rowA C ε g i = a i) ∧
      (∀ j, Real.exp (g j / ε) * colB C ε f j = b j) := by
  set M : ℝ := ∑ i, ∑ j, |C i j| with hM
  have hCM : ∀ i j, |C i j| ≤ M := by
    intro i j
    calc |C i j| ≤ ∑ j', |C i j'| :=
          Finset.single_le_sum (f := fun j' => |C i j'|) (fun j' _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ M := Finset.single_le_sum (f := fun i => ∑ j, |C i j|)
            (fun i' _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
  have hK : ∀ i j, Real.exp (-M / ε) ≤ gibbs C ε i j ∧ gibbs C ε i j ≤ Real.exp (M / ε) := by
    intro i j
    have h := abs_le.1 (hCM i j)
    unfold gibbs
    constructor
    · exact Real.exp_le_exp.2 ((div_le_div_iff_of_pos_right hε).2 (by linarith))
    · exact Real.exp_le_exp.2 ((div_le_div_iff_of_pos_right hε).2 (by linarith))
  -- row sums when `∑ e^{g/ε} = 1`
  have hrowB : ∀ g : Fin m → ℝ, ∑ j, Real.exp (g j / ε) = 1 → ∀ i,
      Real.exp (-M / ε) ≤ rowA C ε g i ∧ rowA C ε g i ≤ Real.exp (M / ε) := by
    intro g hg i
    unfold rowA
    constructor
    · calc Real.exp (-M / ε) = ∑ j, Real.exp (-M / ε) * Real.exp (g j / ε) := by
            rw [← Finset.mul_sum, hg, mul_one]
        _ ≤ _ := Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (hK i j).1 (Real.exp_pos _).le)
    · calc ∑ j, gibbs C ε i j * Real.exp (g j / ε)
            ≤ ∑ j, Real.exp (M / ε) * Real.exp (g j / ε) := Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (hK i j).2 (Real.exp_pos _).le)
        _ = Real.exp (M / ε) := by rw [← Finset.mul_sum, hg, mul_one]
  -- column sums when `f` is in the row box
  have hcolB : ∀ f : Fin n → ℝ,
      (∀ i, ε * Real.log (a i) - M ≤ f i ∧ f i ≤ ε * Real.log (a i) + M) → ∀ j,
      Real.exp (-(2 * M) / ε) ≤ colB C ε f j ∧ colB C ε f j ≤ Real.exp ((2 * M) / ε) := by
    intro f hf j
    have hE : ∀ i, a i * Real.exp (-M / ε) ≤ Real.exp (f i / ε) ∧
        Real.exp (f i / ε) ≤ a i * Real.exp (M / ε) :=
      fun i => exp_div_bounds hε (ha_pos i) (hf i).1 (hf i).2
    have e2 : Real.exp ((2 * M) / ε) = Real.exp (M / ε) * Real.exp (M / ε) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2' : Real.exp (-(2 * M) / ε) = Real.exp (-M / ε) * Real.exp (-M / ε) := by
      rw [← Real.exp_add]; congr 1; ring
    unfold colB
    constructor
    · calc Real.exp (-(2 * M) / ε)
            = ∑ i, a i * Real.exp (-M / ε) * Real.exp (-M / ε) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, hsa, one_mul, e2']
        _ ≤ _ := Finset.sum_le_sum (fun i _ =>
            mul_le_mul (hE i).1 (hK i j).1 (Real.exp_pos _).le (Real.exp_pos _).le)
    · calc ∑ i, Real.exp (f i / ε) * gibbs C ε i j
            ≤ ∑ i, a i * Real.exp (M / ε) * Real.exp (M / ε) := Finset.sum_le_sum (fun i _ =>
            mul_le_mul (hE i).2 (hK i j).2 (gibbs_pos C ε i j).le
              (mul_pos (ha_pos i) (Real.exp_pos _)).le)
        _ = Real.exp ((2 * M) / ε) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, hsa, one_mul, e2]
  set S : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
    Set.Icc (fun i => ε * Real.log (a i) - M) (fun i => ε * Real.log (a i) + M) ×ˢ
    Set.Icc (fun j => ε * Real.log (b j) - 2 * M) (fun j => ε * Real.log (b j) + 2 * M)
    with hS
  have chain : ∀ f g, ∃ q ∈ S, dualObjEnt C a b ε f g ≤ dualObjEnt C a b ε q.1 q.2 := by
    intro f g
    set T := ∑ j, Real.exp (g j / ε) with hT
    have hTpos : 0 < T := by
      have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
    set c := ε * Real.log T with hc
    set g' : Fin m → ℝ := fun j => g j - c with hg'
    have hsum' : ∑ j, Real.exp (g' j / ε) = 1 := by
      have : ∀ j, Real.exp (g' j / ε) = Real.exp (g j / ε) / T := by
        intro j
        have : g' j / ε = g j / ε - Real.log T := by
          rw [hg', hc]; field_simp
        rw [this, Real.exp_sub, Real.exp_log hTpos]
      simp_rw [this]
      rw [← Finset.sum_div, ← hT, div_self hTpos.ne']
    set f1 := updF C a ε g' with hf1
    set g1 := updG C b ε f1 with hg1
    have hf1b : ∀ i, ε * Real.log (a i) - M ≤ f1 i ∧ f1 i ≤ ε * Real.log (a i) + M := by
      intro i
      exact log_bounds hε (rowA_pos C ε g' hm i) (ha_pos i) (hrowB g' hsum' i).1
        (hrowB g' hsum' i).2 rfl
    have hg1b : ∀ j, ε * Real.log (b j) - 2 * M ≤ g1 j ∧ g1 j ≤ ε * Real.log (b j) + 2 * M := by
      intro j
      exact log_bounds (M := 2 * M) hε (colB_pos C ε f1 hn j) (hb_pos j) (hcolB f1 hf1b j).1
        (hcolB f1 hf1b j).2 rfl
    refine ⟨(f1, g1), ?_, ?_⟩
    · refine ⟨⟨fun i => (hf1b i).1, fun i => (hf1b i).2⟩,
        ⟨fun j => (hg1b j).1, fun j => (hg1b j).2⟩⟩
    · calc dualObjEnt C a b ε f g
          = dualObjEnt C a b ε (fun i => f i + c) (fun j => g j - c) :=
            (dual_shift C a b hε hsa hsb f g c).symm
        _ ≤ dualObjEnt C a b ε f1 g' := dual_le_updF C a b hε hm ha_pos _ _
        _ ≤ dualObjEnt C a b ε f1 g1 := dual_le_updG C a b hε hn hb_pos _ _
  have hScpt : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hSne : S.Nonempty := by
    obtain ⟨q, hq, _⟩ := chain 0 0
    exact ⟨q, hq⟩
  have hcont : Continuous (fun q : (Fin n → ℝ) × (Fin m → ℝ) => dualObjEnt C a b ε q.1 q.2) := by
    unfold dualObjEnt gibbs
    fun_prop
  obtain ⟨q, _, hqmax⟩ := hScpt.exists_isMaxOn hSne hcont.continuousOn
  have hglob : ∀ f g, dualObjEnt C a b ε f g ≤ dualObjEnt C a b ε q.1 q.2 := by
    intro f g
    obtain ⟨q', hq'S, hle⟩ := chain f g
    exact hle.trans ((isMaxOn_iff.1 hqmax) q' hq'S)
  refine ⟨q.1, q.2, ?_, ?_⟩
  · -- row marginals
    have h1 := hglob (updF C a ε q.2) q.2
    rw [dual_rows, dual_rows] at h1
    have hup : ∀ i, updF C a ε q.2 i * a i - ε * (Real.exp (updF C a ε q.2 i / ε)
        * rowA C ε q.2 i) = ε * Real.log (a i / rowA C ε q.2 i) * a i - ε * a i :=
      fun i => phi_at hε (ha_pos i) (rowA_pos C ε q.2 hm i)
    simp_rw [hup] at h1
    have hz : ∑ i, ((ε * Real.log (a i / rowA C ε q.2 i) * a i - ε * a i) -
        (q.1 i * a i - ε * (Real.exp (q.1 i / ε) * rowA C ε q.2 i))) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib]; linarith
      · exact Finset.sum_nonneg (fun i _ =>
          sub_nonneg.2 (phi_le hε (ha_pos i) (rowA_pos C ε q.2 hm i)))
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
          sub_nonneg.2 (phi_le hε (ha_pos i) (rowA_pos C ε q.2 hm i)))] at hz
    intro i
    exact phi_eq hε (ha_pos i) (rowA_pos C ε q.2 hm i)
      (by linarith [hz i (Finset.mem_univ i)])
  · -- column marginals
    have h1 := hglob q.1 (updG C b ε q.1)
    rw [dual_cols, dual_cols] at h1
    have hup : ∀ j, updG C b ε q.1 j * b j - ε * (Real.exp (updG C b ε q.1 j / ε)
        * colB C ε q.1 j) = ε * Real.log (b j / colB C ε q.1 j) * b j - ε * b j :=
      fun j => phi_at hε (hb_pos j) (colB_pos C ε q.1 hn j)
    simp_rw [hup] at h1
    have hz : ∑ j, ((ε * Real.log (b j / colB C ε q.1 j) * b j - ε * b j) -
        (q.2 j * b j - ε * (Real.exp (q.2 j / ε) * colB C ε q.1 j))) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib]; linarith
      · exact Finset.sum_nonneg (fun j _ =>
          sub_nonneg.2 (phi_le hε (hb_pos j) (colB_pos C ε q.1 hn j)))
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
          sub_nonneg.2 (phi_le hε (hb_pos j) (colB_pos C ε q.1 hn j)))] at hz
    intro j
    exact phi_eq hε (hb_pos j) (colB_pos C ε q.1 hn j)
      (by linarith [hz j (Finset.mem_univ j)])

end P44Sinkhorn

open CompOT.EntropicDual in
theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ j, 0 < b j) :
    ∃ P : Matrix (Fin n) (Fin m) ℝ,
      CompOT.EntropicLimit.IsEntropicOptimal C a b ε P ∧
      ∃ f : Fin n → ℝ, ∃ g : Fin m → ℝ,
        dualObjEnt C a b ε f g = entropicObj C P ε ∧
        (∀ f' g', dualObjEnt C a b ε f' g' ≤ dualObjEnt C a b ε f g) ∧
        (∀ f' g', dualObjEnt C a b ε f' g' = dualObjEnt C a b ε f g →
          ∀ i j, P i j = Real.exp (f' i / ε) * gibbs C ε i j *
            Real.exp (g' j / ε)) := by
  obtain ⟨f, g, hrow, hcol⟩ :=
    P44Sinkhorn.exists_scaling C a b ε hn hm hε ha.2 hb.2 ha_pos hb_pos
  set P : Matrix (Fin n) (Fin m) ℝ :=
    fun i j => Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε) with hPdef
  have hPpos : ∀ i j, 0 < P i j := fun i j =>
    mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (Real.exp_pos _)
  have hP : P ∈ CompOT.Assignment.couplings a b := by
    refine ⟨fun i j => (hPpos i j).le, fun i => ?_, fun j => ?_⟩
    · rw [← hrow i]; unfold P44Sinkhorn.rowA; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by simp only [hPdef]; ring)
    · rw [← hcol j]; unfold P44Sinkhorn.colB; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by simp only [hPdef]; ring)
  have hgap0 : entropicObj C P ε = dualObjEnt C a b ε f g := by
    have h := P44Sinkhorn.gap_eq C a b hε P hP f g
    have h0 : ∀ i j, ε * P44Sinkhorn.psi (P i j) ((f i + g j - C i j) / ε) = 0 := by
      intro i j
      have hPe : P i j = Real.exp ((f i + g j - C i j) / ε) := P44Sinkhorn.scal_eq C f g i j
      rw [hPe]; unfold P44Sinkhorn.psi; rw [Real.log_exp]; ring
    simp_rw [h0, Finset.sum_const_zero] at h
    linarith
  refine ⟨P, ⟨hP, fun Q hQ => ?_⟩, f, g, hgap0.symm, fun f' g' => ?_, fun f' g' heq i j => ?_⟩
  · show entropicObj C P ε ≤ entropicObj C Q ε
    rw [hgap0]; exact P44Sinkhorn.weak_dual C a b hε Q hQ f g
  · rw [← hgap0]; exact P44Sinkhorn.weak_dual C a b hε P hP f' g'
  · have h := P44Sinkhorn.gap_eq C a b hε P hP f' g'
    rw [hgap0, ← heq, sub_self] at h
    have hnn : ∀ i j, 0 ≤ ε * P44Sinkhorn.psi (P i j) ((f' i + g' j - C i j) / ε) :=
      fun i j => mul_nonneg hε.le (P44Sinkhorn.psi_nonneg _ (hPpos i j).le)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => hnn i j))).1 h.symm i (Finset.mem_univ i)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 h2 j
      (Finset.mem_univ j)
    have h4 : P44Sinkhorn.psi (P i j) ((f' i + g' j - C i j) / ε) = 0 := by
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hε.ne'
      · exact h
    rw [P44Sinkhorn.psi_eq_zero (hPpos i j) h4, P44Sinkhorn.scal_eq C f' g' i j]
