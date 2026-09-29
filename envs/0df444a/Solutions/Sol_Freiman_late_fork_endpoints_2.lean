-- Prove2me | solution 2 for Freiman.late_fork_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-18T10:52:22.838179+00:00
-- url     : https://prove2.me/submissions/ce6e7f8f-ba52-42ef-9699-e2411d8d2cad

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational

set_option maxRecDepth 8000

open Freiman

namespace ForkDev

/-! ### The quadratic irrational α -/

lemma not_isSquare_of (n : ℕ) (h : ∀ r ≤ n, r * r ≠ n) : ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  have hle : r ≤ n := by nlinarith
  exact h r hle hr.symm

lemma irr21 : Irrational (Real.sqrt 21) := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_of 21 (by decide))
  simpa using this

lemma s21_nonneg : (0:ℝ) ≤ Real.sqrt 21 := Real.sqrt_nonneg _
lemma s21_sq : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
lemma s21_lb : (4.582:ℝ) < Real.sqrt 21 := by nlinarith [s21_sq, s21_nonneg]
lemma s21_ub : Real.sqrt 21 < (4.583:ℝ) := by nlinarith [s21_sq, s21_nonneg]

lemma beta_eq : lowerBeta = 3 * lowerAlpha := by unfold lowerBeta lowerAlpha; ring
lemma alpha_lb : (0.2636:ℝ) < lowerAlpha := by unfold lowerAlpha; linarith [s21_lb]
lemma alpha_ub : lowerAlpha < (0.26384:ℝ) := by unfold lowerAlpha; linarith [s21_ub]
lemma alpha_pos : 0 < lowerAlpha := by linarith [alpha_lb]
lemma beta_gt_alpha : lowerAlpha < lowerBeta := by rw [beta_eq]; linarith [alpha_pos]

lemma alpha_quad : 3 * lowerAlpha ^ 2 + 3 * lowerAlpha - 1 = 0 := by
  unfold lowerAlpha; nlinarith [s21_sq]

/-- ℤ-linear independence of `1` and `α`: the only form of irrationality we need. -/
lemma alpha_indep (a b : ℤ) (h : (a:ℝ) + lowerAlpha * (b:ℝ) = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hbR : ((b:ℤ):ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
    apply irr21
    refine ⟨((3*b - 6*a : ℤ) : ℚ) / ((b : ℤ) : ℚ), ?_⟩
    push_cast
    unfold lowerAlpha at h
    field_simp at h ⊢
    linarith
  refine ⟨?_, hb⟩
  subst hb
  simpa using h

/-! ### Continuants, as reals -/

noncomputable def cdR (w : List ℕ+) : ℝ × ℝ := (((lowerCD w).1 : ℝ), ((lowerCD w).2 : ℝ))

lemma cdR_nil : cdR [] = (0, 1) := by simp [cdR, lowerCD]

lemma cd_step (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

lemma cdR_step (w : List ℕ+) (a : ℕ+) :
    cdR (w ++ [a]) = ((cdR w).2, (cdR w).1 + ((a:ℕ):ℝ) * (cdR w).2) := by
  simp [cdR, cd_step]

lemma cdR_pos (w : List ℕ+) : 0 ≤ (cdR w).1 ∧ 0 < (cdR w).2 := by
  induction w using List.reverseRecOn with
  | nil => rw [cdR_nil]; norm_num
  | append_singleton w a ih =>
    rw [cdR_step]
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    exact ⟨le_of_lt ih.2, by simp only; nlinarith [ih.1, ih.2]⟩

lemma cdR_le (w : List ℕ+) : (cdR w).1 ≤ (cdR w).2 := by
  induction w using List.reverseRecOn with
  | nil => rw [cdR_nil]; norm_num
  | append_singleton w a ih =>
    rw [cdR_step]
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.one_le
    have h := cdR_pos w
    simp only
    nlinarith [h.1, h.2]

lemma cd_bounds' (w : List ℕ+) :
    (0:ℤ) ≤ ((lowerCD w).1 : ℤ) ∧ (0:ℤ) < ((lowerCD w).2 : ℤ) := by
  have h := cdR_pos w
  constructor
  · positivity
  · have : 0 < (lowerCD w).2 := by
      by_contra hc
      have : (lowerCD w).2 = 0 := by omega
      rw [cdR, this] at h; simp at h
    exact_mod_cast this

/-! ### The Möbius difference identity -/

lemma pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => simp [prefixEval]
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

lemma pe_single (a : ℕ+) (x : ℝ) : prefixEval [a] x = 1 / (((a:ℕ):ℝ) + x) := rfl

lemma pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => simpa [prefixEval]
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1 / (((a:ℕ):ℝ) + prefixEval w x)
    positivity

noncomputable def sgnOf (w : List ℕ+) : ℝ := if w.length % 2 = 0 then 1 else -1

lemma sgnOf_step (w : List ℕ+) (a : ℕ+) : sgnOf (w ++ [a]) = - sgnOf w := by
  unfold sgnOf
  have hl : (w ++ [a]).length = w.length + 1 := by simp
  rw [hl]
  rcases Nat.mod_two_eq_zero_or_one w.length with h | h
  · rw [if_neg (by omega : ¬ (w.length + 1) % 2 = 0), if_pos h]; try norm_num
  · rw [if_pos (by omega : (w.length + 1) % 2 = 0), if_neg (by omega : ¬ w.length % 2 = 0)]; try norm_num

lemma pe_diff (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) / (((cdR w).2 + (cdR w).1 * x) * ((cdR w).2 + (cdR w).1 * y)) := by
  induction w using List.reverseRecOn generalizing x y with
  | nil => simp [cdR_nil, prefixEval, sgnOf]
  | append_singleton w a ih =>
    obtain ⟨hc, hd⟩ := cdR_pos w
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.one_le
    have hax : (0:ℝ) < ((a:ℕ):ℝ) + x := by linarith
    have hay : (0:ℝ) < ((a:ℕ):ℝ) + y := by linarith
    have hx' : (0:ℝ) ≤ 1 / (((a:ℕ):ℝ) + x) := by positivity
    have hy' : (0:ℝ) ≤ 1 / (((a:ℕ):ℝ) + y) := by positivity
    have hdx : (0:ℝ) < (cdR w).2 + (cdR w).1 * (1 / (((a:ℕ):ℝ) + x)) := by positivity
    have hdy : (0:ℝ) < (cdR w).2 + (cdR w).1 * (1 / (((a:ℕ):ℝ) + y)) := by positivity
    have hdx' : (0:ℝ) < (cdR w).1 + ((a:ℕ):ℝ) * (cdR w).2 + (cdR w).2 * x := by positivity
    have hdy' : (0:ℝ) < (cdR w).1 + ((a:ℕ):ℝ) * (cdR w).2 + (cdR w).2 * y := by positivity
    rw [pe_append, pe_append, pe_single, pe_single, ih _ _ hx' hy', cdR_step, sgnOf_step]
    simp only
    field_simp
    ring

/-! ### The width formula and the integer invariants -/

noncomputable def sg (w : List ℕ+) : ℝ :=
  ((cdR w).2 + (cdR w).1 * lowerAlpha) * ((cdR w).2 + (cdR w).1 * lowerBeta)

lemma sg_pos (w : List ℕ+) : 0 < sg w := by
  obtain ⟨hc, hd⟩ := cdR_pos w
  have ha := alpha_pos
  have hb : 0 < lowerBeta := by rw [beta_eq]; linarith
  unfold sg; positivity

lemma width_eq (w : List ℕ+) : lowerWidth w = (lowerBeta - lowerAlpha) / sg w := by
  have ha : (0:ℝ) ≤ lowerAlpha := le_of_lt alpha_pos
  have hb : (0:ℝ) ≤ lowerBeta := by rw [beta_eq]; linarith [alpha_pos]
  have hpos := sg_pos w
  unfold lowerWidth
  rw [pe_diff w _ _ hb ha]
  rw [abs_div, abs_mul]
  have h1 : |sgnOf w| = 1 := by unfold sgnOf; split_ifs <;> simp
  have h2 : |lowerBeta - lowerAlpha| = lowerBeta - lowerAlpha :=
    abs_of_pos (sub_pos.mpr beta_gt_alpha)
  have h3 : |((cdR w).2 + (cdR w).1 * lowerBeta) * ((cdR w).2 + (cdR w).1 * lowerAlpha)|
      = sg w := by
    rw [abs_of_pos]
    · unfold sg; ring
    · unfold sg at hpos; nlinarith [hpos]
  rw [h1, h2, h3, one_mul]

lemma width_eq_iff_sg (u v : List ℕ+) : lowerWidth u = lowerWidth v ↔ sg u = sg v := by
  have hu := sg_pos u
  have hv := sg_pos v
  have hba : 0 < lowerBeta - lowerAlpha := sub_pos.mpr beta_gt_alpha
  rw [width_eq, width_eq]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h; rw [h]

/-- `A` invariant of a word: `C^2 + D^2` for the continuant pair `(C,D)`. -/
def Ainv (w : List ℕ+) : ℤ := ((lowerCD w).1 : ℤ)^2 + ((lowerCD w).2 : ℤ)^2
/-- `B` invariant of a word: `4CD - 3C^2` for the continuant pair `(C,D)`. -/
def Binv (w : List ℕ+) : ℤ := 4*((lowerCD w).1 : ℤ)*((lowerCD w).2 : ℤ) - 3*((lowerCD w).1 : ℤ)^2

lemma sg_AB (w : List ℕ+) : sg w = (Ainv w : ℝ) + lowerAlpha * (Binv w : ℝ) := by
  have hq := alpha_quad
  unfold sg Ainv Binv cdR
  rw [beta_eq]
  push_cast
  nlinarith [hq]

/-- Equal widths force equality of BOTH integer invariants (α is irrational). -/
lemma width_eq_AB (u v : List ℕ+) (h : lowerWidth u = lowerWidth v) :
    Ainv u = Ainv v ∧ Binv u = Binv v := by
  have hs : sg u = sg v := (width_eq_iff_sg u v).mp h
  rw [sg_AB, sg_AB] at hs
  have h0 : ((Ainv u - Ainv v : ℤ) : ℝ) + lowerAlpha * ((Binv u - Binv v : ℤ) : ℝ) = 0 := by
    push_cast; linarith
  obtain ⟨h1, h2⟩ := alpha_indep _ _ h0
  exact ⟨by omega, by omega⟩

/-- **Ratio separator.** If a rational `m/n` strictly separates `B/A` of `u` from `B/A` of `v`,
the two words cannot have equal width. -/
lemma width_ne_of_sep (u v : List ℕ+) (m n : ℤ)
    (hu : n * Binv u < m * Ainv u) (hv : m * Ainv v < n * Binv v) :
    lowerWidth u ≠ lowerWidth v := by
  intro h
  obtain ⟨hA, hB⟩ := width_eq_AB u v h
  rw [hA, hB] at hu
  omega

/-! ### Transport of continuants along a concrete suffix -/

lemma cd_app (U V : List ℕ+) :
    lowerCD (U ++ V) = V.foldl (fun z a => (z.2, z.1 + (a:ℕ) * z.2)) (lowerCD U) := by
  simp [lowerCD, List.foldl_append]

-- smoke test: an explicit transport
example (U : List ℕ+) :
    lowerCD (U ++ [3,1]) = ((lowerCD U).1 + 3*(lowerCD U).2,
                            (lowerCD U).1 + 4*(lowerCD U).2) := by
  rw [cd_app]; simp; ring

/-! ### The tie dichotomy -/

/-- **Integer tie dichotomy.**  Two continuant pairs carry the same `(A,B)` invariants
iff they are equal or related by the single non-trivial involution
`(C,D) ↦ ((4D-3C)/5, (4C+3D)/5)` (the reflection of the `(A,B)`-preserving orthogonal group). -/
lemma AB_dichotomy (C D C' D' : ℤ) (hC : 0 ≤ C) (hD : 0 < D) (hC' : 0 ≤ C') (hD' : 0 < D')
    (hA : C^2 + D^2 = C'^2 + D'^2)
    (hB : 4*C*D - 3*C^2 = 4*C'*D' - 3*C'^2) :
    (C' = C ∧ D' = D) ∨ (5*C' = 4*D - 3*C ∧ 5*D' = 4*C + 3*D) := by
  have hid : ∀ x y : ℤ, (4*(x^2-y^2)+6*(x*y))^2 + (-3*(x^2-y^2)+8*(x*y))^2
      = 25*(x^2+y^2)^2 := by intros; ring
  have hS : -3*(C^2-D^2) + 8*(C*D) = -3*(C'^2-D'^2) + 8*(C'*D') := by
    linear_combination 3*hA + 2*hB
  have hPP : (4*(C^2-D^2)+6*(C*D))^2 = (4*(C'^2-D'^2)+6*(C'*D'))^2 := by
    have e1 := hid C D
    have e2 := hid C' D'
    have hAA : (C^2+D^2)^2 = (C'^2+D'^2)^2 := by rw [hA]
    have hSS : (-3*(C^2-D^2) + 8*(C*D))^2 = (-3*(C'^2-D'^2) + 8*(C'*D'))^2 := by rw [hS]
    linarith [e1, e2, hAA, hSS]
  have hP : (4*(C^2-D^2)+6*(C*D) - (4*(C'^2-D'^2)+6*(C'*D')))
          * (4*(C^2-D^2)+6*(C*D) + (4*(C'^2-D'^2)+6*(C'*D'))) = 0 := by
    linear_combination hPP
  rcases mul_eq_zero.mp hP with h | h
  · left
    have h25 : 25*(C^2-D^2) - 25*(C'^2-D'^2) = 0 := by linear_combination 4*h - 3*hS
    have hX : C^2 - D^2 = C'^2 - D'^2 := by linarith
    have hCsq : C^2 = C'^2 := by linarith
    have hDsq : D^2 = D'^2 := by linarith
    have hCC : (C - C')*(C + C') = 0 := by linear_combination hCsq
    have hDD : (D - D')*(D + D') = 0 := by linear_combination hDsq
    constructor
    · rcases mul_eq_zero.mp hCC with h1 | h1 <;> omega
    · rcases mul_eq_zero.mp hDD with h1 | h1 <;> omega
  · right
    have hX' : 25*(C'^2 - D'^2) = -7*(C^2-D^2) - 48*(C*D) := by
      linear_combination 4*h + 3*hS
    have hY50 : 50*(C'*D') = -24*(C^2-D^2) + 14*(C*D) := by
      linear_combination 3*h - 4*hS
    have hY25 : 25*(C'*D') = (4*D-3*C)*(4*C+3*D) := by nlinarith [hY50]
    have hD2 : ((5*D' - (4*C+3*D))*(5*D' + (4*C+3*D))) * 2 = 0 := by
      linear_combination (-25)*hA - hX'
    have hD2' : (5*D' - (4*C+3*D))*(5*D' + (4*C+3*D)) = 0 := by linarith
    have hDeq : 5*D' = 4*C + 3*D := by
      rcases mul_eq_zero.mp hD2' with h1 | h1 <;> omega
    refine ⟨?_, hDeq⟩
    have e1 : (4*D-3*C)*(5*D') = (4*D-3*C)*(4*C+3*D) := by rw [hDeq]
    have e2 : (5*C')*(5*D') = (4*D-3*C)*(5*D') := by
      rw [e1]; linear_combination hY25
    have hprod : (5*C' - (4*D-3*C))*(5*D') = 0 := by linear_combination e2
    have hpos : (0:ℤ) < 5*D' := by omega
    rcases mul_eq_zero.mp hprod with h1 | h1 <;> omega

/-- Word-level form of the dichotomy: a width tie forces equal continuants or the reflection. -/
lemma width_tie_dichotomy (u v : List ℕ+) (h : lowerWidth u = lowerWidth v) :
    ((lowerCD v).1 = (lowerCD u).1 ∧ (lowerCD v).2 = (lowerCD u).2) ∨
    (5*((lowerCD v).1:ℤ) = 4*((lowerCD u).2:ℤ) - 3*((lowerCD u).1:ℤ) ∧
     5*((lowerCD v).2:ℤ) = 4*((lowerCD u).1:ℤ) + 3*((lowerCD u).2:ℤ)) := by
  obtain ⟨hA, hB⟩ := width_eq_AB u v h
  have hu := cd_bounds' u
  have hv := cd_bounds' v
  have hA' : ((lowerCD u).1:ℤ)^2 + ((lowerCD u).2:ℤ)^2
      = ((lowerCD v).1:ℤ)^2 + ((lowerCD v).2:ℤ)^2 := by
    unfold Ainv at hA; exact hA
  have hB' : 4*((lowerCD u).1:ℤ)*((lowerCD u).2:ℤ) - 3*((lowerCD u).1:ℤ)^2
      = 4*((lowerCD v).1:ℤ)*((lowerCD v).2:ℤ) - 3*((lowerCD v).1:ℤ)^2 := by
    unfold Binv at hB; exact hB
  rcases AB_dichotomy _ _ _ _ hu.1 hu.2 hv.1 hv.2 hA' hB' with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · left; constructor <;> omega
  · right; exact ⟨h1, h2⟩

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

lemma tr_1_1_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1]) = (1*(lowerCD U).1 + 2*(lowerCD U).2, 2*(lowerCD U).1 + 3*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_1_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 1, 1]) = (3*(lowerCD U).1 + 5*(lowerCD U).2, 5*(lowerCD U).1 + 8*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_1_1_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 1, 1, 1]) = (5*(lowerCD U).1 + 8*(lowerCD U).2, 8*(lowerCD U).1 + 13*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_1_2 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 1, 2]) = (3*(lowerCD U).1 + 5*(lowerCD U).2, 8*(lowerCD U).1 + 13*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_1_2_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 1, 2, 1]) = (8*(lowerCD U).1 + 13*(lowerCD U).2, 11*(lowerCD U).1 + 18*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_2_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 2, 1]) = (5*(lowerCD U).1 + 8*(lowerCD U).2, 7*(lowerCD U).1 + 11*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_2_1_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 2, 1, 1]) = (7*(lowerCD U).1 + 11*(lowerCD U).2, 12*(lowerCD U).1 + 19*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_2_2 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 2, 2]) = (5*(lowerCD U).1 + 8*(lowerCD U).2, 12*(lowerCD U).1 + 19*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_2_2_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 2, 2, 1]) = (12*(lowerCD U).1 + 19*(lowerCD U).2, 17*(lowerCD U).1 + 27*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_3_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 3, 1]) = (7*(lowerCD U).1 + 11*(lowerCD U).2, 9*(lowerCD U).1 + 14*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_3_1_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 3, 1, 1]) = (9*(lowerCD U).1 + 14*(lowerCD U).2, 16*(lowerCD U).1 + 25*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_3_2 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 3, 2]) = (7*(lowerCD U).1 + 11*(lowerCD U).2, 16*(lowerCD U).1 + 25*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_1_3_2_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 1, 3, 2, 1]) = (16*(lowerCD U).1 + 25*(lowerCD U).2, 23*(lowerCD U).1 + 36*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_2 (U : List ℕ+) : lowerCD (U ++ [1, 1, 2]) = (1*(lowerCD U).1 + 2*(lowerCD U).2, 3*(lowerCD U).1 + 5*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_2_1 (U : List ℕ+) : lowerCD (U ++ [1, 1, 2, 1]) = (3*(lowerCD U).1 + 5*(lowerCD U).2, 4*(lowerCD U).1 + 7*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_1_2_2 (U : List ℕ+) : lowerCD (U ++ [1, 1, 2, 2]) = (3*(lowerCD U).1 + 5*(lowerCD U).2, 7*(lowerCD U).1 + 12*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_1_1 (U : List ℕ+) : lowerCD (U ++ [1, 2, 1, 1]) = (3*(lowerCD U).1 + 4*(lowerCD U).2, 5*(lowerCD U).1 + 7*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_1_1_1 (U : List ℕ+) : lowerCD (U ++ [1, 2, 1, 1, 1]) = (5*(lowerCD U).1 + 7*(lowerCD U).2, 8*(lowerCD U).1 + 11*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_1_1_2 (U : List ℕ+) : lowerCD (U ++ [1, 2, 1, 1, 2]) = (5*(lowerCD U).1 + 7*(lowerCD U).2, 13*(lowerCD U).1 + 18*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_1_2 (U : List ℕ+) : lowerCD (U ++ [1, 2, 1, 2]) = (3*(lowerCD U).1 + 4*(lowerCD U).2, 8*(lowerCD U).1 + 11*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_1_2_1 (U : List ℕ+) : lowerCD (U ++ [1, 2, 1, 2, 1]) = (8*(lowerCD U).1 + 11*(lowerCD U).2, 11*(lowerCD U).1 + 15*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_2_1 (U : List ℕ+) : lowerCD (U ++ [1, 2, 2, 1]) = (5*(lowerCD U).1 + 7*(lowerCD U).2, 7*(lowerCD U).1 + 10*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_2_1_1 (U : List ℕ+) : lowerCD (U ++ [1, 2, 2, 1, 1]) = (7*(lowerCD U).1 + 10*(lowerCD U).2, 12*(lowerCD U).1 + 17*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_2_2 (U : List ℕ+) : lowerCD (U ++ [1, 2, 2, 2]) = (5*(lowerCD U).1 + 7*(lowerCD U).2, 12*(lowerCD U).1 + 17*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_2_2_1 (U : List ℕ+) : lowerCD (U ++ [1, 2, 2, 2, 1]) = (12*(lowerCD U).1 + 17*(lowerCD U).2, 17*(lowerCD U).1 + 24*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_3_1 (U : List ℕ+) : lowerCD (U ++ [1, 2, 3, 1]) = (7*(lowerCD U).1 + 10*(lowerCD U).2, 9*(lowerCD U).1 + 13*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_3_1_1 (U : List ℕ+) : lowerCD (U ++ [1, 2, 3, 1, 1]) = (9*(lowerCD U).1 + 13*(lowerCD U).2, 16*(lowerCD U).1 + 23*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_3_2 (U : List ℕ+) : lowerCD (U ++ [1, 2, 3, 2]) = (7*(lowerCD U).1 + 10*(lowerCD U).2, 16*(lowerCD U).1 + 23*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_1_2_3_2_1 (U : List ℕ+) : lowerCD (U ++ [1, 2, 3, 2, 1]) = (16*(lowerCD U).1 + 23*(lowerCD U).2, 23*(lowerCD U).1 + 33*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_2 (U : List ℕ+) : lowerCD (U ++ [3, 1, 2]) = (1*(lowerCD U).1 + 4*(lowerCD U).2, 3*(lowerCD U).1 + 11*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_2_1 (U : List ℕ+) : lowerCD (U ++ [3, 1, 2, 1]) = (3*(lowerCD U).1 + 11*(lowerCD U).2, 4*(lowerCD U).1 + 15*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_3_1_1 (U : List ℕ+) : lowerCD (U ++ [3, 1, 3, 1, 1]) = (5*(lowerCD U).1 + 19*(lowerCD U).2, 9*(lowerCD U).1 + 34*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_3_1_1_1 (U : List ℕ+) : lowerCD (U ++ [3, 1, 3, 1, 1, 1]) = (9*(lowerCD U).1 + 34*(lowerCD U).2, 14*(lowerCD U).1 + 53*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_3_1_2 (U : List ℕ+) : lowerCD (U ++ [3, 1, 3, 1, 2]) = (5*(lowerCD U).1 + 19*(lowerCD U).2, 14*(lowerCD U).1 + 53*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_3_1_2_1 (U : List ℕ+) : lowerCD (U ++ [3, 1, 3, 1, 2, 1]) = (14*(lowerCD U).1 + 53*(lowerCD U).2, 19*(lowerCD U).1 + 72*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_3_2 (U : List ℕ+) : lowerCD (U ++ [3, 1, 3, 2]) = (4*(lowerCD U).1 + 15*(lowerCD U).2, 9*(lowerCD U).1 + 34*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_3_2_1 (U : List ℕ+) : lowerCD (U ++ [3, 1, 3, 2, 1]) = (9*(lowerCD U).1 + 34*(lowerCD U).2, 13*(lowerCD U).1 + 49*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_3_2_1_1 (U : List ℕ+) : lowerCD (U ++ [3, 1, 3, 2, 1, 1]) = (13*(lowerCD U).1 + 49*(lowerCD U).2, 22*(lowerCD U).1 + 83*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_3_3 (U : List ℕ+) : lowerCD (U ++ [3, 1, 3, 3]) = (4*(lowerCD U).1 + 15*(lowerCD U).2, 13*(lowerCD U).1 + 49*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tr_3_1_3_3_1 (U : List ℕ+) : lowerCD (U ++ [3, 1, 3, 3, 1]) = (13*(lowerCD U).1 + 49*(lowerCD U).2, 17*(lowerCD U).1 + 64*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; try constructor <;> ring

lemma tie_0 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 2]) ≠ lowerWidth (W ++ [1, 2, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_2, tr_1_2_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_1 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 2, 1]) ≠ lowerWidth (W ++ [1, 2, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_2_1, tr_1_2_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_2 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 2]) ≠ lowerWidth (W ++ [1, 2, 2, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_2, tr_1_2_2_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_3 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 2]) ≠ lowerWidth (W ++ [1, 2, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_2, tr_1_2_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_4 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 2, 1]) ≠ lowerWidth (W ++ [1, 2, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_2_1, tr_1_2_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_5 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 2]) ≠ lowerWidth (W ++ [1, 2, 2, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_2, tr_1_2_2_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_6 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 3, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_3_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_7 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 3, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1_1, tr_1_2_3_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_8 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 3, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_3_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_9 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 3, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_3_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_10 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 3, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1_1, tr_1_2_3_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_11 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 3, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_3_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_12 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_13 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1_1, tr_1_2_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_14 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 2, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_2_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_15 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_16 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1_1, tr_1_2_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_17 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 2, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_2_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_18 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 1, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_1_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_19 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 1, 1, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_1_1_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_20 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_21 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_22 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_1_1_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_23 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_1_1_1_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_24 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_25 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2_1, tr_1_1_1_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_26 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_1_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_27 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_1_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_28 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2_1, tr_1_1_1_1_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_29 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_1_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_30 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_1_1_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_31 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_1_1_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_32 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_33 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3_1, tr_1_1_1_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_34 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_1_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_35 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_1_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_36 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3_1, tr_1_1_1_1_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_37 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 1, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_1_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_38 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_39 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2_1, tr_1_1_1_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_40 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_2_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_41 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_42 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2_1, tr_1_1_1_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_43 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_2_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_44 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_3_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_45 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2_1, tr_1_1_1_3_1] at e1 e2 <;> push_cast at e1 e2 <;> omega


lemma tie_47 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_3_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_48 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2_1, tr_1_1_1_3_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_49 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2, tr_1_1_1_3_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_50 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_51 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3_1, tr_1_1_1_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_52 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_2_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_53 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_54 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3_1, tr_1_1_1_2_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_55 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 2, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_2_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_56 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_3_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_57 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3_1, tr_1_1_1_3_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_58 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_3_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_59 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_3_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_60 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3_1, tr_1_1_1_3_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_61 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 3]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_3, tr_1_1_1_3_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega


lemma tie_63 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 2]) ≠ lowerWidth (W ++ [1, 1, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_2, tr_1_1_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_64 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2_1, tr_1_1_1_3_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_65 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 2, 1]) ≠ lowerWidth (W ++ [1, 1, 1, 3, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_2_1, tr_1_1_1_3_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_66 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_67 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1_1, tr_1_2_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_68 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 1, 1, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_1_1_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_69 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 1, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_1_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_70 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 1, 2]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1_1, tr_1_2_1_2] at e1 e2 <;> push_cast at e1 e2 <;> omega

lemma tie_71 (U W : List ℕ+) (a1 : (lowerCD U).1 ≤ (lowerCD U).2) (a2 : 0 < (lowerCD U).2)
    (b1 : (lowerCD W).1 ≤ (lowerCD W).2) (b2 : 0 < (lowerCD W).2) :
    lowerWidth (U ++ [3, 1, 3, 1, 1]) ≠ lowerWidth (W ++ [1, 2, 1, 2, 1]) := by
  intro htie
  rcases width_tie_dichotomy _ _ htie with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;>
    simp only [tr_3_1_3_1_1, tr_1_2_1_2_1] at e1 e2 <;> push_cast at e1 e2 <;> omega

/-! ### σ-monotonicity glue -/

lemma width_lt_of_sg_lt (u v : List ℕ+) (h : sg u < sg v) : lowerWidth v < lowerWidth u := by
  have hu := sg_pos u
  have hba : 0 < lowerBeta - lowerAlpha := sub_pos.mpr beta_gt_alpha
  rw [width_eq, width_eq]
  exact div_lt_div_of_pos_left hba hu h

lemma sg_le_of_width_le (u v : List ℕ+) (h : lowerWidth u ≤ lowerWidth v) : sg v ≤ sg u := by
  by_contra hcon
  push_neg at hcon
  have := width_lt_of_sg_lt u v hcon
  linarith

lemma tr_3_1 (U : List ℕ+) : lowerCD (U ++ [3,1]) =
    (1*(lowerCD U).1 + 3*(lowerCD U).2, 1*(lowerCD U).1 + 4*(lowerCD U).2) := by
  rw [cd_app]; norm_num [List.foldl_cons, List.foldl_nil]; ring

/-! ### The two σ-ratio bounds needed where the ratio test is silent -/

lemma sgA_ub (U : List ℕ+) (h1 : (lowerCD U).1 ≤ (lowerCD U).2) (h2 : 0 < (lowerCD U).2) :
    sg (U ++ [3,1,2]) ≤ 6 * sg (U ++ [3,1]) := by
  have hc : (0:ℝ) ≤ ((lowerCD U).1 : ℝ) := by positivity
  have he : (1:ℝ) ≤ ((lowerCD U).2 : ℝ) := by exact_mod_cast h2
  have hce : ((lowerCD U).1 : ℝ) ≤ ((lowerCD U).2 : ℝ) := by exact_mod_cast h1
  have he0 : (0:ℝ) ≤ ((lowerCD U).2 : ℝ) := by linarith
  rw [sg_AB, sg_AB]
  simp only [Ainv, Binv, tr_3_1_2, tr_3_1]
  push_cast
  nlinarith [alpha_lb, alpha_ub, hc, he, hce, mul_nonneg hc hc, mul_nonneg hc he0,
    sq_nonneg (((lowerCD U).2:ℝ) - ((lowerCD U).1:ℝ))]

lemma sgB_ub (U : List ℕ+) (h1 : (lowerCD U).1 ≤ (lowerCD U).2) (h2 : 0 < (lowerCD U).2) :
    sg (U ++ [3,1,3,2]) ≤ 58 * sg (U ++ [3,1]) := by
  have hc : (0:ℝ) ≤ ((lowerCD U).1 : ℝ) := by positivity
  have he : (1:ℝ) ≤ ((lowerCD U).2 : ℝ) := by exact_mod_cast h2
  have hce : ((lowerCD U).1 : ℝ) ≤ ((lowerCD U).2 : ℝ) := by exact_mod_cast h1
  have he0 : (0:ℝ) ≤ ((lowerCD U).2 : ℝ) := by linarith
  rw [sg_AB, sg_AB]
  simp only [Ainv, Binv, tr_3_1_3_2, tr_3_1]
  push_cast
  nlinarith [alpha_lb, alpha_ub, hc, he, hce, mul_nonneg hc hc, mul_nonneg hc he0,
    sq_nonneg (((lowerCD U).2:ℝ) - ((lowerCD U).1:ℝ))]

lemma sgC_lb (W : List ℕ+) (h1 : (lowerCD W).1 ≤ (lowerCD W).2) (h2 : 0 < (lowerCD W).2) :
    16 * sg W ≤ sg (W ++ [1,1,1]) := by
  have hc : (0:ℝ) ≤ ((lowerCD W).1 : ℝ) := by positivity
  have he : (1:ℝ) ≤ ((lowerCD W).2 : ℝ) := by exact_mod_cast h2
  have hce : ((lowerCD W).1 : ℝ) ≤ ((lowerCD W).2 : ℝ) := by exact_mod_cast h1
  have he0 : (0:ℝ) ≤ ((lowerCD W).2 : ℝ) := by linarith
  rw [sg_AB, sg_AB]
  simp only [Ainv, Binv, tr_1_1_1]
  push_cast
  nlinarith [alpha_lb, alpha_ub, hc, he, hce, mul_nonneg hc hc, mul_nonneg hc he0,
    sq_nonneg (((lowerCD W).2:ℝ) - ((lowerCD W).1:ℝ))]

lemma sgD_lb (W : List ℕ+) (h1 : (lowerCD W).1 ≤ (lowerCD W).2) (h2 : 0 < (lowerCD W).2) :
    380 * sg W ≤ sg (W ++ [1,1,1,3,1]) := by
  have hc : (0:ℝ) ≤ ((lowerCD W).1 : ℝ) := by positivity
  have he : (1:ℝ) ≤ ((lowerCD W).2 : ℝ) := by exact_mod_cast h2
  have hce : ((lowerCD W).1 : ℝ) ≤ ((lowerCD W).2 : ℝ) := by exact_mod_cast h1
  have he0 : (0:ℝ) ≤ ((lowerCD W).2 : ℝ) := by linarith
  rw [sg_AB, sg_AB]
  simp only [Ainv, Binv, tr_1_1_1_3_1]
  push_cast
  nlinarith [alpha_lb, alpha_ub, hc, he, hce, mul_nonneg hc hc, mul_nonneg hc he0,
    sq_nonneg (((lowerCD W).2:ℝ) - ((lowerCD W).1:ℝ))]

/-! ### Swap invariance of `lowerEndpoint` -/

lemma norm_swap (a b : List ℕ+) (h : lowerWidth b ≠ lowerWidth a) :
    lowerNormalize (a,b) = lowerNormalize (b,a) := by
  classical
  by_cases hw : lowerWidth b ≤ lowerWidth a
  · have hw' : ¬ lowerWidth a ≤ lowerWidth b := fun hc => h (le_antisymm hw hc)
    simp [lowerNormalize, hw, hw']
  · have hw' : lowerWidth a ≤ lowerWidth b := le_of_not_ge hw
    simp [lowerNormalize, hw, hw']

lemma endpoint_swap_equal (a b : List ℕ+) (u : Bool)
    (hpar : a.length % 2 = b.length % 2) (h : lowerWidth b ≠ lowerWidth a) :
    lowerEndpoint (a,b) u = lowerEndpoint (b,a) u := by
  classical
  have hE : lowerEndpointWords (a,b) u = lowerEqualWords (a,b) u := by
    simp [lowerEndpointWords, hpar]
  have hE' : lowerEndpointWords (b,a) u = lowerEqualWords (b,a) u := by
    simp [lowerEndpointWords, hpar.symm]
  have hn := norm_swap a b h
  by_cases hw : lowerWidth b ≤ lowerWidth a
  · have hw' : ¬ lowerWidth a ≤ lowerWidth b := fun hc => h (le_antisymm hw hc)
    simp only [lowerEndpoint, hE, hE', lowerEqualWords]
    simp only [hn]
    simp [hw, hw']
    ring
  · have hw' : lowerWidth a ≤ lowerWidth b := le_of_not_ge hw
    simp only [lowerEndpoint, hE, hE', lowerEqualWords]
    simp only [hn]
    simp [hw, hw']
    ring

lemma cd_natb (w : List ℕ+) : (lowerCD w).1 ≤ (lowerCD w).2 ∧ 0 < (lowerCD w).2 := by
  have h1 := cdR_le w
  have h2 := cdR_pos w
  unfold cdR at h1 h2
  simp only at h1 h2
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2.2

/-! ### The two directional bounds (where the ratio test is silent) -/

lemma dir_A (U W : List ℕ+) (hnorm : lowerWidth W ≤ lowerWidth (U ++ [3,1])) :
    lowerWidth (W ++ [1,1,1]) < lowerWidth (U ++ [3,1,2]) := by
  obtain ⟨a1, a2⟩ := cd_natb U
  obtain ⟨b1, b2⟩ := cd_natb W
  have h1 := sgA_ub U a1 a2
  have h2 := sgC_lb W b1 b2
  have h3 := sg_le_of_width_le W (U ++ [3,1]) hnorm
  have hp := sg_pos (U ++ [3,1])
  exact width_lt_of_sg_lt _ _ (by linarith)

lemma dir_B (U W : List ℕ+) (hnorm : lowerWidth W ≤ lowerWidth (U ++ [3,1])) :
    lowerWidth (W ++ [1,1,1,3,1]) < lowerWidth (U ++ [3,1,3,2]) := by
  obtain ⟨a1, a2⟩ := cd_natb U
  obtain ⟨b1, b2⟩ := cd_natb W
  have h1 := sgB_ub U a1 a2
  have h2 := sgD_lb W b1 b2
  have h3 := sg_le_of_width_le W (U ++ [3,1]) hnorm
  have hp := sg_pos (U ++ [3,1])
  exact width_lt_of_sg_lt _ _ (by linarith)

/-! ### Mixed-parity swap invariance -/

lemma endpoint_swap_mixed (a b : List ℕ+) (u : Bool)
    (hpar : ¬ (a.length % 2 = b.length % 2)) (h : lowerWidth b ≠ lowerWidth a)
    (hv1 : lowerWidth b ≤ lowerWidth a → lowerWidth b ≠ lowerWidth (a ++ [1]))
    (hv2 : lowerWidth a ≤ lowerWidth b → lowerWidth a ≠ lowerWidth (b ++ [1])) :
    lowerEndpoint (a,b) u = lowerEndpoint (b,a) u := by
  classical
  have hpar' : ¬ (b.length % 2 = a.length % 2) := fun hc => hpar hc.symm
  have q1 : b.length % 2 = (a.length + 1) % 2 := by omega
  have q2 : (a.length + 1) % 2 = b.length % 2 := by omega
  have q3 : a.length % 2 = (b.length + 1) % 2 := by omega
  have q4 : (b.length + 1) % 2 = a.length % 2 := by omega
  by_cases hw : lowerWidth b ≤ lowerWidth a
  · have hw' : ¬ lowerWidth a ≤ lowerWidth b := fun hc => h (le_antisymm hw hc)
    by_cases hu : u = decide (a.length % 2 = 0)
    · have hpar2 : (a ++ [1]).length % 2 = b.length % 2 := by simp; omega
      have key := endpoint_swap_equal (a ++ [1]) b u hpar2 (hv1 hw)
      have e1 : lowerEndpointWords (a,b) u = lowerEqualWords (a ++ [1], b) u := by
        simp [lowerEndpointWords, hpar, hw, hw', hu]
      have e2 : lowerEndpointWords (b,a) u = lowerEqualWords (b, a ++ [1]) u := by
        simp [lowerEndpointWords, hpar', hw, hw', hu]
      have k1 : lowerEndpointWords (a ++ [1], b) u = lowerEqualWords (a ++ [1], b) u := by
        simp [lowerEndpointWords, q2]
      have k2 : lowerEndpointWords (b, a ++ [1]) u = lowerEqualWords (b, a ++ [1]) u := by
        simp [lowerEndpointWords, q1]
      simp only [lowerEndpoint, e1, e2]
      simp only [lowerEndpoint, k1, k2] at key
      exact key
    · simp [lowerEndpoint, lowerEndpointWords, hpar, hpar', hw, hw', hu, lowerNaturalWords]
      ring
  · have hw' : lowerWidth a ≤ lowerWidth b := le_of_not_ge hw
    have hwne : ¬ lowerWidth a ≤ lowerWidth b → False := fun hc => hc hw'
    by_cases hu : u = decide (b.length % 2 = 0)
    · have hpar2 : (b ++ [1]).length % 2 = a.length % 2 := by simp; omega
      have key := endpoint_swap_equal a (b ++ [1]) u hpar2.symm (fun hc => hv2 hw' hc.symm)
      have e1 : lowerEndpointWords (a,b) u = lowerEqualWords (a, b ++ [1]) u := by
        simp [lowerEndpointWords, hpar, hw, hw', hu]
      have e2 : lowerEndpointWords (b,a) u = lowerEqualWords (b ++ [1], a) u := by
        simp [lowerEndpointWords, hpar', hw, hw', hu]
      have k1 : lowerEndpointWords (a, b ++ [1]) u = lowerEqualWords (a, b ++ [1]) u := by
        simp [lowerEndpointWords, q3]
      have k2 : lowerEndpointWords (b ++ [1], a) u = lowerEqualWords (b ++ [1], a) u := by
        simp [lowerEndpointWords, q4]
      simp only [lowerEndpoint, e1, e2]
      simp only [lowerEndpoint, k1, k2] at key
      exact key
    · simp [lowerEndpoint, lowerEndpointWords, hpar, hpar', hw, hw', hu, lowerNaturalWords]
      ring

/-- An element of `l.tail.dropLast` lies in `l` and is neither its head nor its last entry. -/
lemma mem_tail_dropLast {α : Type} [DecidableEq α] (l : List α) (h : l.Nodup)
    (a b x : α) (hh : l.head? = some a) (hl : l.getLast? = some b)
    (hx : x ∈ l.tail.dropLast) : x ∈ l ∧ x ≠ a ∧ x ≠ b := by
  cases l with
  | nil => simp at hh
  | cons c t =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.tail_cons] at hx
    have htsub : x ∈ t := List.dropLast_subset _ hx
    have hat : c ∉ t := (List.nodup_cons.mp h).1
    have hnt : t.Nodup := (List.nodup_cons.mp h).2
    have hne : t ≠ [] := by intro hemp; rw [hemp] at hx; simp at hx
    have hlt : t.getLast? = some b := by
      rw [List.getLast?_cons_of_ne_nil hne] at hl; exact hl
    have hgl : t.getLast hne = b := by
      have hg := List.getLast?_eq_some_getLast hne
      rw [hg] at hlt
      exact Option.some_inj.mp hlt
    have hsplit : t.dropLast ++ [t.getLast hne] = t := List.dropLast_append_getLast hne
    have hbnot : t.getLast hne ∉ t.dropLast := by
      have hnd2 : (t.dropLast ++ [t.getLast hne]).Nodup := by rw [hsplit]; exact hnt
      rw [List.nodup_append] at hnd2
      intro hmem
      exact hnd2.2.2 _ hmem _ (by simp) rfl
    refine ⟨List.mem_cons_of_mem _ htsub, ?_, ?_⟩
    · intro he; subst he; exact hat (hh ▸ htsub)
    · intro he; subst he; exact hbnot (hgl ▸ hx)

/-! ### Assembly -/

lemma norm_eq (p : LowerPair) :
    lowerNormalize p = if lowerWidth p.2 ≤ lowerWidth p.1 then p else (p.2, p.1) := rfl

lemma child_eq (p : LowerPair) (l : LowerLabel) :
    lowerChild p l = ((lowerNormalize p).1 ++ l.1.reverse, (lowerNormalize p).2 ++ l.2) := rfl

lemma norm_width (p : LowerPair) :
    lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
  rw [norm_eq]; split_ifs with hc
  · exact hc
  · exact le_of_not_ge hc

end ForkDev

open ForkDev

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem solution (p : LowerPair) (path : LatePath) (hm : lateMatches p path.right3)
    (hv : latePathValid lateCatalog path)
    (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n) :
    lateForkAlignment p path := by
  classical
  intro n hnmem d hd upper
  obtain ⟨lab, wide, bnd⟩ := n
  obtain ⟨hmixp, hL, -⟩ := hm
  obtain ⟨-, -, hnd, hhead, hlast, hcands, -, -, hmapl, -, -, -, -⟩ := hv
  have hlab : lab ∈ path.route.tail.dropLast := by
    rw [← hmapl]
    exact List.mem_map.mpr ⟨⟨lab, wide, bnd⟩, hnmem, rfl⟩
  obtain ⟨hlr, hne1, hne2⟩ :=
    mem_tail_dropLast path.route hnd _ _ _ hhead hlast hlab
  have hcand : lab ∈ lowerLateCandidates := hcands _ hlr
  have hparp : p.1.length % 2 = p.2.length % 2 := by
    unfold lowerMixed at hmixp; omega
  have hparP : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
    rw [norm_eq]; split_ifs with hc
    · exact hparp
    · exact hparp.symm
  obtain ⟨U, hU⟩ : ∃ U, (lowerNormalize p).1 = U ++ [3,1] := by
    obtain ⟨t, ht⟩ := hL; exact ⟨t, ht.symm⟩
  have bU := cd_natb U
  have bW := cd_natb (lowerNormalize p).2
  have hnw : lowerWidth (lowerNormalize p).2 ≤ lowerWidth (U ++ [3,1]) := by
    rw [← hU]; exact norm_width p
  have hUW : U.length % 2 = (lowerNormalize p).2.length % 2 := by
    have h := hparP; rw [hU] at h; simp at h; omega
  have hnh := hn _ hnmem
  simp only [lateNormalizationHolds] at hnh
  have hfork : lateForkWords ⟨lab, wide, bnd⟩ d =
      (if wide then (lab.1.reverse, lab.2 ++ [d]) else (lab.1.reverse ++ [d], lab.2)) := by
    unfold lateForkWords lateWords lowerHistorySet lowerHistoryPick
    split_ifs <;> rfl
  simp only [lowerLateCandidates, List.mem_cons, List.not_mem_nil, or_false] at hcand
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  cases wide
  · -- left-wide: pure concatenation, no geometry
    simp only [Bool.false_eq_true, if_false] at hnh hfork
    congr 1
    rw [child_eq (lowerChild p lab) ([d], []), hnh, hfork]
    simp only [child_eq, lowerHistoryAppend, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_nil, List.append_assoc]
  · -- right-wide: the two pairs are swaps of one another
    simp only [if_true] at hnh hfork
    have hgoal : lowerChild (lowerChild p lab) ([d], []) =
        ((lowerChild p lab).2 ++ [d], (lowerChild p lab).1) := by
      rw [child_eq (lowerChild p lab) ([d], []), hnh]
      simp
    have hrhs : lowerHistoryAppend (lowerNormalize p) (lateForkWords ⟨lab, true, bnd⟩ d) =
        ((lowerChild p lab).1, (lowerChild p lab).2 ++ [d]) := by
      rw [hfork]
      simp only [lowerHistoryAppend, child_eq, List.append_assoc]
    rw [hgoal, hrhs]
    simp only [child_eq]
    rcases hcand with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals rcases hd with rfl | rfl
    · exact absurd rfl hne1
    · exact absurd rfl hne1
    · exact absurd rfl hne2
    · exact absurd rfl hne2
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_0 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_1 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_2 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_3 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_4 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_5 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_6 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_7 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_8 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_9 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_10 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_11 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_12 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_13 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_14 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_15 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_16 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_17 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_18 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_19 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_20 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_21 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_22 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_23 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_24 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_25 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_26 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_27 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_28 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_29 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_30 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_31 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_32 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_33 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_34 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_35 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_36 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_37 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_38 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_39 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_40 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_41 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_42 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_43 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_44 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_45 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun hle => absurd hle (not_le.mpr (dir_B U (lowerNormalize p).2 hnw)))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_47 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_48 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_49 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_50 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_51 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_52 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_53 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_54 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_55 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_56 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_57 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_58 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_59 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_60 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_61 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (dir_A U (lowerNormalize p).2 hnw).ne).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_63 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_64 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_equal _ _ _ (by simp; omega) (by simpa using (tie_65 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_66 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_67 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_68 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm
    · simp only [hU, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append, List.append_assoc, List.append_nil]
      exact (endpoint_swap_mixed _ _ _ (by simp; omega) (by simpa using (tie_69 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm)
        (fun _ => by simpa using (tie_70 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2).symm) (fun _ => by simpa using (tie_71 U (lowerNormalize p).2 bU.1 bU.2 bW.1 bW.2))).symm

#print axioms solution
