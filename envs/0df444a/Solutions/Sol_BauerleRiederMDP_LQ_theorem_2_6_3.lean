-- Prove2me | solution 1 for BauerleRiederMDP.LQ.theorem_2_6_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:15:26.044898+00:00
-- url     : https://prove2.me/submissions/39d5089e-829f-41b9-808d-4b4636fee6a8

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction
import Definitions.Def_BauerleRiederMDP_LQ_Model
import Definitions.Def_BauerleRiederMDP_LQ_Riccati

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix

namespace LQ52e

open BauerleRiederMDP.LQ MDPFinance.Bellman

/-! ### Extended-real integral facts -/

lemma aux_toENNReal (r : ℝ) : ((r : EReal) ⊔ 0).toENNReal = ENNReal.ofReal r := by
  rcases le_total r 0 with hx | hx
  · have : (r : EReal) ≤ 0 := by exact_mod_cast hx
    rw [sup_of_le_right this, ENNReal.ofReal_of_nonpos hx]
    simp
  · have : (0 : EReal) ≤ r := by exact_mod_cast hx
    rw [sup_of_le_left this, EReal.real_coe_toENNReal]

lemma erealIntegral_mono {E : Type*} [MeasurableSpace E] (μ : Measure E) {f g : E → EReal}
    (h : ∀ x, f x ≤ g x) : erealIntegral μ f ≤ erealIntegral μ g := by
  unfold erealIntegral
  refine add_le_add ?_ ?_
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) 0))
  · exact EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun x => EReal.toENNReal_le_toENNReal
        (sup_le_sup_right (EReal.neg_le_neg_iff.mpr (h x)) 0)))

lemma erealIntegral_coe {E : Type*} [MeasurableSpace E] (μ : Measure E) {h : E → ℝ}
    (hi : Integrable h μ) :
    erealIntegral μ (fun x => (h x : EReal)) = ((∫ x, h x ∂μ : ℝ) : EReal) := by
  unfold erealIntegral
  simp only [← EReal.coe_neg, aux_toENNReal]
  have f1 : ∫⁻ x, ENNReal.ofReal (h x) ∂μ ≠ ⊤ := hi.lintegral_lt_top.ne
  have f2 : ∫⁻ x, ENNReal.ofReal (-h x) ∂μ ≠ ⊤ := hi.neg.lintegral_lt_top.ne
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, ← EReal.coe_ennreal_toReal f1,
    ← EReal.coe_ennreal_toReal f2, ← EReal.coe_neg, ← EReal.coe_add, sub_eq_add_neg]

/-! ### Matrix expectations -/

lemma integ_entry {Z : Type*} [MeasurableSpace Z] {ν : Measure Z} {m p q : ℕ}
    (U : Z → Matrix (Fin m) (Fin p) ℝ) (V : Z → Matrix (Fin m) (Fin q) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ)
    (hU : ∀ i j, MemLp (fun z => U z i j) 2 ν) (hV : ∀ i j, MemLp (fun z => V z i j) 2 ν)
    (i : Fin p) (j : Fin q) : Integrable (fun z => ((U z)ᵀ * Q * V z) i j) ν := by
  simp only [mul_apply, transpose_apply, Finset.sum_mul]
  refine integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => ?_
  have h := ((hU k i).integrable_mul (hV l j)).const_mul (Q k l)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.mul_apply]
  ring

lemma integ_dot {Z : Type*} [MeasurableSpace Z] {ν : Measure Z} {k l : ℕ}
    (F : Z → Matrix (Fin k) (Fin l) ℝ) (hF : ∀ i j, Integrable (fun z => F z i j) ν)
    (x : Fin k → ℝ) (y : Fin l → ℝ) : Integrable (fun z => x ⬝ᵥ (F z *ᵥ y)) ν := by
  simp only [dotProduct, mulVec]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_finsetSum _ fun j _ => (hF i j).mul_const (y j)).const_mul (x i)

lemma dot_matExp {m d k l : ℕ}
    (ν : Measure (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ))
    (F : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ → Matrix (Fin k) (Fin l) ℝ)
    (hF : ∀ i j, Integrable (fun z => F z i j) ν) (x : Fin k → ℝ) (y : Fin l → ℝ) :
    x ⬝ᵥ (matExp ν F *ᵥ y) = ∫ z, x ⬝ᵥ (F z *ᵥ y) ∂ν := by
  simp only [dotProduct, mulVec, matExp, of_apply]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_finsetSum _ fun j _ => (hF i j).mul_const (y j)).const_mul (x i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hF i j).mul_const (y j)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]

lemma key_dot {m p q : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (U : Matrix (Fin m) (Fin p) ℝ)
    (V : Matrix (Fin m) (Fin q) ℝ) (u : Fin p → ℝ) (v : Fin q → ℝ) :
    (U *ᵥ u) ⬝ᵥ (Q *ᵥ (V *ᵥ v)) = u ⬝ᵥ ((Uᵀ * Q * V) *ᵥ v) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm, dotProduct_mulVec,
    dotProduct_comm]

lemma qf_expand {m d : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) (a : Fin d → ℝ)
    (z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ) :
    quadForm Q (lqTransition x a z) = x ⬝ᵥ ((z.1ᵀ * Q * z.1) *ᵥ x) + x ⬝ᵥ ((z.1ᵀ * Q * z.2) *ᵥ a)
      + (a ⬝ᵥ ((z.2ᵀ * Q * z.1) *ᵥ x) + a ⬝ᵥ ((z.2ᵀ * Q * z.2) *ᵥ a)) := by
  simp only [quadForm, lqTransition, mulVec_add, add_dotProduct, dotProduct_add, key_dot]
  ring

lemma integral_qf {m d : ℕ} (ν : Measure (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ))
    (hA : ∀ i j, MemLp (fun z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ => z.1 i j) 2 ν)
    (hB : ∀ i j, MemLp (fun z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ => z.2 i j) 2 ν)
    (Q : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) (a : Fin d → ℝ) :
    Integrable (fun z => quadForm Q (lqTransition x a z)) ν ∧
    ∫ z, quadForm Q (lqTransition x a z) ∂ν =
      x ⬝ᵥ (matExp ν (fun z => z.1ᵀ * Q * z.1) *ᵥ x) + x ⬝ᵥ (matExp ν (fun z => z.1ᵀ * Q * z.2) *ᵥ a)
      + (a ⬝ᵥ (matExp ν (fun z => z.2ᵀ * Q * z.1) *ᵥ x)
        + a ⬝ᵥ (matExp ν (fun z => z.2ᵀ * Q * z.2) *ᵥ a)) := by
  have e11 := integ_entry (ν := ν) (fun z => z.1) (fun z => z.1) Q hA hA
  have e12 := integ_entry (ν := ν) (fun z => z.1) (fun z => z.2) Q hA hB
  have e21 := integ_entry (ν := ν) (fun z => z.2) (fun z => z.1) Q hB hA
  have e22 := integ_entry (ν := ν) (fun z => z.2) (fun z => z.2) Q hB hB
  have i1 := integ_dot _ e11 x x
  have i2 := integ_dot _ e12 x a
  have i3 := integ_dot _ e21 a x
  have i4 := integ_dot _ e22 a a
  have i12 : Integrable (fun z => x ⬝ᵥ ((z.1ᵀ * Q * z.1) *ᵥ x) + x ⬝ᵥ ((z.1ᵀ * Q * z.2) *ᵥ a)) ν :=
    i1.add i2
  have i34 : Integrable (fun z => a ⬝ᵥ ((z.2ᵀ * Q * z.1) *ᵥ x) + a ⬝ᵥ ((z.2ᵀ * Q * z.2) *ᵥ a)) ν :=
    i3.add i4
  simp only [qf_expand]
  refine ⟨i12.add i34, ?_⟩
  rw [integral_add i12 i34, integral_add i1 i2, integral_add i3 i4,
    dot_matExp ν _ e11 x x, dot_matExp ν _ e12 x a, dot_matExp ν _ e21 a x,
    dot_matExp ν _ e22 a a]

lemma matExp_transpose {m d k l : ℕ}
    (ν : Measure (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ))
    (U : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ → Matrix (Fin m) (Fin k) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ → Matrix (Fin m) (Fin l) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Qᵀ = Q) :
    (matExp ν (fun z => (U z)ᵀ * Q * V z))ᵀ = matExp ν (fun z => (V z)ᵀ * Q * U z) := by
  ext i j
  simp only [matExp, transpose_apply, of_apply]
  congr 1
  funext z
  rw [← transpose_apply ((V z)ᵀ * Q * U z), transpose_mul, transpose_mul, transpose_transpose, hQ,
    Matrix.mul_assoc]

lemma complete_sq {m d : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin d) ℝ)
    (Bm : Matrix (Fin d) (Fin m) ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hR : R = Bmᵀ) (hS : Sᵀ = S)
    (hSu : IsUnit S.det) (x : Fin m → ℝ) (a : Fin d → ℝ) :
    x ⬝ᵥ (P *ᵥ x) + x ⬝ᵥ (R *ᵥ a) + (a ⬝ᵥ (Bm *ᵥ x) + a ⬝ᵥ (S *ᵥ a)) =
      x ⬝ᵥ ((P - R * S⁻¹ * Bm) *ᵥ x) + quadForm S (a - (-(S⁻¹ * Bm)) *ᵥ x) := by
  have sw : ∀ {p q : ℕ} (u : Fin p → ℝ) (Mx : Matrix (Fin p) (Fin q) ℝ) (v : Fin q → ℝ),
      u ⬝ᵥ (Mx *ᵥ v) = v ⬝ᵥ (Mxᵀ *ᵥ u) := by
    intro p q u Mx v
    rw [mulVec_transpose, dotProduct_mulVec, dotProduct_comm]
  have e1 : (-(S⁻¹ * Bm)) *ᵥ x = -(S⁻¹ *ᵥ (Bm *ᵥ x)) := by
    rw [neg_mulVec, ← mulVec_mulVec]
  have e2 : S *ᵥ (S⁻¹ *ᵥ (Bm *ᵥ x)) = Bm *ᵥ x := by
    rw [mulVec_mulVec (Bm *ᵥ x) S S⁻¹, mul_nonsing_inv _ hSu, one_mulVec]
  have e3 : (R * S⁻¹ * Bm) *ᵥ x = R *ᵥ (S⁻¹ *ᵥ (Bm *ᵥ x)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  have c1 : x ⬝ᵥ (R *ᵥ a) = a ⬝ᵥ (Bm *ᵥ x) := by rw [sw, hR, transpose_transpose]
  have c2 : x ⬝ᵥ (R *ᵥ (S⁻¹ *ᵥ (Bm *ᵥ x))) = (S⁻¹ *ᵥ (Bm *ᵥ x)) ⬝ᵥ (Bm *ᵥ x) := by
    rw [sw, hR, transpose_transpose]
  have c3 : (S⁻¹ *ᵥ (Bm *ᵥ x)) ⬝ᵥ (S *ᵥ a) = a ⬝ᵥ (Bm *ᵥ x) := by rw [sw, hS, e2]
  rw [e1, sub_neg_eq_add]
  unfold quadForm
  rw [sub_mulVec, dotProduct_sub, e3, c2, mulVec_add, dotProduct_add, add_dotProduct,
    add_dotProduct, e2, c3, c1]
  ring

lemma symm_of_pd {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (h : A.PosDef) : Aᵀ = A := by
  have := h.isHermitian
  unfold Matrix.IsHermitian at this
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-! ### One Riccati step -/

lemma step_facts {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) (n : ℕ) (hn : n < N)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef) :
    (∀ (x : Fin m → ℝ) (a : Fin d → ℝ),
      Integrable (fun z => quadForm Q (lqTransition x a z)) (M.ν (n + 1) : Measure _)) ∧
    (∀ x a, M.costArg n Q x a =
      quadForm (M.riccatiStep n Q) x + quadForm (M.EBQB n Q) (a - M.gainOf n Q *ᵥ x)) ∧
    (M.EBQB n Q).PosDef ∧ (M.riccatiStep n Q).PosDef := by
  have hA := hM.memLp_A (n + 1) (by omega) (by omega)
  have hB := hM.memLp_B (n + 1) (by omega) (by omega)
  have hS : (M.EBQB n Q).PosDef := hM.posDef_EBQB (n + 1) (by omega) (by omega) Q hQ
  have hSu : IsUnit (M.EBQB n Q).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hQt : Qᵀ = Q := symm_of_pd hQ
  have hQnt : (M.Q n)ᵀ = M.Q n := symm_of_pd (hM.posDef_Q n hn.le)
  have hSt : (M.EBQB n Q)ᵀ = M.EBQB n Q := matExp_transpose _ (fun z => z.2) (fun z => z.2) Q hQt
  have hP : (M.EAQA n Q)ᵀ = M.EAQA n Q := matExp_transpose _ (fun z => z.1) (fun z => z.1) Q hQt
  have hR : M.EAQB n Q = (M.EBQA n Q)ᵀ :=
    (matExp_transpose _ (fun z => z.2) (fun z => z.1) Q hQt).symm
  have hRt : (M.EAQB n Q)ᵀ = M.EBQA n Q := by rw [hR, transpose_transpose]
  have hcost : ∀ x a, M.costArg n Q x a =
      quadForm (M.riccatiStep n Q) x + quadForm (M.EBQB n Q) (a - M.gainOf n Q *ᵥ x) := by
    intro x a
    have h1 : (∫ z, quadForm Q (lqTransition x a z) ∂(M.ν (n + 1) : Measure _)) =
        x ⬝ᵥ (M.EAQA n Q *ᵥ x) + x ⬝ᵥ (M.EAQB n Q *ᵥ a)
          + (a ⬝ᵥ (M.EBQA n Q *ᵥ x) + a ⬝ᵥ (M.EBQB n Q *ᵥ a)) :=
      (integral_qf _ hA hB Q x a).2
    have h2 := complete_sq (M.EAQA n Q) (M.EAQB n Q) (M.EBQA n Q) (M.EBQB n Q) hR hSt hSu x a
    rw [LQData.costArg, h1, h2]
    simp only [LQData.riccatiStep, LQData.gainOf]
    unfold quadForm
    simp only [sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add]
    ring
  refine ⟨fun x a => (integral_qf _ hA hB Q x a).1, hcost, hS, ?_⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · show (M.riccatiStep n Q)ᴴ = M.riccatiStep n Q
    rw [conjTranspose_eq_transpose_of_trivial]
    simp only [LQData.riccatiStep, transpose_sub, transpose_add, transpose_mul,
      transpose_nonsing_inv, hSt, hP, hQnt, hRt, Matrix.mul_assoc]
    rw [hR]
  · rw [star_trivial]
    have e := hcost x (M.gainOf n Q *ᵥ x)
    have q0 : quadForm (M.EBQB n Q) 0 = 0 := by simp [quadForm]
    rw [sub_self, q0, add_zero] at e
    change 0 < quadForm (M.riccatiStep n Q) x
    rw [← e, LQData.costArg]
    have hpos : 0 < quadForm (M.Q n) x := by
      have := (posDef_iff_dotProduct_mulVec.mp (hM.posDef_Q n hn.le)).2 hx
      rwa [star_trivial] at this
    have hnn : 0 ≤ ∫ z, quadForm Q (lqTransition x (M.gainOf n Q *ᵥ x) z)
        ∂(M.ν (n + 1) : Measure _) := by
      refine integral_nonneg fun z => ?_
      have := (posSemidef_iff_dotProduct_mulVec.mp hQ.posSemidef).2
        (lqTransition x (M.gainOf n Q *ᵥ x) z)
      rw [star_trivial] at this
      exact this
    linarith

lemma Qt_N {m d N : ℕ} (M : LQData m d N) : M.Qt N = M.Q N := by
  rw [LQData.Qt, if_neg (lt_irrefl N)]

lemma Qt_lt {m d N : ℕ} (M : LQData m d N) {n : ℕ} (hn : n < N) :
    M.Qt n = M.riccatiStep n (M.Qt (n + 1)) := by
  rw [LQData.Qt, if_pos hn]

lemma Qt_pd {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) : ∀ n ≤ N, (M.Qt n).PosDef := by
  have key : ∀ k, k ≤ N → (M.Qt (N - k)).PosDef := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.sub_zero, Qt_N]; exact hM.posDef_Q N le_rfl
    | succ k ih =>
      intro hk
      have h1 : N - (k + 1) < N := by omega
      have h2 : N - (k + 1) + 1 = N - k := by omega
      rw [Qt_lt M h1, h2]
      exact (step_facts M hM _ h1 _ (ih (by omega))).2.2.2
  intro n hn
  have := key (N - n) (by omega)
  rwa [Nat.sub_sub_self hn] at this

/-! ### Backward induction over the value recursion -/

lemma main_ind {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) :
    ∀ k n, n + k = N → ∀ (π : Policy M.toMDP) (x : Fin m → ℝ) (acc : ℝ),
      EFromToAcc M.toMDP π (fun x => ((M.toMDP.g x : ℝ) : EReal)) k n x (acc : EReal)
          ≤ ((acc - quadForm (M.Qt n) x : ℝ) : EReal) ∧
      ((∀ j < N, π.1 j = M.fstar j) →
        EFromToAcc M.toMDP π (fun x => ((M.toMDP.g x : ℝ) : EReal)) k n x (acc : EReal)
          = ((acc - quadForm (M.Qt n) x : ℝ) : EReal)) := by
  intro k
  induction k with
  | zero =>
    intro n hn π x acc
    have hQt : M.Qt n = M.Q N := by rw [show n = N by omega]; exact Qt_N M
    have e : EFromToAcc M.toMDP π (fun x => ((M.toMDP.g x : ℝ) : EReal)) 0 n x (acc : EReal)
        = ((acc - quadForm (M.Qt n) x : ℝ) : EReal) := by
      rw [EFromToAcc, hQt]
      show ((acc : ℝ) : EReal) + ((-quadForm (M.Q N) x : ℝ) : EReal)
        = ((acc - quadForm (M.Q N) x : ℝ) : EReal)
      rw [← EReal.coe_add, sub_eq_add_neg]
    exact ⟨e.le, fun _ => e⟩
  | succ k ih =>
    intro n hn π x acc
    have hnN : n < N := by omega
    obtain ⟨hint, hcost, hSpd, -⟩ :=
      step_facts M hM n hnN (M.Qt (n + 1)) (Qt_pd M hM (n + 1) (by omega))
    have hφ : Measurable (lqTransition (m := m) (d := d) x (π.1 n x)) :=
      (measurable_lqTransition (m := m) (d := d)).comp
        (measurable_const.prodMk measurable_id :
          Measurable fun z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ =>
            ((x, π.1 n x), z))
    have hker : M.toMDP.Q n (x, π.1 n x)
        = (M.ν (n + 1) : Measure _).map (lqTransition x (π.1 n x)) :=
      disturbanceKernel_apply _ (measurable_lqTransition (m := m) (d := d)) (x, π.1 n x)
    have hr : (acc : EReal) + ((M.toMDP.r n (x, π.1 n x) : ℝ) : EReal)
        = ((acc - quadForm (M.Q n) x : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      rfl
    have hmeas : Measurable
        (fun y : Fin m → ℝ => acc - quadForm (M.Q n) x - quadForm (M.Qt (n + 1)) y) :=
      measurable_const.sub (measurable_quadForm _)
    have hhi : Integrable (fun y => acc - quadForm (M.Q n) x - quadForm (M.Qt (n + 1)) y)
        (M.toMDP.Q n (x, π.1 n x)) := by
      rw [hker, integrable_map_measure hmeas.aestronglyMeasurable hφ.aemeasurable]
      exact (integrable_const _).sub (hint x (π.1 n x))
    have hval : ∫ y, (acc - quadForm (M.Q n) x - quadForm (M.Qt (n + 1)) y)
        ∂(M.toMDP.Q n (x, π.1 n x)) = acc - M.costArg n (M.Qt (n + 1)) x (π.1 n x) := by
      rw [hker, integral_map hφ.aemeasurable hmeas.aestronglyMeasurable]
      show ∫ z, (acc - quadForm (M.Q n) x - quadForm (M.Qt (n + 1)) (lqTransition x (π.1 n x) z))
        ∂(M.ν (n + 1) : Measure _) = _
      rw [integral_sub (integrable_const _) (hint x (π.1 n x))]
      simp [LQData.costArg]
      ring
    rw [EFromToAcc, hr]
    refine ⟨?_, fun hπ => ?_⟩
    · calc _ ≤ erealIntegral (M.toMDP.Q n (x, π.1 n x))
            (fun y => ((acc - quadForm (M.Q n) x - quadForm (M.Qt (n + 1)) y : ℝ) : EReal)) :=
            erealIntegral_mono _ fun y => (ih (n + 1) (by omega) π y _).1
        _ = _ := erealIntegral_coe _ hhi
        _ ≤ _ := by
          rw [hval, Qt_lt M hnN]
          have h1 := hcost x (π.1 n x)
          have hq : 0 ≤ quadForm (M.EBQB n (M.Qt (n + 1)))
              (π.1 n x - M.gainOf n (M.Qt (n + 1)) *ᵥ x) := by
            have := (posSemidef_iff_dotProduct_mulVec.mp hSpd.posSemidef).2
              (π.1 n x - M.gainOf n (M.Qt (n + 1)) *ᵥ x)
            rw [star_trivial] at this
            exact this
          exact EReal.coe_le_coe_iff.mpr (by linarith)
    · calc _ = erealIntegral (M.toMDP.Q n (x, π.1 n x))
            (fun y => ((acc - quadForm (M.Q n) x - quadForm (M.Qt (n + 1)) y : ℝ) : EReal)) := by
            congr 1
            exact funext fun y => (ih (n + 1) (by omega) π y _).2 hπ
        _ = _ := erealIntegral_coe _ hhi
        _ = _ := by
          rw [hval, hπ n hnN, hcost, Qt_lt M hnN,
            show M.fstar n x = M.gainOf n (M.Qt (n + 1)) *ᵥ x from rfl, sub_self]
          simp [quadForm]

lemma Vpi_bound {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) (n : ℕ) (hn : n ≤ N)
    (π : Policy M.toMDP) (x : Fin m → ℝ) :
    Vpi M.toMDP π n x ≤ ((-quadForm (M.Qt n) x : ℝ) : EReal) ∧
    ((∀ j < N, π.1 j = M.fstar j) → Vpi M.toMDP π n x = ((-quadForm (M.Qt n) x : ℝ) : EReal)) := by
  have h := main_ind M hM (N - n) n (by omega) π x 0
  rw [EReal.coe_zero, zero_sub] at h
  exact h

lemma Vcost_eq {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) (n : ℕ) (hn : n ≤ N)
    (x : Fin m → ℝ) : M.Vcost n x = ((quadForm (M.Qt n) x : ℝ) : EReal) := by
  let πs : Policy M.toMDP := Subtype.mk (fun j => M.fstar j)
    ⟨fun j => by
      show Measurable (fun y => M.gainOf j (M.Qt (j + 1)) *ᵥ y)
      exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable,
     fun _ _ _ => Set.mem_univ _⟩
  have hV : V M.toMDP n x = ((-quadForm (M.Qt n) x : ℝ) : EReal) := by
    apply le_antisymm
    · unfold MDPFinance.Bellman.V
      exact iSup_le fun π => (Vpi_bound M hM n hn π x).1
    · unfold MDPFinance.Bellman.V
      exact le_iSup_of_le πs ((Vpi_bound M hM n hn πs x).2 (fun j _ => rfl)).ge
  show -V M.toMDP n x = _
  rw [hV, ← EReal.coe_neg, neg_neg]

theorem final {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) :
    (∀ n ≤ N, (M.Qt n).IsSymm ∧ (M.Qt n).PosSemidef ∧
      ∀ x : Fin m → ℝ, M.Vcost n x = ((quadForm (M.Qt n) x : ℝ) : EReal)) ∧
    (∀ π : MDPFinance.Bellman.Policy M.toMDP, (∀ n < N, π.1 n = M.fstar n) →
      ∀ n ≤ N, ∀ x : Fin m → ℝ, M.VcostPi π n x = M.Vcost n x) := by
  refine ⟨fun n hn => ⟨?_, (Qt_pd M hM n hn).posSemidef, fun x => Vcost_eq M hM n hn x⟩,
    fun π hπ n hn x => ?_⟩
  · exact symm_of_pd (Qt_pd M hM n hn)
  · rw [Vcost_eq M hM n hn x]
    show -Vpi M.toMDP π n x = _
    rw [(Vpi_bound M hM n hn π x).2 hπ, ← EReal.coe_neg, neg_neg]

end LQ52e

open BauerleRiederMDP.LQ MeasureTheory ProbabilityTheory Matrix in
theorem solution {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) :
    (∀ n ≤ N, (M.Qt n).IsSymm ∧ (M.Qt n).PosSemidef ∧
      ∀ x : Fin m → ℝ, M.Vcost n x = ((quadForm (M.Qt n) x : ℝ) : EReal)) ∧
    (∀ π : MDPFinance.Bellman.Policy M.toMDP, (∀ n < N, π.1 n = M.fstar n) →
      ∀ n ≤ N, ∀ x : Fin m → ℝ, M.VcostPi π n x = M.Vcost n x) := by
  exact LQ52e.final M hM
