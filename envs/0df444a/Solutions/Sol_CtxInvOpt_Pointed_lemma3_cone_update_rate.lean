-- Prove2me | solution 1 for CtxInvOpt.Pointed.lemma3_cone_update_rate
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:29:47.263759+00:00
-- url     : https://prove2.me/submissions/5ae58fdc-cdf3-410c-960d-0deb369fe64d

import Mathlib
import Definitions.Def_CtxInvOpt_Greedy_Online
import Definitions.Def_CtxInvOpt_Pointed_ConeUpdate
import Theorems.Thm_CtxInvOpt_Pointed_lemmaB1_cone_update

open Matrix CtxInvOpt.Pointed

namespace L3Red

lemma log_ineq (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (1 / x) * (-Real.log (1 - x ^ 2)) - (Real.log (1 + x) - Real.log (1 - x)) ≤ -x := by
  have hax : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hax2 : |x ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg x)]; nlinarith
  have S1 := (Real.hasSum_pow_div_log_of_abs_lt_one hax2).mul_left (1 / x)
  have S2 := Real.hasSum_log_sub_log_of_abs_lt_one hax
  have S := S1.sub S2
  have B : HasSum (fun n : ℕ => if n = 0 then -x else 0) (-x) := hasSum_ite_eq 0 (-x)
  refine hasSum_le (fun n => ?_) S B
  have hxn : (1 / x) * ((x ^ 2) ^ (n + 1) / ((n:ℝ) + 1)) = x ^ (2 * n + 1) / ((n:ℝ) + 1) := by
    rw [← pow_mul]
    field_simp
    ring
  show (1 / x) * ((x ^ 2) ^ (n + 1) / ((n:ℝ) + 1)) - 2 * (1 / (2 * (n:ℝ) + 1)) * x ^ (2 * n + 1) ≤ _
  rw [hxn]
  have hp : 0 ≤ x ^ (2 * n + 1) := by positivity
  split_ifs with h
  · subst h; simp; ring_nf; linarith
  · have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have : x ^ (2 * n + 1) / ((n:ℝ) + 1) ≤ 2 * (1 / (2 * (n:ℝ) + 1)) * x ^ (2 * n + 1) := by
      rw [div_le_iff₀ (by positivity)]
      have : (1:ℝ) ≤ 2 * (1 / (2 * (n:ℝ) + 1)) * ((n:ℝ) + 1) := by
        rw [show 2 * (1 / (2 * (n:ℝ) + 1)) * ((n:ℝ) + 1) = (2 * n + 2) / (2 * n + 1) by
          field_simp, le_div_iff₀ (by positivity)]
        linarith
      nlinarith
    linarith

lemma rate_ineq (m : ℕ) (hm : 2 ≤ m) :
    ((m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1)) ^ m * (1 - 2 / ((m:ℝ) + 1)) ≤ Real.exp (-(1 / (m:ℝ))) := by
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  set x : ℝ := 1 / m with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hxdef, div_lt_one (by linarith)]; linarith
  have hmx : (m:ℝ) = 1 / x := by rw [hxdef]; field_simp
  have hpos : 0 < ((m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1)) ^ m * (1 - 2 / ((m:ℝ) + 1)) := by
    apply mul_pos
    · apply pow_pos; apply div_pos (by positivity); nlinarith
    · rw [sub_pos, div_lt_one (by linarith)]; linarith
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.2
  have e1 : (m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1) = (1 - x ^ 2)⁻¹ := by
    rw [hmx]; field_simp
  have e2 : 1 - 2 / ((m:ℝ) + 1) = (1 - x) / (1 + x) := by
    rw [hmx]; field_simp; ring
  have h1x : 0 < 1 - x := by linarith
  have h1x2 : 0 < 1 - x ^ 2 := by nlinarith
  rw [Real.log_mul (by rw [e1]; positivity) (by rw [e2]; positivity), Real.log_pow, e1, e2, Real.log_inv,
    Real.log_div h1x.ne' (by linarith)]
  have := log_ineq x hx0 hx1
  rw [← hmx] at this
  linarith


lemma det_ellUpd {m : ℕ} (w : Fin m → ℝ) (a : Fin m → ℝ)
    (hq : a ⬝ᵥ (Matrix.diagonal w *ᵥ a) ≠ 0) :
    (LinearOptimization.ellipsoidUpdateMatrix (Matrix.diagonal w) a).det =
      ((m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1)) ^ m * (∏ i, w i) * (1 - 2 / ((m:ℝ) + 1)) := by
  unfold LinearOptimization.ellipsoidUpdateMatrix
  rw [det_smul, Fintype.card_fin]
  set q := a ⬝ᵥ (Matrix.diagonal w *ᵥ a)
  have hM : Matrix.diagonal w - ((2:ℝ) / (m + 1)) • q⁻¹ • (Matrix.diagonal w * vecMulVec a a * Matrix.diagonal w)
      = Matrix.diagonal w * (1 + replicateCol Unit (-(((2:ℝ) / (m + 1)) * q⁻¹) • a) *
          replicateRow Unit (Matrix.diagonal w *ᵥ a)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal, vecMulVec, replicateCol, replicateRow, Matrix.one_apply,
      Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.add_apply, mul_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    split_ifs <;> ring
  rw [hM, det_mul, det_diagonal, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, dotProduct_comm, ← mul_assoc]
  change _ * (1 + -(2 / ((m:ℝ) + 1) * q⁻¹) * q) = _
  field_simp
  ring

lemma dot_rot {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin k) ℝ)
    (x y : Fin k → ℝ) : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ y) = x ⬝ᵥ y := by
  have h1 : U * Uᵀ = 1 := by simpa using (Matrix.mem_orthogonalGroup_iff (Fin k) ℝ).1 hU
  rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h1, one_mulVec]

lemma inner_eq_dot {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ x y = (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp y) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma core_ineq (y0 y1 a0 p : ℝ) (hy0 : 0 ≤ y0) (hp : 0 ≤ p) (hp2 : p ^ 2 = a0 ^ 2 * y1 ^ 2)
    (hkey : y1 ^ 2 ≤ 2 * y0 * p) :
    (y0 ^ 2 + y1 ^ 2) * (1 + a0 ^ 2) ≤ (1 + 2 * a0 ^ 2) * (y0 + p) ^ 2 := by
  have h1 := mul_nonneg (sq_nonneg a0) (mul_nonneg hy0 hp)
  have h2 := mul_nonneg (sq_nonneg a0) (sq_nonneg p)
  have h3 := mul_nonneg (sq_nonneg a0) (sq_nonneg y0)
  have e : (1 + 2 * a0 ^ 2) * (y0 + p) ^ 2 - (y0 ^ 2 + y1 ^ 2) * (1 + a0 ^ 2) =
      (2 * y0 * p - y1 ^ 2) + a0 ^ 2 * y0 ^ 2 + 4 * (a0 ^ 2 * (y0 * p)) + 2 * (a0 ^ 2 * p ^ 2) +
        (p ^ 2 - a0 ^ 2 * y1 ^ 2) := by ring
  rw [hp2] at e
  nlinarith

lemma incl_one (w : Fin 1 → ℝ) (hw : ∀ i, 0 < w i) (U : Matrix (Fin (1+1)) (Fin (1+1)) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin (1+1)) ℝ)
    (δ : EuclideanSpace ℝ (Fin (1+1))) (hδ : inner ℝ δ (axisVec U) ≤ 0)
    (htail : tailVec (rotCoord U δ) ≠ 0)
    (w' : Fin 1 → ℝ) (U' : Matrix (Fin (1+1)) (Fin (1+1)) ℝ) (hupd : IsConeUpdate w U δ w' U') :
    ellCone w U ∩ {c | 0 ≤ inner ℝ δ c} ⊆ ellCone w' U' := by
  unfold IsConeUpdate at hupd
  dsimp only at hupd
  rw [if_pos rfl] at hupd
  obtain ⟨hw', V, hV, hcol, rfl⟩ := hupd
  rintro c ⟨⟨hy0, hy1⟩, hc⟩
  simp only [Set.mem_ofPred_eq] at hc
  set y := rotCoord U c with hydef
  set r := rotCoord U δ with hrdef
  have hinner : inner ℝ δ c = r 0 * y 0 + r 1 * y 1 := by
    rw [inner_eq_dot, ← dot_rot U hU]
    simp [hrdef, hydef, rotCoord, dotProduct, Fin.sum_univ_two]
  have hr0 : r 0 ≤ 0 := by
    have : r 0 = inner ℝ δ (axisVec U) := by
      simp [hrdef, rotCoord, axisVec, mulVec, dotProduct, PiLp.inner_apply, mul_comm]
    linarith
  have hr1 : r 1 ≠ 0 := by
    intro h; apply htail; ext i; fin_cases i; simpa [tailVec] using h
  have hry : 0 ≤ r 1 * y 1 := by nlinarith
  have hz : rotCoord (U * V) c = Vᵀ *ᵥ y := by
    rw [hydef]; unfold rotCoord; rw [transpose_mul, ← mulVec_mulVec]
  set v := tailVec r with hvdef
  have hvv : v ⬝ᵥ v = r 1 ^ 2 := by simp [hvdef, tailVec, dotProduct, sq]
  set a0 : ℝ := 1 / 2 * (√(w 0) * ((√(v ⬝ᵥ v))⁻¹ • v) 0) with ha0def
  have ha0 : a0 = √(w 0) * r 1 / (2 * |r 1|) := by
    rw [ha0def, hvv, Real.sqrt_sq_eq_abs]; simp [hvdef, tailVec]; ring
  have hdot : (fun i : Fin 1 => 1 / 2 * (√(w i) * ((√(v ⬝ᵥ v))⁻¹ • v) i)) ⬝ᵥ
      (fun i : Fin 1 => 1 / 2 * (√(w i) * ((√(v ⬝ᵥ v))⁻¹ • v) i)) = a0 ^ 2 := by
    simp [dotProduct, ha0def, sq]
  have hcol0 : V 0 0 = 1 / √(1 + a0 ^ 2) := by rw [hcol 0, hdot]; simp
  have hcol1 : V 1 0 = a0 / √(1 + a0 ^ 2) := by rw [hcol 1, hdot]; simp [ha0def]
  have hw0 := hw 0
  have hr1a : 0 < |r 1| := abs_pos.2 hr1
  have ha2 : a0 ^ 2 = w 0 / 4 := by
    rw [ha0, div_pow, mul_pow, Real.sq_sqrt hw0.le, mul_pow, sq_abs]
    field_simp
    norm_num
  have hp : 0 ≤ a0 * y 1 := by
    rw [ha0, div_mul_eq_mul_div, mul_assoc]
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hry) (by positivity)
  have hS : 0 < √(1 + a0 ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hS2 : √(1 + a0 ^ 2) ^ 2 = 1 + a0 ^ 2 := Real.sq_sqrt (by positivity)
  have hz0 : (Vᵀ *ᵥ y) 0 = (y 0 + a0 * y 1) / √(1 + a0 ^ 2) := by
    have : (Vᵀ *ᵥ y) 0 = V 0 0 * y 0 + V 1 0 * y 1 := by
      simp [mulVec, dotProduct, Fin.sum_univ_succ]
    rw [this, hcol0, hcol1]; field_simp
  have hz0e : (Vᵀ *ᵥ y) 0 = V 0 0 * y 0 + V 1 0 * y 1 := by
    simp [mulVec, dotProduct, Fin.sum_univ_succ]
  have hz1e : (Vᵀ *ᵥ y) 1 = V 0 1 * y 0 + V 1 1 * y 1 := by
    simp [mulVec, dotProduct, Fin.sum_univ_succ]
  have hnorm : (Vᵀ *ᵥ y) 0 ^ 2 + (Vᵀ *ᵥ y) 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    have h := dot_rot V hV y y
    simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    have e1 : (Fin.succ 0 : Fin (1+1)) = 1 := rfl
    rw [e1] at h
    simp only [sq]
    linarith [h]
  have hy1' : y 1 ^ 2 / w 0 ≤ y 0 ^ 2 := by simpa using hy1
  have hy1'' : y 1 ^ 2 ≤ w 0 * y 0 ^ 2 := by
    rw [div_le_iff₀ hw0] at hy1'; linarith
  set p := a0 * y 1 with hpdef
  have hp2 : p ^ 2 = a0 ^ 2 * y 1 ^ 2 := by rw [hpdef]; ring
  have hkey : y 1 ^ 2 ≤ 2 * y 0 * p := by
    have h4 : (y 1 ^ 2) ^ 2 ≤ (2 * y 0 * p) ^ 2 := by
      have : (2 * y 0 * p) ^ 2 = 4 * a0 ^ 2 * y 0 ^ 2 * y 1 ^ 2 := by rw [mul_pow, hp2]; ring
      rw [this, ha2]
      have := mul_le_mul_of_nonneg_left hy1'' (sq_nonneg (y 1))
      nlinarith
    exact (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) two_ne_zero).1 h4
  refine ⟨?_, ?_⟩
  · rw [hz, hz0]; positivity
  · rw [hz]
    simp only [Fin.sum_univ_one, hw']
    have hz1 : (Vᵀ *ᵥ y) (Fin.succ 0) ^ 2 = y 0 ^ 2 + y 1 ^ 2 - (Vᵀ *ᵥ y) 0 ^ 2 := by
      have : (Fin.succ 0 : Fin (1+1)) = 1 := rfl
      rw [this]; linarith
    rw [hz1, hz0, div_pow, hS2, div_le_iff₀ (by linarith)]
    rw [show w 0 = 4 * a0 ^ 2 by linarith]
    have ha0pos : 0 < 1 + a0 ^ 2 := by positivity
    have hc := core_ineq (y 0) (y 1) a0 p hy0 hp hp2 hkey
    set Z := (y 0 + p) ^ 2 / (1 + a0 ^ 2) with hZdef
    have hZ : Z * (1 + a0 ^ 2) = (y 0 + p) ^ 2 := div_mul_cancel₀ _ ha0pos.ne'
    have h' : (y 0 ^ 2 + y 1 ^ 2) * (1 + a0 ^ 2) ≤ ((1 + 2 * a0 ^ 2) * Z) * (1 + a0 ^ 2) := by
      rw [mul_assoc, hZ]; exact hc
    have h'' := le_of_mul_le_mul_right h' ha0pos
    linarith

lemma dot_self_pos {m : ℕ} (v : Fin m → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  rcases Function.ne_iff.1 hv with ⟨i, hi⟩
  have : v i ^ 2 ≤ v ⬝ᵥ v := by
    unfold dotProduct
    have := Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
      (Finset.mem_univ i)
    simpa [sq] using this
  have : 0 < v i ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))
  linarith


lemma dbar_facts {m : ℕ} (v : Fin m → ℝ) (hv : v ≠ 0) (w : Fin m → ℝ) :
    ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ≠ 0 ∧
    ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) = 1 ∧
    ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ (Matrix.diagonal w *ᵥ ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v)) =
      (∑ i, w i * v i ^ 2) / (v ⬝ᵥ v) := by
  have hpos := dot_self_pos v hv
  have hs : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  have hs0 : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hpos
  refine ⟨smul_ne_zero (inv_ne_zero hs0.ne') hv, ?_, ?_⟩
  · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, inv_pow, hs,
      inv_mul_cancel₀ hpos.ne']
  · rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← sq, inv_pow, hs]
    simp only [Matrix.mulVec_diagonal, dotProduct]
    rw [div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => by ring)


lemma inner_effDiff_nonpos {d : ℕ} (u a : EuclideanSpace ℝ (Fin d)) (h : inner ℝ u a ≤ 0) :
    inner ℝ (effDiff u) a ≤ 0 := by
  unfold effDiff
  split_ifs
  · simp
  · rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h


lemma inner_effDiff_nonneg {d : ℕ} (u a : EuclideanSpace ℝ (Fin d)) (h : 0 ≤ inner ℝ u a) :
    0 ≤ inner ℝ (effDiff u) a := by
  unfold effDiff
  split_ifs
  · simp
  · rw [real_inner_smul_left]
    exact mul_nonneg (by positivity) h

/-- Data extracted from a ConeUpdate step with `m ≥ 2`. -/
lemma coneUpdate_ge2 {m : ℕ} (hm : 2 ≤ m) {w w' : Fin m → ℝ}
    {U U' : Matrix (Fin (m+1)) (Fin (m+1)) ℝ} {δ : EuclideanSpace ℝ (Fin (m+1))}
    (h : IsConeUpdate w U δ w' U') :
    ∃ P ∈ Matrix.orthogonalGroup (Fin m) ℝ,
      LinearOptimization.ellipsoidUpdateMatrix (Matrix.diagonal w)
        ((Real.sqrt (tailVec (rotCoord U δ) ⬝ᵥ tailVec (rotCoord U δ)))⁻¹ •
          tailVec (rotCoord U δ)) = P * Matrix.diagonal w' * Pᵀ := by
  unfold IsConeUpdate at h
  dsimp only at h
  rw [if_neg (by omega)] at h
  obtain ⟨V, -, μ, -, -, -, -, hP, -⟩ := h
  exact hP



lemma knowledgeSet_succ_sub {d : ℕ} (C0 : Set (EuclideanSpace ℝ (Fin d)))
    {n : ℕ} (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (xstar : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    CtxInvOpt.Greedy.knowledgeSet C0 X f xstar (t+1) ⊆ CtxInvOpt.Greedy.knowledgeSet C0 X f xstar t :=
  fun _ hc => ⟨hc.1, fun s hs => hc.2 s (by omega)⟩


end L3Red

set_option maxHeartbeats 1000000 in
open L3Red in
theorem solution {n m : ℕ} (hm : 1 ≤ m)
    (C0 : Set (EuclideanSpace ℝ (Fin (m + 1)))) (cstar : EuclideanSpace ℝ (Fin (m + 1)))
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xstar : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ)
    (hxstar : xstar t ∈ CtxInvOpt.Offline.argminSet cstar (X t) (f t))
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ)
    (hK : CtxInvOpt.Greedy.knowledgeSet C0 X f xstar t ⊆ ellCone w U)
    (xpi : EuclideanSpace ℝ (Fin n)) (hxpi : xpi ∈ CtxInvOpt.Offline.argminSet (axisVec U) (X t) (f t))
    (htail : tailVec (rotCoord U (effDiff (f t xpi - f t (xstar t)))) ≠ 0)
    (w' : Fin m → ℝ) (U' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hupd : IsConeUpdate w U (effDiff (f t xpi - f t (xstar t))) w' U') :
    CtxInvOpt.Greedy.knowledgeSet C0 X f xstar (t + 1) ⊆
        ellCone w U ∩ {c | 0 ≤ inner ℝ (effDiff (f t xpi - f t (xstar t))) c} ∧
      ellCone w U ∩ {c | 0 ≤ inner ℝ (effDiff (f t xpi - f t (xstar t))) c} ⊆ ellCone w' U' ∧
      (2 ≤ m → ∏ i, w' i ≤ Real.exp (-(1 / (m : ℝ))) * ∏ i, w i) := by
  have hδ : inner ℝ (effDiff (f t xpi - f t (xstar t))) (axisVec U) ≤ 0 := by
    apply inner_effDiff_nonpos
    rw [inner_sub_left]
    linarith [hxpi.2 (xstar t) hxstar.1]
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    refine ⟨hK (knowledgeSet_succ_sub C0 X f xstar t hc), ?_⟩
    show 0 ≤ inner ℝ (effDiff (f t xpi - f t (xstar t))) c
    apply inner_effDiff_nonneg
    have := hc.2 t (lt_add_one t) xpi hxpi.1
    rw [inner_sub_left]
    linarith
  · rcases (by omega : m = 1 ∨ 2 ≤ m) with h1 | h2
    · subst h1
      exact incl_one w hw U hU _ hδ htail w' U' hupd
    · exact (CtxInvOpt.Pointed.lemmaB1_cone_update h2 w hw U hU _ hδ htail w' U' hupd).1
  · intro h2
    obtain ⟨P, hP, hN⟩ := coneUpdate_ge2 h2 hupd
    set v := tailVec (rotCoord U (effDiff (f t xpi - f t (xstar t))))
    obtain ⟨-, -, hdq⟩ := dbar_facts v htail w
    have hvpos := dot_self_pos v htail
    have hq : 0 < ∑ i, w i * v i ^ 2 := by
      have hv' : ∃ i, v i ≠ 0 := Function.ne_iff.1 htail
      obtain ⟨i, hi⟩ := hv'
      have : 0 < w i * v i ^ 2 := mul_pos (hw i) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => w j * v j ^ 2)
        (fun j _ => mul_nonneg (hw j).le (sq_nonneg _)) (Finset.mem_univ i))
    have hdet := det_ellUpd w ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) (by rw [hdq]; positivity)
    rw [hN] at hdet
    have hPP : P.det * Pᵀ.det = 1 := by
      rw [← det_mul]
      have : P * Pᵀ = 1 := by simpa using (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).1 hP
      rw [this, det_one]
    have hprod : ∏ i, w' i = ((m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1)) ^ m * (∏ i, w i) * (1 - 2 / ((m:ℝ) + 1)) := by
      rw [← hdet, det_mul, det_mul, det_diagonal]
      linear_combination (∏ i, w' i) * hPP.symm
    rw [hprod]
    have hr := rate_ineq m h2
    have hpw : 0 ≤ ∏ i, w i := Finset.prod_nonneg (fun i _ => (hw i).le)
    nlinarith
