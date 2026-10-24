-- Prove2me | solution 1 for CtxInvOpt.Pointed.lemma5_largest_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:20:36.316402+00:00
-- url     : https://prove2.me/submissions/16c0db68-37ca-4776-a07f-a4d1cc466632

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_Run
import Theorems.Thm_CtxInvOpt_Pointed_lemma4_low_regret_period
import Theorems.Thm_CtxInvOpt_Pointed_lemma3_cone_update_rate
import Theorems.Thm_CtxInvOpt_Pointed_lemmaB1_cone_update
import Theorems.Thm_FeaturePricing_Ellipsoid_lemma3_min_eigenvalue_shrink
import Theorems.Thm_FeaturePricing_Ellipsoid_lemma4_min_eigenvalue_no_decrease

open Matrix CtxInvOpt.Pointed

namespace Thm3Red

lemma sum_sq_rotCoord {m : ℕ} (U : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin (m+1)) ℝ) (c : EuclideanSpace ℝ (Fin (m+1))) :
    ∑ i, rotCoord U c i ^ 2 = ‖c‖ ^ 2 := by
  have h1 : U * Uᵀ = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff (Fin (m+1)) ℝ).1 hU
    simpa using this
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  have key : (rotCoord U c) ⬝ᵥ (rotCoord U c) = (WithLp.ofLp c) ⬝ᵥ (WithLp.ofLp c) := by
    unfold rotCoord
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, h1,
      Matrix.one_mulVec]
  simp only [dotProduct, ← sq] at key
  simpa using key

lemma norm_effDiff_le {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) : ‖effDiff u‖ ≤ 1 := by
  unfold effDiff
  split_ifs with h
  · simp
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

lemma tail_sum_le {m : ℕ} (v : Fin (m+1) → ℝ) : ∑ i : Fin m, v i.succ ^ 2 ≤ ∑ i, v i ^ 2 := by
  rw [Fin.sum_univ_succ]
  have := sq_nonneg (v 0)
  linarith

lemma tailQuad_le {m : ℕ} (w : Fin m → ℝ) (c : ℝ) (hc : 0 ≤ c) (hw : ∀ i, w i ≤ c)
    (U : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin (m+1)) ℝ) (δ : EuclideanSpace ℝ (Fin (m+1)))
    (hδ : ‖δ‖ ≤ 1) : tailQuad w (rotCoord U δ) ≤ c := by
  unfold tailQuad
  have h1 : ∑ i : Fin m, w i * rotCoord U δ i.succ ^ 2 ≤ ∑ i : Fin m, c * rotCoord U δ i.succ ^ 2 :=
    Finset.sum_le_sum (fun (i : Fin m) _ => mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _))
  have h2 := tail_sum_le (rotCoord U δ)
  rw [sum_sq_rotCoord U hU] at h2
  have h3 : ‖δ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg δ]
  rw [← Finset.mul_sum] at h1
  nlinarith

lemma le_lamMax {m : ℕ} (w : Fin m → ℝ) (i : Fin m) : w i ≤ lamMax w :=
  le_ciSup (Set.finite_range w).bddAbove i


open CtxInvOpt.Offline in
lemma vecAngle_le_pi {d : ℕ} (c chat : EuclideanSpace ℝ (Fin d)) : vecAngle c chat ≤ Real.pi := by
  unfold vecAngle
  split_ifs
  · exact Real.pi_pos.le
  · exact Real.arccos_le_pi _

open CtxInvOpt.Offline in
lemma init_contain {m : ℕ} (C0 : Set (EuclideanSpace ℝ (Fin (m + 1))))
    (hC0 : C0 ⊆ unitSphere (m + 1))
    (hα0 : 0 < uncAngle C0) (hα : uncAngle C0 < Real.pi / 2)
    (U : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (m+1)) ℝ)
    (hcc : IsCircumcenter C0 (axisVec U)) :
    C0 ⊆ ellCone (fun _ => Real.tan (uncAngle C0) ^ 2) U := by
  intro c hc
  set α := uncAngle C0 with hαdef
  have hcn : ‖c‖ = 1 := by simpa [unitSphere] using hC0 hc
  have hhn : ‖axisVec U‖ = 1 := by simpa [unitSphere] using hcc.1
  have hθ : vecAngle c (axisVec U) ≤ α := by
    rw [hαdef, ← hcc.2]
    exact le_ciSup (f := fun c : C0 => vecAngle (c : EuclideanSpace ℝ (Fin (m+1))) (axisVec U))
      ⟨Real.pi, by rintro _ ⟨x, rfl⟩; exact vecAngle_le_pi _ _⟩ ⟨c, hc⟩
  have hc0 : c ≠ 0 := by intro h; simp [h] at hcn
  have hh0 : axisVec U ≠ 0 := by intro h; simp [h] at hhn
  rw [vecAngle, if_neg (by tauto), hcn, hhn, mul_one, div_one] at hθ
  set x := inner ℝ c (axisVec U) with hxdef
  have hx1 : |x| ≤ 1 := by
    have := abs_real_inner_le_norm c (axisVec U); rw [hcn, hhn] at this; linarith
  have hcos : Real.cos α ≤ x := by
    have := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg x)
      (by linarith [Real.pi_pos]) hθ
    rwa [Real.cos_arccos (by linarith [(abs_le.1 hx1).1]) (abs_le.1 hx1).2] at this
  have hcospos : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα⟩
  have hrc0 : rotCoord U c 0 = x := by
    simp [rotCoord, hxdef, axisVec, mulVec, dotProduct, PiLp.inner_apply]
  have hsum := sum_sq_rotCoord U hU c
  rw [Fin.sum_univ_succ, hcn, hrc0] at hsum
  refine ⟨by rw [hrc0]; linarith, ?_⟩
  rw [hrc0, ← Finset.sum_div]
  have htan : Real.tan α ^ 2 * Real.cos α ^ 2 = 1 - Real.cos α ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, div_pow, div_mul_cancel₀ _ (by positivity)]
    linarith [Real.sin_sq_add_cos_sq α]
  have htpos : 0 < Real.tan α := Real.tan_pos_of_pos_of_lt_pi_div_two hα0 hα
  rw [div_le_iff₀ (by positivity)]
  have h1 : Real.cos α ^ 2 ≤ x ^ 2 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (Real.tan α))
  nlinarith

lemma coneUpdate_orth {m : ℕ} {w w' : Fin m → ℝ} {U U' : Matrix (Fin (m+1)) (Fin (m+1)) ℝ}
    {δ : EuclideanSpace ℝ (Fin (m+1))} (hU : U ∈ Matrix.orthogonalGroup (Fin (m+1)) ℝ)
    (h : IsConeUpdate w U δ w' U') : U' ∈ Matrix.orthogonalGroup (Fin (m+1)) ℝ := by
  unfold IsConeUpdate at h
  dsimp only at h
  split_ifs at h with hm
  · obtain ⟨-, V, hV, -, rfl⟩ := h
    exact mul_mem hU hV
  · obtain ⟨V, hV, μ, -, -, -, -, -, -, rfl⟩ := h
    exact mul_mem hU hV

lemma coneUpdate_one {w w' : Fin 1 → ℝ} {U U' : Matrix (Fin (1+1)) (Fin (1+1)) ℝ}
    {δ : EuclideanSpace ℝ (Fin (1+1))}
    (h : IsConeUpdate w U δ w' U') : ∀ i, w' i = w i / 2 := by
  unfold IsConeUpdate at h
  dsimp only at h
  rw [if_pos rfl] at h
  exact h.1

lemma inner_effDiff_nonpos {d : ℕ} (u a : EuclideanSpace ℝ (Fin d)) (h : inner ℝ u a ≤ 0) :
    inner ℝ (effDiff u) a ≤ 0 := by
  unfold effDiff
  split_ifs
  · simp
  · rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h

open CtxInvOpt.Offline in
lemma period_le_one {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsActionSet X)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)) (hf : IsContext f)
    (a b : EuclideanSpace ℝ (Fin n)) (ha : a ∈ X) (hb : b ∈ X)
    (c : EuclideanSpace ℝ (Fin d)) (hc : ‖c‖ = 1) : inner ℝ (f a - f b) c ≤ 1 := by
  have h1 := real_inner_le_norm (f a - f b) c
  have h2 : ‖f a - f b‖ ≤ ‖a - b‖ := by
    have := hf.dist_le_mul a b
    simpa [dist_eq_norm] using this
  have h3 : ‖a - b‖ ≤ 1 := by
    rw [← dist_eq_norm]
    exact (Metric.dist_le_diam_of_mem hX.2.1.isBounded ha hb).trans hX.2.2
  rw [hc, mul_one] at h1
  linarith

section run
open Classical
variable {n m : ℕ} (ε : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (w : ℕ → Fin m → ℝ)
    (U : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)

lemma updateCount_succ (t : ℕ) :
    updateCount ε f xpi xstar w U (t+1) =
      updateCount ε f xpi xstar w U t + (if IsUpdatePeriod ε f xpi xstar w U t then 1 else 0) := by
  classical
  unfold updateCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma updateCount_zero : updateCount ε f xpi xstar w U 0 = 0 := by
  simp [updateCount]

lemma count_le (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t, IsUpdatePeriod ε f xpi xstar w U t → (updateCount ε f xpi xstar w U t : ℝ) < B)
    (T : ℕ) : (updateCount ε f xpi xstar w U T : ℝ) ≤ B + 1 := by
  induction T with
  | zero => rw [updateCount_zero]; simp; linarith
  | succ T ih =>
    rw [updateCount_succ]
    split_ifs with hu
    · push_cast; linarith [h T hu]
    · simpa using ih

lemma regret_le (cstar : EuclideanSpace ℝ (Fin (m + 1)))
    (h : ∀ t, inner ℝ (f t (xpi t) - f t (xstar t)) cstar ≤
      ε + (if IsUpdatePeriod ε f xpi xstar w U t then 1 else 0)) (T : ℕ) :
    CtxInvOpt.Greedy.cumRegret cstar f xpi xstar T ≤
      ε * T + updateCount ε f xpi xstar w U T := by
  induction T with
  | zero => simp [CtxInvOpt.Greedy.cumRegret, updateCount_zero]
  | succ T ih =>
    simp only [CtxInvOpt.Greedy.cumRegret] at ih ⊢
    rw [Finset.sum_range_succ, updateCount_succ]
    have := h T
    split_ifs at this ⊢ with hu
    · push_cast; linarith
    · push_cast; linarith


lemma knowledgeSet_succ_sub {d : ℕ} (C0 : Set (EuclideanSpace ℝ (Fin d)))
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (xstar : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    CtxInvOpt.Greedy.knowledgeSet C0 X f xstar (t+1) ⊆ CtxInvOpt.Greedy.knowledgeSet C0 X f xstar t :=
  fun _ hc => ⟨hc.1, fun s hs => hc.2 s (by omega)⟩

lemma tail_ne_of_update (t : ℕ) (_hε : 0 ≤ ε) (hu : IsUpdatePeriod ε f xpi xstar w U t) :
    tailVec (rotCoord (U t) (effDiff (f t (xpi t) - f t (xstar t)))) ≠ 0 := by
  intro h0
  unfold IsUpdatePeriod tailQuad at hu
  have : ∀ i : Fin m, rotCoord (U t) (effDiff (f t (xpi t) - f t (xstar t))) i.succ = 0 :=
    fun i => congrFun h0 i
  simp [this] at hu
  nlinarith [sq_nonneg ε]

lemma invariant (hm : 1 ≤ m) (C0 : Set (EuclideanSpace ℝ (Fin (m + 1))))
    (cstar : EuclideanSpace ℝ (Fin (m + 1)))
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hε : 0 ≤ ε)
    (hrun : IsEllConesRun ε C0 cstar X f xpi xstar w U)
    (hinit : C0 ⊆ ellCone (w 0) (U 0)) (hτ : 0 < Real.tan (CtxInvOpt.Offline.uncAngle C0)) :
    ∀ t, (∀ i, 0 < w t i) ∧ U t ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ ∧
      CtxInvOpt.Greedy.knowledgeSet C0 X f xstar t ⊆ ellCone (w t) (U t) := by
  intro t
  induction t with
  | zero =>
    refine ⟨?_, hrun.2.1, fun c hc => hinit hc.1⟩
    intro i; rw [hrun.1]; positivity
  | succ t ih =>
    obtain ⟨hxpi, hxs, hno, hyes⟩ := hrun.2.2.2 t
    by_cases hu : IsUpdatePeriod ε f xpi xstar w U t
    · have hupd := hyes hu
      have htail := tail_ne_of_update ε f xpi xstar w U t hε hu
      have L3 := lemma3_cone_update_rate hm C0 cstar X f xstar t hxs (w t) ih.1 (U t) ih.2.1
        ih.2.2 (xpi t) hxpi htail (w (t+1)) (U (t+1)) hupd
      refine ⟨?_, coneUpdate_orth ih.2.1 hupd, L3.1.trans L3.2.1⟩
      rcases (by omega : m = 1 ∨ 2 ≤ m) with h1 | h2
      · subst h1
        intro i
        rw [coneUpdate_one hupd i]
        linarith [ih.1 i]
      · have hδ : inner ℝ (effDiff (f t (xpi t) - f t (xstar t))) (axisVec (U t)) ≤ 0 := by
          apply inner_effDiff_nonpos
          rw [inner_sub_left]
          linarith [hxpi.2 (xstar t) hxs.1]
        exact (lemmaB1_cone_update h2 (w t) ih.1 (U t) ih.2.1 _ hδ htail _ _ hupd).2.1
    · obtain ⟨h1, h2⟩ := hno hu
      rw [h1, h2]
      exact ⟨ih.1, ih.2.1, (knowledgeSet_succ_sub C0 X f xstar t).trans ih.2.2⟩

end run

end Thm3Red


namespace L5Red

open Thm3Red

lemma spectrum_conj {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (hP : P ∈ Matrix.orthogonalGroup (Fin m) ℝ) (d : Fin m → ℝ) :
    spectrum ℝ (P * Matrix.diagonal d * Pᵀ) = Set.range d := by
  have h1 : P * Pᵀ = 1 := by
    simpa using (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).1 hP
  have h2 : Pᵀ * P = 1 := by
    simpa using (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).1 hP
  let u : (Matrix (Fin m) (Fin m) ℝ)ˣ := ⟨P, Pᵀ, h1, h2⟩
  have : spectrum ℝ (P * Matrix.diagonal d * Pᵀ) = spectrum ℝ ((u : Matrix (Fin m) (Fin m) ℝ) *
      Matrix.diagonal d * ((u⁻¹ : (Matrix (Fin m) (Fin m) ℝ)ˣ) : Matrix (Fin m) (Fin m) ℝ)) := rfl
  rw [this, spectrum.units_conjugate, spectrum_diagonal]

lemma lamMin_le {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (x : ℝ) (hx : x ∈ spectrum ℝ A) :
    FeaturePricing.Ellipsoid.lamMin A ≤ x :=
  csInf_le (Matrix.finite_spectrum A).bddBelow hx

lemma le_lamMin_diag {m : ℕ} (hm : 1 ≤ m) (w : Fin m → ℝ) (c : ℝ) (h : ∀ i, c ≤ w i) :
    c ≤ FeaturePricing.Ellipsoid.lamMin (Matrix.diagonal w) := by
  unfold FeaturePricing.Ellipsoid.lamMin
  rw [spectrum_diagonal]
  exact le_csInf (Set.range_nonempty_iff_nonempty.2 ⟨⟨0, by omega⟩⟩) (by rintro _ ⟨i, rfl⟩; exact h i)

lemma lamMin_diag_le {m : ℕ} (w : Fin m → ℝ) (i : Fin m) :
    FeaturePricing.Ellipsoid.lamMin (Matrix.diagonal w) ≤ w i :=
  lamMin_le _ _ (by rw [spectrum_diagonal]; exact ⟨i, rfl⟩)

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

end L5Red

set_option maxHeartbeats 2000000 in
open Classical L5Red Thm3Red in
theorem solution {n m : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (C0 : Set (EuclideanSpace ℝ (Fin (m + 1)))) (hC0closed : IsClosed C0)
    (hC0 : C0 ⊆ CtxInvOpt.Offline.unitSphere (m + 1)) (hC0ne : C0.Nonempty)
    (hα0 : 0 < CtxInvOpt.Offline.uncAngle C0) (hα : CtxInvOpt.Offline.uncAngle C0 < Real.pi / 2)
    (cstar : EuclideanSpace ℝ (Fin (m + 1))) (hcstar : cstar ∈ C0)
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (w : ℕ → Fin m → ℝ)
    (U : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hX : ∀ t, CtxInvOpt.Offline.IsActionSet (X t)) (hf : ∀ t, CtxInvOpt.Offline.IsContext (f t))
    (hrun : CtxInvOpt.Pointed.IsEllConesRun ε C0 cstar X f xpi xstar w U) :
    (2 ≤ m → (ε / (10 * (m : ℝ))) ^ 2 < Real.tan (CtxInvOpt.Offline.uncAngle C0) ^ 2 →
        ∀ t, CtxInvOpt.Pointed.lamMax (w t) ≤
          (10 * ((m : ℝ) + 1) / ε) ^ (2 * (m - 1)) * (Real.tan (CtxInvOpt.Offline.uncAngle C0) ^ 2) ^ m *
            Real.exp (-((CtxInvOpt.Pointed.updateCount ε f xpi xstar w U t : ℝ) / m))) ∧
      (Real.tan (CtxInvOpt.Offline.uncAngle C0) ^ 2 ≤ (ε / (10 * (m : ℝ))) ^ 2 →
        (∀ t, CtxInvOpt.Pointed.updateCount ε f xpi xstar w U t = 0) ∧
          ∀ t, inner ℝ (f t (xpi t) - f t (xstar t)) cstar ≤ ε) := by
  set α := CtxInvOpt.Offline.uncAngle C0 with hαdef
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hτ : 0 < Real.tan α := Real.tan_pos_of_pos_of_lt_pi_div_two hα0 hα
  have hinit : C0 ⊆ ellCone (w 0) (U 0) := by
    rw [hrun.1]; exact Thm3Red.init_contain C0 hC0 hα0 hα (U 0) hrun.2.1 hrun.2.2.1
  have hinv := Thm3Red.invariant ε f xpi xstar w U hm C0 cstar X hε.le hrun hinit hτ
  have hupd_le : ∀ t, IsUpdatePeriod ε f xpi xstar w U t → ∀ c, 0 ≤ c → (∀ i, w t i ≤ c) →
      ε ^ 2 < c := by
    intro t hu c hc hwc
    exact lt_of_lt_of_le hu
      (Thm3Red.tailQuad_le _ c hc hwc _ (hinv t).2.1 _ (Thm3Red.norm_effDiff_le _))
  constructor
  · intro h2 hcond
    have hm2 : (2:ℝ) ≤ m := by exact_mod_cast h2
    -- product of eigenvalues
    have hprod : ∀ t, ∏ i, w t i ≤ (Real.tan α ^ 2) ^ m *
        Real.exp (-((updateCount ε f xpi xstar w U t : ℝ) / m)) := by
      intro t
      induction t with
      | zero => rw [updateCount_zero, hrun.1]; simp; exact le_rfl
      | succ t ih =>
        obtain ⟨hxpi, hxs, hno, hyes⟩ := hrun.2.2.2 t
        rw [updateCount_succ]
        by_cases hu : IsUpdatePeriod ε f xpi xstar w U t
        · have htail := tail_ne_of_update ε f xpi xstar w U t hε.le hu
          have L3 := CtxInvOpt.Pointed.lemma3_cone_update_rate hm C0 cstar X f xstar t hxs (w t)
            (hinv t).1 (U t) (hinv t).2.1 (hinv t).2.2 (xpi t) hxpi htail (w (t+1)) (U (t+1))
            (hyes hu)
          rw [if_pos hu]
          refine (L3.2.2 h2).trans ?_
          have he : Real.exp (-((↑(updateCount ε f xpi xstar w U t + 1) : ℝ) / m)) =
              Real.exp (-(1 / (m:ℝ))) * Real.exp (-((updateCount ε f xpi xstar w U t : ℝ) / m)) := by
            rw [← Real.exp_add]; congr 1; push_cast; ring
          rw [he]
          have := mul_le_mul_of_nonneg_left ih (Real.exp_pos (-(1 / (m:ℝ)))).le
          linarith
        · rw [if_neg hu, ((hno hu).1)]
          simpa using ih
    -- lower bound on all eigenvalues
    set c : ℝ := (ε / (10 * ((m:ℝ) + 1))) ^ 2 with hcdef
    have hcpos : 0 < c := by positivity
    have hmin : ∀ t i, c ≤ w t i := by
      intro t
      induction t with
      | zero =>
        intro i; rw [hrun.1]
        refine le_trans ?_ hcond.le
        rw [hcdef]
        apply pow_le_pow_left₀ (by positivity)
        apply div_le_div_of_nonneg_left hε.le (by positivity); linarith
      | succ t ih =>
        obtain ⟨hxpi, hxs, hno, hyes⟩ := hrun.2.2.2 t
        by_cases hu : IsUpdatePeriod ε f xpi xstar w U t
        · have htail := tail_ne_of_update ε f xpi xstar w U t hε.le hu
          obtain ⟨P, hP, hN⟩ := coneUpdate_ge2 h2 (hyes hu)
          set v := tailVec (rotCoord (U t) (effDiff (f t (xpi t) - f t (xstar t)))) with hv
          obtain ⟨hd0, hd1, hdq⟩ := dbar_facts v htail (w t)
          set db := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v
          have hvv : v ⬝ᵥ v ≤ 1 := by
            have h1 := tail_sum_le (rotCoord (U t) (effDiff (f t (xpi t) - f t (xstar t))))
            rw [sum_sq_rotCoord _ (hinv t).2.1] at h1
            have h2 := norm_effDiff_le (f t (xpi t) - f t (xstar t))
            have : v ⬝ᵥ v = ∑ i : Fin m, rotCoord (U t) (effDiff (f t (xpi t) - f t (xstar t))) i.succ ^ 2 := by
              simp [hv, dotProduct, tailVec, sq]
            rw [this]; nlinarith [norm_nonneg (effDiff (f t (xpi t) - f t (xstar t)))]
          have hvpos : 0 < v ⬝ᵥ v := dot_self_pos v htail
          have hquad : ε ^ 2 < db ⬝ᵥ (Matrix.diagonal (w t) *ᵥ db) := by
            rw [hdq]
            have hu' : ε ^ 2 < ∑ i, w t i * v i ^ 2 := by
              have := hu; unfold IsUpdatePeriod tailQuad at this; simpa [hv, tailVec] using this
            rw [lt_div_iff₀ hvpos]
            have : 0 ≤ ε ^ 2 := sq_nonneg _
            nlinarith
          have hPD : (Matrix.diagonal (w t)).PosDef := Matrix.PosDef.diagonal (hinv t).1
          have hlamN : c ≤ FeaturePricing.Ellipsoid.lamMin
              (LinearOptimization.ellipsoidUpdateMatrix (Matrix.diagonal (w t)) db) := by
            by_cases hs : FeaturePricing.Ellipsoid.lamMin (Matrix.diagonal (w t)) ≤
                1 / (400 * (m:ℝ) ^ 2) * (2 * ε) ^ 2
            · have := FeaturePricing.Ellipsoid.lemma4_min_eigenvalue_no_decrease h2
                (by positivity : 0 < 2 * ε) _ hPD db hd1.le hs (by nlinarith)
              exact (le_lamMin_diag hm _ _ ih).trans this
            · replace hs := lt_of_not_ge hs
              have := FeaturePricing.Ellipsoid.lemma3_min_eigenvalue_shrink h2 _ hPD db hd0
              refine le_trans ?_ this
              have hk : c = (m:ℝ) ^ 2 / ((m:ℝ) + 1) ^ 2 * (1 / (400 * (m:ℝ) ^ 2) * (2 * ε) ^ 2) := by
                rw [hcdef]; field_simp; ring
              rw [hk]
              exact mul_le_mul_of_nonneg_left hs.le (by positivity)
          intro i
          refine hlamN.trans (lamMin_le _ _ ?_)
          rw [hN, spectrum_conj P hP]
          exact ⟨i, rfl⟩
        · rw [((hno hu).1)]; exact ih
    intro t
    have hwpos := (hinv t).1
    set I := updateCount ε f xpi xstar w U t
    have hcpow : 0 < c ^ (m - 1) := by positivity
    have hbound : ∀ i, w t i * c ^ (m - 1) ≤ ∏ j, w t j := by
      intro i
      rw [← Finset.mul_prod_erase Finset.univ (w t) (Finset.mem_univ i)]
      apply mul_le_mul_of_nonneg_left _ (hwpos i).le
      have := Finset.prod_le_prod (s := Finset.univ.erase i) (f := fun _ => c) (g := w t)
        (fun j _ => hcpos.le) (fun j _ => hmin t j)
      rwa [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin] at this
    have hkey : (10 * ((m:ℝ) + 1) / ε) ^ (2 * (m - 1)) = (c ^ (m - 1))⁻¹ := by
      rw [hcdef, ← pow_mul, ← inv_pow, inv_div]
    rw [hkey]
    unfold CtxInvOpt.Pointed.lamMax
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    apply ciSup_le
    intro i
    calc w t i = (w t i * c ^ (m - 1)) / c ^ (m - 1) := by field_simp
      _ ≤ (∏ j, w t j) / c ^ (m - 1) := div_le_div_of_nonneg_right (hbound i) hcpow.le
      _ ≤ ((Real.tan α ^ 2) ^ m * Real.exp (-((I : ℝ) / m))) / c ^ (m - 1) :=
          div_le_div_of_nonneg_right (hprod t) hcpow.le
      _ = (c ^ (m - 1))⁻¹ * (Real.tan α ^ 2) ^ m * Real.exp (-((I : ℝ) / m)) := by ring
  · intro hcase
    have hsmall : Real.tan α ^ 2 < ε ^ 2 := by
      refine hcase.trans_lt (pow_lt_pow_left₀ ?_ (by positivity) (by norm_num))
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    have key : ∀ t, w t = w 0 → ¬ IsUpdatePeriod ε f xpi xstar w U t := by
      intro t ht hu
      have := hupd_le t hu (Real.tan α ^ 2) (sq_nonneg _) (by intro i; rw [ht, hrun.1])
      linarith
    have hnu : ∀ t, w t = w 0 ∧ ¬ IsUpdatePeriod ε f xpi xstar w U t := by
      intro t
      induction t with
      | zero => exact ⟨rfl, key 0 rfl⟩
      | succ t ih =>
        have h1 := ((hrun.2.2.2 t).2.2.1 ih.2).1
        have : w (t+1) = w 0 := h1.trans ih.1
        exact ⟨this, key _ this⟩
    refine ⟨fun t => ?_, fun t => ?_⟩
    · unfold updateCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      exact (hnu x).2
    · obtain ⟨hxpi, hxs, -, -⟩ := hrun.2.2.2 t
      exact CtxInvOpt.Pointed.lemma4_low_regret_period hε C0 hC0 cstar hcstar X f xstar
        (fun s => (hrun.2.2.2 s).2.1) t (hX t) (hf t) (w t) (hinv t).1 (U t) (hinv t).2.1
        (hinv t).2.2 (xpi t) hxpi (le_of_not_gt (hnu t).2)
