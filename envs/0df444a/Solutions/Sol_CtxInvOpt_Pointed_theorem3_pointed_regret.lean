-- Prove2me | solution 1 for CtxInvOpt.Pointed.theorem3_pointed_regret
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:14:53.894303+00:00
-- url     : https://prove2.me/submissions/31d0b913-8de1-4137-8328-8af3284aa808

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_Run
import Theorems.Thm_CtxInvOpt_Pointed_lemma4_low_regret_period
import Theorems.Thm_CtxInvOpt_Pointed_lemma3_cone_update_rate
import Theorems.Thm_CtxInvOpt_Pointed_lemmaB1_cone_update
import Theorems.Thm_CtxInvOpt_Pointed_lemma5_largest_eigenvalue

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

set_option maxHeartbeats 2000000 in
open Classical in
theorem solution :
    ∃ K : ℝ, ∀ (m n T : ℕ), 1 ≤ m → 1 ≤ n → 1 ≤ T →
      ∀ C0 : Set (EuclideanSpace ℝ (Fin (m + 1))), IsClosed C0 → C0 ⊆ CtxInvOpt.Offline.unitSphere (m + 1) →
        C0.Nonempty → 0 < CtxInvOpt.Offline.uncAngle C0 → CtxInvOpt.Offline.uncAngle C0 < Real.pi / 2 →
        ∀ cstar ∈ C0,
        ∀ (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
          (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
          (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (w : ℕ → Fin m → ℝ)
          (U : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ),
        (∀ t, CtxInvOpt.Offline.IsActionSet (X t)) → (∀ t, CtxInvOpt.Offline.IsContext (f t)) →
        CtxInvOpt.Pointed.IsEllConesRun (((m : ℝ) + 1) / T) C0 cstar X f xpi xstar w U →
        (Real.arctan (((m : ℝ) + 1) / T) < CtxInvOpt.Offline.uncAngle C0 →
            CtxInvOpt.Greedy.cumRegret cstar f xpi xstar T ≤
              K * ((m : ℝ) + 1) ^ 2 * Real.log (T * Real.tan (CtxInvOpt.Offline.uncAngle C0))) ∧
          (CtxInvOpt.Offline.uncAngle C0 ≤ Real.arctan (((m : ℝ) + 1) / T) →
            CtxInvOpt.Greedy.cumRegret cstar f xpi xstar T ≤ K * ((m : ℝ) + 1)) := by
  refine ⟨9, ?_⟩
  intro m n T hm hn hT C0 hC0closed hC0 hC0ne hα0 hα cstar hcstar X f xpi xstar w U hX hf hrun
  set α := CtxInvOpt.Offline.uncAngle C0 with hαdef
  set ε : ℝ := ((m:ℝ)+1)/T with hεdef
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hεpos : 0 < ε := by positivity
  have hτ : 0 < Real.tan α := Real.tan_pos_of_pos_of_lt_pi_div_two hα0 hα
  have hinit : C0 ⊆ ellCone (w 0) (U 0) := by
    rw [hrun.1]; exact Thm3Red.init_contain C0 hC0 hα0 hα (U 0) hrun.2.1 hrun.2.2.1
  have hinv := Thm3Red.invariant ε f xpi xstar w U hm C0 cstar X hεpos.le hrun hinit hτ
  have hcn : ‖cstar‖ = 1 := by simpa [CtxInvOpt.Offline.unitSphere] using hC0 hcstar
  have hper : ∀ t, inner ℝ (f t (xpi t) - f t (xstar t)) cstar ≤
      ε + (if IsUpdatePeriod ε f xpi xstar w U t then 1 else 0) := by
    intro t
    obtain ⟨hxpi, hxs, -, -⟩ := hrun.2.2.2 t
    split_ifs with hu
    · have := Thm3Red.period_le_one (X t) (hX t) (f t) (hf t) _ _ hxpi.1 hxs.1 cstar hcn
      linarith
    · have := lemma4_low_regret_period hεpos C0 hC0 cstar hcstar X f xstar
        (fun s => (hrun.2.2.2 s).2.1) t (hX t) (hf t) (w t) (hinv t).1 (U t) (hinv t).2.1
        (hinv t).2.2 (xpi t) hxpi (le_of_not_gt hu)
      linarith
  have hreg := Thm3Red.regret_le ε f xpi xstar w U cstar hper T
  have hεT : ε * T = (m:ℝ) + 1 := by rw [hεdef]; field_simp
  rw [hεT] at hreg
  have hupd_le : ∀ t, IsUpdatePeriod ε f xpi xstar w U t → ∀ c, 0 ≤ c → (∀ i, w t i ≤ c) →
      ε ^ 2 < c := by
    intro t hu c hc hwc
    exact lt_of_lt_of_le hu
      (Thm3Red.tailQuad_le _ c hc hwc _ (hinv t).2.1 _ (Thm3Red.norm_effDiff_le _))
  constructor
  · intro hcase
    have hετ : ε < Real.tan α := by
      have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two
        (by linarith [Real.neg_pi_div_two_lt_arctan ε]) hα hcase
      rwa [Real.tan_arctan] at this
    set L := Real.log (T * Real.tan α) with hL
    have hTτ : (m:ℝ) + 1 < T * Real.tan α := by
      rw [← hεT, mul_comm ε]
      exact mul_lt_mul_of_pos_left hετ hTpos
    have hLe : L = Real.log T + Real.log (Real.tan α) :=
      Real.log_mul (by positivity) (by positivity)
    have hlε : Real.log ε = Real.log ((m:ℝ)+1) - Real.log T :=
      Real.log_div (by positivity) (by positivity)
    have hLlog : Real.log ((m:ℝ)+1) < L := Real.log_lt_log (by positivity) hTτ
    have hlog2 : Real.log 2 ≤ Real.log ((m:ℝ)+1) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog2pos := Real.log_two_gt_d9
    have hLpos : 0 < L := by linarith
    rcases (by omega : m = 1 ∨ 2 ≤ m) with h1 | h2
    · subst h1
      have hform : ∀ t i, w t i =
          Real.tan α ^ 2 * (1/2:ℝ) ^ (updateCount ε f xpi xstar w U t) := by
        intro t
        induction t with
        | zero => intro i; rw [Thm3Red.updateCount_zero, hrun.1]; simp; rfl
        | succ t ih =>
          intro i
          rw [Thm3Red.updateCount_succ]
          by_cases hu : IsUpdatePeriod ε f xpi xstar w U t
          · rw [if_pos hu, Thm3Red.coneUpdate_one ((hrun.2.2.2 t).2.2.2 hu) i, ih i, pow_succ]
            ring
          · rw [if_neg hu, ((hrun.2.2.2 t).2.2.1 hu).1, ih i]
            simp
      have hcnt : ∀ t, IsUpdatePeriod ε f xpi xstar w U t →
          (updateCount ε f xpi xstar w U t : ℝ) < 3 * L := by
        intro t hu
        set I := updateCount ε f xpi xstar w U t
        have hlt : ε ^ 2 < Real.tan α ^ 2 * (1/2:ℝ) ^ I :=
          hupd_le t hu _ (by positivity) (fun i => (hform t i).le)
        have := Real.log_lt_log (by positivity) hlt
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
          Real.log_pow, one_div, Real.log_inv] at this
        have hI : (0:ℝ) ≤ I := Nat.cast_nonneg _
        rw [hlε] at this
        norm_num at this hlog2 ⊢
        nlinarith
      have hI := Thm3Red.count_le ε f xpi xstar w U (3 * L) (by positivity) hcnt T
      norm_num at hreg hI ⊢
      nlinarith
    · have hcond : (ε / (10 * (m:ℝ))) ^ 2 < Real.tan α ^ 2 := by
        have h10 : ε / (10 * (m:ℝ)) < ε := by
          rw [div_lt_iff₀ (by positivity)]; nlinarith
        exact pow_lt_pow_left₀ (h10.trans hετ) (by positivity) (by norm_num)
      have L5 := (lemma5_largest_eigenvalue hm hn hεpos C0 hC0closed hC0 hC0ne hα0 hα cstar hcstar
        X f xpi xstar w U hX hf hrun).1 h2 hcond
      have hm2 : (2:ℝ) ≤ m := by exact_mod_cast h2
      have hlog3 : Real.log 3 ≤ Real.log ((m:ℝ)+1) :=
        Real.log_le_log (by norm_num) (by linarith)
      have hlog3gt : 1 < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9; linarith
      have hlog10 : Real.log 10 < 3 * Real.log 3 := by
        rw [← Real.log_rpow (by norm_num)]
        exact Real.log_lt_log (by norm_num) (by norm_num)
      have hcnt : ∀ t, IsUpdatePeriod ε f xpi xstar w U t →
          (updateCount ε f xpi xstar w U t : ℝ) < 8 * (m:ℝ) ^ 2 * L := by
        intro t hu
        set I := updateCount ε f xpi xstar w U t
        have hwpos := (hinv t).1
        have hlam0 : 0 ≤ lamMax (w t) :=
          (hwpos ⟨0, by omega⟩).le.trans (Thm3Red.le_lamMax _ _)
        have hlt : ε ^ 2 < lamMax (w t) :=
          hupd_le t hu _ hlam0 (fun i => Thm3Red.le_lamMax _ i)
        have hlt2 := hlt.trans_le (L5 t)
        have h10T : 10 * ((m:ℝ) + 1) / ε = 10 * T := by rw [hεdef]; field_simp
        rw [h10T] at hlt2
        have := Real.log_lt_log (by positivity) hlt2
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
          (by positivity), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_exp,
          Real.log_mul (by norm_num) (by positivity), hlε] at this
        push_cast [Nat.cast_sub hm] at this
        have hI : (0:ℝ) ≤ I := Nat.cast_nonneg _
        have hmpos : (0:ℝ) < m := by linarith
        set q : ℝ := (I:ℝ) / m with hqdef
        set a := Real.log T
        set b := Real.log (Real.tan α)
        set c := Real.log ((m:ℝ) + 1)
        set e := Real.log 10
        have key : 2 * (c - a) < 2 * ((m:ℝ) - 1) * (e + a) + m * (2 * b) + -q := by
          convert this using 2
        have e1 : ((m:ℝ) - 1) * e ≤ ((m:ℝ) - 1) * (3 * L) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have e2 : (m:ℝ) * L = m * a + m * b := by rw [hLe]; ring
        have hcpos : 0 < c := by linarith
        have hq : q < 8 * m * L := by
          ring_nf at key e1 e2 ⊢
          linarith
        have hIq : (I:ℝ) = m * q := by rw [hqdef]; field_simp
        rw [hIq]
        have := mul_lt_mul_of_pos_left hq hmpos
        nlinarith
      have hI := Thm3Red.count_le ε f xpi xstar w U _ (by positivity) hcnt T
      have hL1 : 1 ≤ L := by linarith
      have f1 : ((m:ℝ) + 1) ^ 2 ≤ ((m:ℝ) + 1) ^ 2 * L := le_mul_of_one_le_right (by positivity) hL1
      have f2 : (m:ℝ) ^ 2 * L ≤ ((m:ℝ) + 1) ^ 2 * L :=
        mul_le_mul_of_nonneg_right (by nlinarith) hLpos.le
      have f3 : (m:ℝ) + 2 ≤ ((m:ℝ) + 1) ^ 2 := by nlinarith
      linarith
  · intro hcase
    have hτε : Real.tan α ≤ ε := by
      by_contra hcon
      replace hcon := lt_of_not_ge hcon
      have := Real.arctan_strictMono hcon
      rw [Real.arctan_tan (by linarith [Real.pi_pos]) hα] at this
      linarith
    have key : ∀ t, w t = w 0 → ¬ IsUpdatePeriod ε f xpi xstar w U t := by
      intro t ht hu
      have := hupd_le t hu (Real.tan α ^ 2) (sq_nonneg _) (by intro i; rw [ht, hrun.1])
      nlinarith
    have hnu : ∀ t, w t = w 0 ∧ ¬ IsUpdatePeriod ε f xpi xstar w U t := by
      intro t
      induction t with
      | zero => exact ⟨rfl, key 0 rfl⟩
      | succ t ih =>
        have h1 := ((hrun.2.2.2 t).2.2.1 ih.2).1
        have : w (t+1) = w 0 := h1.trans ih.1
        exact ⟨this, key _ this⟩
    have hc0 : updateCount ε f xpi xstar w U T = 0 := by
      unfold updateCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      exact (hnu x).2
    rw [hc0] at hreg
    push_cast at hreg
    nlinarith
