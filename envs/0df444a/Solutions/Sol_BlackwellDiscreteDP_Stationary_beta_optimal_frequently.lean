-- Prove2me | solution 1 for BlackwellDiscreteDP.Stationary.beta_optimal_frequently
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:25:45.801371+00:00
-- url     : https://prove2.me/submissions/712771ff-221f-403f-9042-4f7c567995a0

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model



namespace BlackwellDiscreteDP.Stationary

open Model
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]

lemma bw_Qn_stoch (M : Model St Act) (π : Policy St Act) (n : ℕ) :
    (∀ i j, 0 ≤ M.Qn π n i j) ∧ ∀ i, ∑ j, M.Qn π n i j = 1 := by
  induction n with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [Model.Qn, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Model.Qn, Matrix.one_apply]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [Model.Qn, Matrix.mul_apply, Model.Q, Matrix.of_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (h1 i k) ((M.law_kernel k (π n k)).1 j)
    · simp only [Model.Qn, Matrix.mul_apply, Model.Q, Matrix.of_apply]
      rw [Finset.sum_comm]
      rw [← h2 i]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, (M.law_kernel k (π n k)).2, mul_one]

/-- bound of a stochastic matrix applied to a vector -/
lemma bw_stoch_mulVec_le {A : Matrix St St ℝ} (h1 : ∀ i j, 0 ≤ A i j) (h2 : ∀ i, ∑ j, A i j = 1)
    {u v : St → ℝ} {c : ℝ} (huv : ∀ s, u s ≤ v s + c) (i : St) :
    (A.mulVec u) i ≤ (A.mulVec v) i + c := by
  show ∑ j, A i j * u j ≤ ∑ j, A i j * v j + c
  calc ∑ j, A i j * u j ≤ ∑ j, A i j * (v j + c) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (huv j) (h1 i j)
    _ = ∑ j, A i j * v j + c := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h2 i, one_mul]

lemma bw_stoch_abs {A : Matrix St St ℝ} (h1 : ∀ i j, 0 ≤ A i j) (h2 : ∀ i, ∑ j, A i j = 1)
    {u : St → ℝ} {c : ℝ} (hu : ∀ s, |u s| ≤ c) (i : St) : |(A.mulVec u) i| ≤ c := by
  have e : ∀ v : St → ℝ, (A.mulVec v) i = ∑ j, A i j * v j := fun v => rfl
  rw [abs_le, e]
  constructor
  · calc -c = ∑ j, A i j * (-c) := by rw [← Finset.sum_mul, h2 i, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_le.1 (hu j)).1 (h1 i j)
  · calc ∑ j, A i j * u j ≤ ∑ j, A i j * c :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_le.1 (hu j)).2 (h1 i j)
      _ = c := by rw [← Finset.sum_mul, h2 i, one_mul]

noncomputable def bwR (M : Model St Act) : ℝ := ∑ s, ∑ a, |M.income s a|

lemma bw_r_abs (M : Model St Act) (f : St → Act) (s : St) : |M.r f s| ≤ bwR M := by
  unfold bwR Model.r
  calc |M.income s (f s)| ≤ ∑ a, |M.income s a| :=
        Finset.single_le_sum (f := fun a => |M.income s a|) (fun a _ => abs_nonneg _) (Finset.mem_univ _)
    _ ≤ ∑ s, ∑ a, |M.income s a| :=
        Finset.single_le_sum (f := fun s => ∑ a, |M.income s a|)
          (fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _) (Finset.mem_univ _)

lemma bwR_nonneg (M : Model St Act) : 0 ≤ bwR M :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _

lemma bw_term_abs (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (n : ℕ) (s : St) :
    |β ^ n * (M.Qn π n).mulVec (M.r (π n)) s| ≤ bwR M * β ^ n := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 n), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (bw_stoch_abs (bw_Qn_stoch M π n).1 (bw_Qn_stoch M π n).2 (bw_r_abs M (π n)) s)
    (pow_nonneg hβ0 n)

lemma bw_term_summable (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s : St) : Summable (fun n => β ^ n * (M.Qn π n).mulVec (M.r (π n)) s) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (bwR M))
    (fun n => by rw [Real.norm_eq_abs]; exact bw_term_abs M π β hβ0 n s)

lemma bw_V_apply (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s : St) : M.V β π s = ∑' n, β ^ n * (M.Qn π n).mulVec (M.r (π n)) s := by
  unfold Model.V
  rw [tsum_apply]
  · rfl
  · exact Pi.summable.2 fun s => bw_term_summable M π β hβ0 hβ1 s

lemma bw_V_abs (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s : St) : |M.V β π s| ≤ bwR M / (1 - β) := by
  rw [bw_V_apply M π β hβ0 hβ1]
  have hs : Summable (fun n => ‖β ^ n * (M.Qn π n).mulVec (M.r (π n)) s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact bw_term_abs M π β hβ0 n s)
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (bwR M))
  calc |∑' n, β ^ n * (M.Qn π n).mulVec (M.r (π n)) s|
        = ‖∑' n, β ^ n * (M.Qn π n).mulVec (M.r (π n)) s‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖β ^ n * (M.Qn π n).mulVec (M.r (π n)) s‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, bwR M * β ^ n := Summable.tsum_le_tsum
          (fun n => by rw [Real.norm_eq_abs]; exact bw_term_abs M π β hβ0 n s) hs
          ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (bwR M))
    _ = bwR M / (1 - β) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]

lemma bw_Qn_cons (M : Model St Act) (f : St → Act) (π : Policy St Act) (n : ℕ) :
    M.Qn (Policy.cons f π) (n + 1) = M.Q f * M.Qn π n := by
  induction n with
  | zero => simp [Model.Qn, Policy.cons]
  | succ n ih =>
    rw [Model.Qn, ih, Model.Qn, Matrix.mul_assoc]
    rfl

lemma bw_V_cons (M : Model St Act) (f : St → Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : M.V β (Policy.cons f π) = M.L β f (M.V β π) := by
  funext s
  rw [bw_V_apply M _ β hβ0 hβ1, (bw_term_summable M _ β hβ0 hβ1 s).tsum_eq_zero_add]
  simp only [Model.L, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · simp [Model.Qn, Policy.cons]
  · have : ∀ n, β ^ (n + 1) * (M.Qn (Policy.cons f π) (n + 1)).mulVec (M.r (Policy.cons f π (n + 1))) s
        = β * ∑ s', M.Q f s s' * (β ^ n * (M.Qn π n).mulVec (M.r (π n)) s') := by
      intro n
      rw [bw_Qn_cons, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, Policy.cons, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring_nf
    simp_rw [this]
    rw [tsum_mul_left, Summable.tsum_finsetSum (fun s' _ => (bw_term_summable M π β hβ0 hβ1 s').mul_left _)]
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [tsum_mul_left, bw_V_apply M π β hβ0 hβ1]
    rfl

lemma bw_cons_stationary (f : St → Act) : Policy.cons f (stationary f) = stationary f := by
  funext n; cases n <;> rfl

lemma bw_V_fix (M : Model St Act) (f : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    M.V β (stationary f) = M.L β f (M.V β (stationary f)) := by
  conv_lhs => rw [← bw_cons_stationary f]
  exact bw_V_cons M f _ β hβ0 hβ1

lemma bw_Q_stoch (M : Model St Act) (f : St → Act) :
    (∀ i j, 0 ≤ M.Q f i j) ∧ ∀ i, ∑ j, M.Q f i j = 1 :=
  ⟨fun i j => (M.law_kernel i (f i)).1 j, fun i => (M.law_kernel i (f i)).2⟩

lemma bw_L_apply (M : Model St Act) (β : ℝ) (f : St → Act) (w : St → ℝ) (s : St) :
    M.L β f w s = M.income s (f s) + β * ∑ s', M.law s (f s) s' * w s' := rfl

lemma bw_L_le (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (f : St → Act) {u v : St → ℝ} {c : ℝ}
    (huv : ∀ s, u s ≤ v s + c) (s : St) : M.L β f u s ≤ M.L β f v s + β * c := by
  have := bw_stoch_mulVec_le (bw_Q_stoch M f).1 (bw_Q_stoch M f).2 huv s
  show M.r f s + β * (M.Q f).mulVec u s ≤ M.r f s + β * (M.Q f).mulVec v s + β * c
  nlinarith

lemma bw_L_mono (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (f : St → Act) {u v : St → ℝ}
    (huv : u ≤ v) : M.L β f u ≤ M.L β f v := by
  intro s
  have := bw_L_le M β hβ0 f (u := u) (v := v) (c := 0) (fun s => by simpa using huv s) s
  simpa using this

lemma bw_cons_shift (π : Policy St Act) : Policy.cons (π 0) (Policy.shift π) = π := by
  funext n; cases n <;> rfl

theorem bw_thm1 (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (πstar : Policy St Act)
    (h : ∀ f : St → Act, M.V β (Policy.cons f πstar) ≤ M.V β πstar) :
    M.IsBetaOptimal β πstar := by
  set D := Set.range (fun p : Policy St Act × St => M.V β p.1 p.2 - M.V β πstar p.2) with hD
  have hbdd : BddAbove D := by
    refine ⟨2 * (bwR M / (1 - β)), ?_⟩
    rintro _ ⟨⟨π, s⟩, rfl⟩
    have h1 := (abs_le.1 (bw_V_abs M π β hβ0 hβ1 s)).2
    have h2 := (abs_le.1 (bw_V_abs M πstar β hβ0 hβ1 s)).1
    simp only; linarith
  have hne : D.Nonempty := ⟨_, ⟨(πstar, Classical.arbitrary St), rfl⟩⟩
  have hle : ∀ π s, M.V β π s - M.V β πstar s ≤ sSup D :=
    fun π s => le_csSup hbdd ⟨(π, s), rfl⟩
  have key : ∀ π s, M.V β π s - M.V β πstar s ≤ β * sSup D := by
    intro π s
    have e : M.V β π = M.L β (π 0) (M.V β (Policy.shift π)) := by
      conv_lhs => rw [← bw_cons_shift π]
      exact bw_V_cons M _ _ β hβ0 hβ1
    have h1 := bw_L_le M β hβ0 (π 0) (u := M.V β (Policy.shift π)) (v := M.V β πstar)
      (c := sSup D) (fun s' => by linarith [hle (Policy.shift π) s']) s
    have h2 := h (π 0) s
    rw [bw_V_cons M _ _ β hβ0 hβ1] at h2
    rw [e]; linarith
  have hd : sSup D ≤ β * sSup D := csSup_le hne (by rintro _ ⟨⟨π, s⟩, rfl⟩; exact key π s)
  have hd0 : sSup D ≤ 0 := by nlinarith
  intro π s
  linarith [hle π s]

lemma bw_le_V_stat (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (w : St → ℝ) (hw : w ≤ M.L β f w) : w ≤ M.V β (stationary f) := by
  set Vf := M.V β (stationary f)
  obtain ⟨s0, hs0⟩ := Finite.exists_max (fun s => w s - Vf s)
  have h1 := bw_L_le M β hβ0 f (u := w) (v := Vf) (c := w s0 - Vf s0)
    (fun s => by have : w s - Vf s ≤ w s0 - Vf s0 := hs0 s; linarith) s0
  have hfix := congrFun (bw_V_fix M f β hβ0 hβ1) s0
  have h2 := hw s0
  have hd : w s0 - Vf s0 ≤ 0 := by nlinarith
  intro s
  have : w s - Vf s ≤ w s0 - Vf s0 := hs0 s; linarith

theorem bw_thm2 (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (π : Policy St Act)
    (h : M.V β π ≤ M.V β (Policy.cons f π) ∧ M.V β (Policy.cons f π) ≠ M.V β π) :
    M.V β π ≤ M.V β (stationary f) ∧ M.V β (stationary f) ≠ M.V β π := by
  rw [bw_V_cons M f π β hβ0 hβ1] at h
  have hw := bw_le_V_stat M β hβ0 hβ1 f _ h.1
  refine ⟨hw, fun heq => h.2 ?_⟩
  have h3 : M.L β f (M.V β π) ≤ M.V β π := by
    have := bw_L_mono M β hβ0 f hw
    rw [← bw_V_fix M f β hβ0 hβ1, heq] at this
    exact this
  exact le_antisymm h3 h.1

theorem bw_thm3 (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act) :
    ((∀ s : St, M.G β f s = ∅) → M.IsBetaOptimal β (stationary f)) ∧
    (∀ g : St → Act, (∃ s : St, g s ∈ M.G β f s) →
        (∀ s : St, g s ∉ M.G β f s → g s = f s) →
        M.V β (stationary f) ≤ M.V β (stationary g) ∧
          M.V β (stationary g) ≠ M.V β (stationary f)) := by
  constructor
  · intro hG
    apply bw_thm1 M β hβ0 hβ1
    intro g s
    rw [bw_V_cons M g _ β hβ0 hβ1, bw_L_apply]
    by_contra hlt
    push_neg at hlt
    have : g s ∈ M.G β f s := hlt
    rw [hG s] at this
    exact this
  · intro g ⟨s0, hs0⟩ hb
    apply bw_thm2 M β hβ0 hβ1 g (stationary f)
    rw [bw_V_cons M g _ β hβ0 hβ1]
    have hfix := bw_V_fix M f β hβ0 hβ1
    have hge : ∀ s, M.V β (stationary f) s ≤ M.L β g (M.V β (stationary f)) s := by
      intro s
      by_cases hs : g s ∈ M.G β f s
      · rw [bw_L_apply]; exact le_of_lt hs
      · have e : M.L β g (M.V β (stationary f)) s = M.L β f (M.V β (stationary f)) s := by
          simp only [bw_L_apply, hb s hs]
        rw [e, ← hfix]
    refine ⟨hge, fun heq => ?_⟩
    have := congrFun heq s0
    have hs0' : M.V β (stationary f) s0 < M.L β g (M.V β (stationary f)) s0 := by
      rw [bw_L_apply]; exact hs0
    linarith

lemma bw_improve (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (hs : ∃ s, (M.G β f s).Nonempty) :
    ∃ g : St → Act, M.V β (stationary f) ≤ M.V β (stationary g) ∧
          M.V β (stationary g) ≠ M.V β (stationary f) := by
  classical
  let g : St → Act := fun s => if h : (M.G β f s).Nonempty then h.some else f s
  refine ⟨g, (bw_thm3 M β hβ0 hβ1 f).2 g ?_ ?_⟩
  · obtain ⟨s, hs⟩ := hs
    refine ⟨s, ?_⟩
    simp only [g, dif_pos hs]; exact hs.some_mem
  · intro s hgs
    by_cases h : (M.G β f s).Nonempty
    · exfalso; apply hgs; simp only [g, dif_pos h]; exact h.some_mem
    · simp only [g, dif_neg h]

lemma bw_opt_of_stat (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (h : ∀ g : St → Act, M.V β (stationary g) ≤ M.V β (stationary f)) :
    M.IsBetaOptimal β (stationary f) := by
  by_cases hs : ∃ s, (M.G β f s).Nonempty
  · obtain ⟨g, h1, h2⟩ := bw_improve M β hβ0 hβ1 f hs
    exact absurd (le_antisymm (h g) h1) h2
  · push_neg at hs
    exact (bw_thm3 M β hβ0 hβ1 f).1 fun s => hs s

lemma bw_exists_opt (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ f : St → Act, M.IsBetaOptimal β (stationary f) := by
  obtain ⟨f, hf⟩ := Finite.exists_max (fun f : St → Act => ∑ s, M.V β (stationary f) s)
  refine ⟨f, ?_⟩
  by_cases hs : ∃ s, (M.G β f s).Nonempty
  · obtain ⟨g, h1, h2⟩ := bw_improve M β hβ0 hβ1 f hs
    exfalso
    have hne : ∃ s, M.V β (stationary f) s < M.V β (stationary g) s := by
      by_contra hc
      push_neg at hc
      exact h2 (funext fun s => le_antisymm (hc s) (h1 s))
    obtain ⟨s, hs⟩ := hne
    have := Finset.sum_lt_sum (fun i _ => h1 i) ⟨s, Finset.mem_univ s, hs⟩
    have := hf g
    linarith
  · push_neg at hs
    exact (bw_thm3 M β hβ0 hβ1 f).1 fun s => hs s

theorem bw_frequently (M : Model St Act) :
    ∃ fstar : St → Act, ∀ β₀ : ℝ, β₀ < 1 →
      ∃ β : ℝ, β₀ < β ∧ β < 1 ∧ M.IsBetaOptimal β (stationary fstar) := by
  by_contra H
  push_neg at H
  choose b hb1 hb using H
  set m := Finset.univ.sup' Finset.univ_nonempty b with hm
  have hm1 : m < 1 := by
    rw [hm, Finset.sup'_lt_iff]; exact fun f _ => hb1 f
  set B := max m 0
  have hB1 : B < 1 := max_lt hm1 one_pos
  obtain ⟨f, hf⟩ := bw_exists_opt M ((B + 1) / 2) (by have := le_max_right m 0; linarith)
    (by linarith)
  have hbf : b f ≤ m := Finset.le_sup' b (Finset.mem_univ f)
  exact hb f ((B + 1) / 2) (by have := le_max_left m 0; linarith) (by linarith) hf

end BlackwellDiscreteDP.Stationary

open BlackwellDiscreteDP.Stationary


theorem solution {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act) :
    ∃ fstar : St → Act, ∀ β₀ : ℝ, β₀ < 1 →
      ∃ β : ℝ, β₀ < β ∧ β < 1 ∧ M.IsBetaOptimal β (stationary fstar) := by
  exact bw_frequently M
