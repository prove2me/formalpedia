-- Prove2me | solution 1 for DermanDenumerable.AvgCost.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:42:06.831202+00:00
-- url     : https://prove2.me/submissions/a3b554da-08b2-471e-b1cc-cd74910dd6bd

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology ENNReal NNReal
open Filter SennottDP.AvgFinite DermanDenumerable.AvgCost

namespace DermanAvgAux

variable {S Act : Type} [Countable S]

/-- expectation of a `[0,∞]`-valued function of the history, over histories of length `n`. -/
noncomputable def ExL {M : MDC S Act} (θ : Policy M) (i : S) (n : ℕ)
    (F : List (S × Act) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' h : List (S × Act), if h.length = n then histProb θ i h * F h else 0

def onHead (Φ : S → Act → ℝ≥0∞) : List (S × Act) → ℝ≥0∞
  | [] => 0
  | p :: _ => Φ p.1 p.2

lemma ExL_zero {M : MDC S Act} (θ : Policy M) (i : S) (F : List (S × Act) → ℝ≥0∞) :
    ExL θ i 0 F = F [] := by
  unfold ExL
  rw [tsum_eq_single []]
  · simp [histProb]
  · intro h hh
    simp [List.length_eq_zero_iff, hh]

lemma ExL_succ {M : MDC S Act} (θ : Policy M) (i : S) (n : ℕ) (F : List (S × Act) → ℝ≥0∞) :
    ExL θ i (n+1) F = ExL θ i n (fun rest => ∑' p : S × Act,
      prevWeight M i rest p.1 * θ.prob rest p.1 p.2 * F (p :: rest)) := by
  unfold ExL
  have hinj : Function.Injective (fun x : (S × Act) × List (S × Act) => x.1 :: x.2) := by
    intro x y hxy
    simp only [List.cons.injEq] at hxy
    exact Prod.ext hxy.1 hxy.2
  rw [← hinj.tsum_eq]
  · rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    congr 1; funext rest
    by_cases hr : rest.length = n
    · simp only [List.length_cons, hr, if_true]
      rw [← ENNReal.tsum_mul_left]; congr 1; funext p
      obtain ⟨j, a⟩ := p
      simp only [histProb]; ring
    · simp [List.length_cons, hr]
  · intro h hh
    cases h with
    | nil => simp at hh
    | cons p rest => exact ⟨(p, rest), rfl⟩

lemma sum_prob {M : MDC S Act} (θ : Policy M) (rest : List (S × Act)) (j : S) :
    ∑' a, θ.prob rest j a = 1 := by
  rw [tsum_eq_sum (s := M.A j) (fun a ha => θ.prob_supp rest j a ha)]
  exact θ.prob_sum rest j

lemma sum_prevWeight (M : MDC S Act) (i : S) (rest : List (S × Act)) :
    ∑' j, prevWeight M i rest j = 1 := by
  cases rest with
  | nil => simp [prevWeight]
  | cons p rest => obtain ⟨k, b⟩ := p; simp [prevWeight, M.P_sum]

lemma inner_sum {M : MDC S Act} (θ : Policy M) (i : S) (rest : List (S × Act)) (G : S → ℝ≥0∞) :
    ∑' p : S × Act, prevWeight M i rest p.1 * θ.prob rest p.1 p.2 * G p.1 =
      ∑' j, prevWeight M i rest j * G j := by
  rw [ENNReal.tsum_prod']
  congr 1; funext j
  calc ∑' a, prevWeight M i rest j * θ.prob rest j a * G j
      = (prevWeight M i rest j * G j) * ∑' a, θ.prob rest j a := by
        rw [← ENNReal.tsum_mul_left]; congr 1; funext a; ring
    _ = _ := by rw [sum_prob, mul_one]

lemma ExL_one {M : MDC S Act} (θ : Policy M) (i : S) (n : ℕ) :
    ExL θ i n (fun _ => 1) = 1 := by
  induction n with
  | zero => rw [ExL_zero]
  | succ n ih =>
    rw [ExL_succ]
    calc _ = ExL θ i n (fun _ => 1) := by
          congr 1; funext rest
          have := inner_sum θ i rest (fun _ => 1)
          simp only [mul_one] at this ⊢
          rw [this, sum_prevWeight]
      _ = 1 := ih

lemma ExL_congr {M : MDC S Act} (θ : Policy M) (i : S) (n : ℕ) {F G : List (S × Act) → ℝ≥0∞}
    (h : ∀ x, x.length = n → histProb θ i x ≠ 0 → F x = G x) : ExL θ i n F = ExL θ i n G := by
  unfold ExL; congr 1; funext x
  split_ifs with hx
  · by_cases h0 : histProb θ i x = 0
    · simp [h0]
    · rw [h x hx h0]
  · rfl

lemma ExL_mono {M : MDC S Act} (θ : Policy M) (i : S) (n : ℕ) {F G : List (S × Act) → ℝ≥0∞}
    (h : ∀ x, x.length = n → histProb θ i x ≠ 0 → F x ≤ G x) : ExL θ i n F ≤ ExL θ i n G := by
  unfold ExL
  refine ENNReal.tsum_le_tsum fun x => ?_
  split_ifs with hx
  · by_cases h0 : histProb θ i x = 0
    · simp [h0]
    · exact mul_le_mul_right (h x hx h0) _
  · exact le_rfl

lemma ExL_add {M : MDC S Act} (θ : Policy M) (i : S) (n : ℕ) (F G : List (S × Act) → ℝ≥0∞) :
    ExL θ i n (fun x => F x + G x) = ExL θ i n F + ExL θ i n G := by
  unfold ExL
  rw [← ENNReal.tsum_add]
  congr 1; funext x
  split_ifs <;> simp [mul_add]

lemma ExL_const_mul {M : MDC S Act} (θ : Policy M) (i : S) (n : ℕ) (c : ℝ≥0∞)
    (F : List (S × Act) → ℝ≥0∞) :
    ExL θ i n (fun x => c * F x) = c * ExL θ i n F := by
  unfold ExL
  rw [← ENNReal.tsum_mul_left]
  congr 1; funext x
  split_ifs <;> simp; ring

lemma ExL_const {M : MDC S Act} (θ : Policy M) (i : S) (n : ℕ) (c : ℝ≥0∞) :
    ExL θ i n (fun _ => c) = c := by
  have := ExL_const_mul θ i n c (fun _ => 1)
  simp only [mul_one] at this
  rw [this, ExL_one, mul_one]

lemma ExL_le_const {M : MDC S Act} (θ : Policy M) (i : S) (n : ℕ) {F : List (S × Act) → ℝ≥0∞}
    (c : ℝ≥0∞) (h : ∀ x, x.length = n → histProb θ i x ≠ 0 → F x ≤ c) : ExL θ i n F ≤ c := by
  calc ExL θ i n F ≤ ExL θ i n (fun _ => c) := ExL_mono θ i n h
    _ = c := ExL_const θ i n c

lemma prob_ne_zero_of_hp {M : MDC S Act} {θ : Policy M} {i : S} {rest : List (S × Act)} {j : S}
    {a : Act} (h : histProb θ i ((j, a) :: rest) ≠ 0) : θ.prob rest j a ≠ 0 := by
  intro h0; apply h; simp [histProb, h0]

lemma mem_of_hp {M : MDC S Act} {θ : Policy M} {i : S} {rest : List (S × Act)} {j : S}
    {a : Act} (h : histProb θ i ((j, a) :: rest) ≠ 0) : a ∈ M.A j := by
  by_contra ha
  exact prob_ne_zero_of_hp h (θ.prob_supp rest j a ha)

lemma eq_of_hp_stat {M : MDC S Act} (e : StationaryPolicy M) {i : S} {rest : List (S × Act)}
    {j : S} {a : Act} (h : histProb e.toPolicy i ((j, a) :: rest) ≠ 0) : a = e.f j := by
  have := prob_ne_zero_of_hp h
  by_contra hne; apply this; simp [StationaryPolicy.toPolicy, hne]

/-- next-state formula. -/
lemma ExL_next {M : MDC S Act} (θ : Policy M) (i : S) (t : ℕ) (V : S → ℝ≥0∞) :
    ExL θ i (t+2) (onHead fun j _ => V j) =
      ExL θ i (t+1) (onHead fun k b => ∑' j, M.P k b j * V j) := by
  rw [ExL_succ]
  apply ExL_congr
  intro x hx _
  have := inner_sum θ i x V
  simp only [onHead] at this ⊢
  rw [this]
  cases x with
  | nil => simp at hx
  | cons p rest => obtain ⟨k, b⟩ := p; simp [prevWeight, onHead]

/-- The ENNReal drift inequality (subsolution form). -/
lemma drift_sub {M : MDC S Act} (θ : Policy M) (i : S) (Q : S → Act → Prop)
    (hQ : ∀ rest j a, histProb θ i ((j, a) :: rest) ≠ 0 → Q j a)
    (G : ℝ≥0∞) (V : S → ℝ≥0∞) (W : S → Act → ℝ≥0∞)
    (hsub : ∀ j a, Q j a → G + V j ≤ W j a + ∑' k, M.P j a k * V k) (t : ℕ) :
    G + ExL θ i (t+1) (onHead fun j _ => V j) ≤
      ExL θ i (t+1) (onHead W) + ExL θ i (t+2) (onHead fun j _ => V j) := by
  rw [ExL_next, ← ExL_add]
  conv_lhs => rw [← ExL_const θ i (t+1) G, ← ExL_add]
  apply ExL_mono
  intro x hx h0
  cases x with
  | nil => simp at hx
  | cons p rest =>
    obtain ⟨j, a⟩ := p
    simpa [onHead] using hsub j a (hQ rest j a h0)

lemma drift_sup {M : MDC S Act} (θ : Policy M) (i : S) (Q : S → Act → Prop)
    (hQ : ∀ rest j a, histProb θ i ((j, a) :: rest) ≠ 0 → Q j a)
    (G : ℝ≥0∞) (V : S → ℝ≥0∞) (W : S → Act → ℝ≥0∞)
    (hsup : ∀ j a, Q j a → W j a + ∑' k, M.P j a k * V k ≤ G + V j) (t : ℕ) :
    ExL θ i (t+1) (onHead W) + ExL θ i (t+2) (onHead fun j _ => V j) ≤
      G + ExL θ i (t+1) (onHead fun j _ => V j) := by
  rw [ExL_next, ← ExL_add]
  conv_rhs => rw [← ExL_const θ i (t+1) G, ← ExL_add]
  apply ExL_mono
  intro x hx h0
  cases x with
  | nil => simp at hx
  | cons p rest =>
    obtain ⟨j, a⟩ := p
    simpa [onHead] using hsup j a (hQ rest j a h0)

/-! ### real-valued expectations against the kernel -/

lemma P_ne_top (M : MDC S Act) (i : S) (a : Act) (j : S) : M.P i a j ≠ ⊤ :=
  ENNReal.ne_top_of_tsum_ne_top (by rw [M.P_sum]; exact ENNReal.one_ne_top) j

lemma summable_P (M : MDC S Act) (i : S) (a : Act) : Summable fun j => (M.P i a j).toReal :=
  ENNReal.summable_toReal (by rw [M.P_sum]; exact ENNReal.one_ne_top)

lemma tsum_P_toReal (M : MDC S Act) (i : S) (a : Act) : ∑' j, (M.P i a j).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (P_ne_top M i a), M.P_sum]; rfl

lemma summable_Pmul (M : MDC S Act) (i : S) (a : Act) {f : S → ℝ} {B : ℝ}
    (hf : ∀ j, |f j| ≤ B) : Summable fun j => (M.P i a j).toReal * f j := by
  refine Summable.of_norm_bounded (g := fun j => (M.P i a j).toReal * B)
    ((summable_P M i a).mul_right B) ?_
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf j) ENNReal.toReal_nonneg

lemma expNext_add (M : MDC S Act) (i : S) (a : Act) {f g : S → ℝ} {B : ℝ}
    (hf : ∀ j, |f j| ≤ B) (hg : ∀ j, |g j| ≤ B) :
    expNext M i a (fun j => f j + g j) = expNext M i a f + expNext M i a g := by
  unfold expNext
  rw [← (summable_Pmul M i a hf).tsum_add (summable_Pmul M i a hg)]
  congr 1; funext j; ring

lemma expNext_sub (M : MDC S Act) (i : S) (a : Act) {f g : S → ℝ} {B : ℝ}
    (hf : ∀ j, |f j| ≤ B) (hg : ∀ j, |g j| ≤ B) :
    expNext M i a (fun j => f j - g j) = expNext M i a f - expNext M i a g := by
  unfold expNext
  rw [← (summable_Pmul M i a hf).tsum_sub (summable_Pmul M i a hg)]
  congr 1; funext j; ring

lemma expNext_const (M : MDC S Act) (i : S) (a : Act) (c : ℝ) :
    expNext M i a (fun _ => c) = c := by
  unfold expNext
  rw [tsum_mul_right, tsum_P_toReal, one_mul]

lemma expNext_add_const (M : MDC S Act) (i : S) (a : Act) {f : S → ℝ} {B : ℝ}
    (hf : ∀ j, |f j| ≤ B) (c : ℝ) :
    expNext M i a (fun j => f j + c) = expNext M i a f + c := by
  have hc : ∀ j : S, |(fun _ => c) j| ≤ max B |c| := fun _ => le_max_right _ _
  have hf' : ∀ j, |f j| ≤ max B |c| := fun j => (hf j).trans (le_max_left _ _)
  rw [expNext_add M i a hf' hc, expNext_const]

lemma expNext_mono (M : MDC S Act) (i : S) (a : Act) {f g : S → ℝ} {B : ℝ}
    (hf : ∀ j, |f j| ≤ B) (hg : ∀ j, |g j| ≤ B) (hfg : ∀ j, f j ≤ g j) :
    expNext M i a f ≤ expNext M i a g := by
  unfold expNext
  exact (summable_Pmul M i a hf).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (hfg j) ENNReal.toReal_nonneg) (summable_Pmul M i a hg)

lemma abs_expNext_le (M : MDC S Act) (i : S) (a : Act) {f : S → ℝ} {B : ℝ}
    (hf : ∀ j, |f j| ≤ B) : |expNext M i a f| ≤ B := by
  have hB : ∀ j : S, |(fun _ => B) j| ≤ |B| := fun _ => le_rfl
  have hf' : ∀ j, |f j| ≤ |B| := fun j => (hf j).trans (le_abs_self _)
  have hnB : ∀ j : S, |(fun _ => -B) j| ≤ |B| := fun _ => by simp
  rw [abs_le]
  constructor
  · have := expNext_mono M i a hnB hf' (fun j => by linarith [(abs_le.1 (hf j)).1])
    rwa [expNext_const] at this
  · have := expNext_mono M i a hf' hB (fun j => (abs_le.1 (hf j)).2)
    rwa [expNext_const] at this

lemma ofReal_expNext (M : MDC S Act) (i : S) (a : Act) {f : S → ℝ} {B : ℝ}
    (hf : ∀ j, |f j| ≤ B) (hf0 : ∀ j, 0 ≤ f j) :
    ENNReal.ofReal (expNext M i a f) = ∑' j, M.P i a j * ENNReal.ofReal (f j) := by
  unfold expNext
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (hf0 j))
    (summable_Pmul M i a hf)]
  congr 1; funext j
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (P_ne_top M i a j)]

/-! ### the real sum bounds -/

lemma ofReal_split {B x : ℝ} (hx : |x| ≤ B) :
    ENNReal.ofReal x + ENNReal.ofReal B = ENNReal.ofReal (x + B) + ENNReal.ofReal (-x) := by
  have h1 := (abs_le.1 hx).1
  have h2 := (abs_le.1 hx).2
  rcases le_total 0 x with h | h
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -x ≤ 0), add_zero,
      ENNReal.ofReal_add h (by linarith)]
  · rw [ENNReal.ofReal_of_nonpos h, zero_add, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring

/-- shift identity for `expCostR`. -/
lemma expCostR_eq {M : MDC S Act} (θ : Policy M) (w : S → Act → ℝ) (B : ℝ)
    (hw : ∀ j, ∀ a ∈ M.A j, |w j a| ≤ B) (i : S) (t : ℕ) :
    expCostR θ w i t =
      (ExL θ i (t+1) (onHead fun j a => ENNReal.ofReal (w j a + B))).toReal - B ∧
    ExL θ i (t+1) (onHead fun j a => ENNReal.ofReal (w j a + B)) ≤ ENNReal.ofReal (2 * B) := by
  have hsupp : ∀ x : List (S × Act), x.length = t + 1 → histProb θ i x ≠ 0 →
      ∃ j a rest, x = (j, a) :: rest ∧ a ∈ M.A j := by
    intro x hx h0
    cases x with
    | nil => simp at hx
    | cons p rest => obtain ⟨j, a⟩ := p; exact ⟨j, a, rest, rfl, mem_of_hp h0⟩
  have hB0 : 0 ≤ B := by
    obtain ⟨a, ha⟩ := M.A_nonempty i
    exact (abs_nonneg _).trans (hw i a ha)
  set Ep := ExL θ i (t+1) (fun h => ENNReal.ofReal (lastCostR w h)) with hEp
  set En := ExL θ i (t+1) (fun h => ENNReal.ofReal (-lastCostR w h)) with hEn
  set Eb := ExL θ i (t+1) (onHead fun j a => ENNReal.ofReal (w j a + B)) with hEb
  have hdef : expCostR θ w i t = Ep.toReal - En.toReal := rfl
  have hkey : Ep + ENNReal.ofReal B = Eb + En := by
    rw [hEp, hEn, hEb, ← ExL_const θ i (t+1) (ENNReal.ofReal B), ← ExL_add, ← ExL_add]
    apply ExL_congr
    intro x hx h0
    obtain ⟨j, a, rest, rfl, ha⟩ := hsupp x hx h0
    simp only [lastCostR, onHead]
    exact ofReal_split (hw j a ha)
  have hEp_le : Ep ≤ ENNReal.ofReal B := by
    apply ExL_le_const
    intro x hx h0
    obtain ⟨j, a, rest, rfl, ha⟩ := hsupp x hx h0
    simp only [lastCostR]
    exact ENNReal.ofReal_le_ofReal (abs_le.1 (hw j a ha)).2
  have hEn_le : En ≤ ENNReal.ofReal B := by
    apply ExL_le_const
    intro x hx h0
    obtain ⟨j, a, rest, rfl, ha⟩ := hsupp x hx h0
    simp only [lastCostR]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hw j a ha)).1])
  have hEb_le : Eb ≤ ENNReal.ofReal (2 * B) := by
    apply ExL_le_const
    intro x hx h0
    obtain ⟨j, a, rest, rfl, ha⟩ := hsupp x hx h0
    simp only [onHead]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hw j a ha)).2])
  refine ⟨?_, hEb_le⟩
  have hfin : ∀ {X : ℝ≥0∞} {c : ℝ}, X ≤ ENNReal.ofReal c → X ≠ ⊤ :=
    fun h => ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_add (hfin hEp_le) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (hfin hEb_le) (hfin hEn_le), ENNReal.toReal_ofReal hB0] at this
  rw [hdef]; linarith

/-- the real drift sum bound (subsolution ⇒ lower bound). -/
lemma sum_lower {M : MDC S Act} (θ : Policy M) (w : S → Act → ℝ) (v : S → ℝ) (g B : ℝ)
    (hw : ∀ j, ∀ a ∈ M.A j, |w j a| ≤ B) (hv : ∀ j, |v j| ≤ B) (hg : |g| ≤ B) (i : S)
    (Q : S → Act → Prop) (hQ : ∀ rest j a, histProb θ i ((j, a) :: rest) ≠ 0 → Q j a)
    (hQA : ∀ j a, Q j a → a ∈ M.A j)
    (hsub : ∀ j a, Q j a → g + v j ≤ w j a + expNext M j a v) (T : ℕ) :
    ((T : ℝ) + 1) * g - 2 * B ≤ ∑ t ∈ Finset.range (T + 1), expCostR θ w i t := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hg
  have hvB : ∀ j, |v j + B| ≤ 2 * B := fun j => by
    rw [abs_le]; constructor <;> linarith [(abs_le.1 (hv j)).1, (abs_le.1 (hv j)).2]
  have hv0 : ∀ j, 0 ≤ v j + B := fun j => by linarith [(abs_le.1 (hv j)).1]
  set V : S → ℝ≥0∞ := fun j => ENNReal.ofReal (v j + B)
  set W : S → Act → ℝ≥0∞ := fun j a => ENNReal.ofReal (w j a + B)
  have hPV : ∀ j a, ∑' k, M.P j a k * V k = ENNReal.ofReal (expNext M j a v + B) := by
    intro j a
    rw [← expNext_add_const M j a hv B]
    exact (ofReal_expNext M j a hvB hv0).symm
  have hsubE : ∀ j a, Q j a → ENNReal.ofReal (g + B) + V j ≤ W j a + ∑' k, M.P j a k * V k := by
    intro j a hq
    have ha := hQA j a hq
    have hwa := abs_le.1 (hw j a ha)
    have hen := abs_le.1 (abs_expNext_le M j a hv)
    rw [hPV]
    simp only [V, W]
    rw [← ENNReal.ofReal_add (by linarith [(abs_le.1 hg).1]) (hv0 j),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    linarith [hsub j a hq]
  set a : ℕ → ℝ := fun t => (ExL θ i (t+1) (onHead fun j _ => V j)).toReal
  have haE : ∀ t, ExL θ i (t+1) (onHead fun j _ => V j) ≤ ENNReal.ofReal (2 * B) := by
    intro t
    apply ExL_le_const
    intro x _ _
    cases x with
    | nil => simp [onHead]
    | cons p rest => exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hvB p.1)).2])
  have hfin : ∀ {X : ℝ≥0∞} {c : ℝ}, X ≤ ENNReal.ofReal c → X ≠ ⊤ :=
    fun h => ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have ha_bd : ∀ t, 0 ≤ a t ∧ a t ≤ 2 * B := by
    intro t
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (haE t)
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hstep : ∀ t, (g + B) + a t ≤ (expCostR θ w i t + B) + a (t+1) := by
    intro t
    obtain ⟨hc, hcle⟩ := expCostR_eq θ w B hw i t
    have hd := drift_sub θ i Q hQ (ENNReal.ofReal (g + B)) V W hsubE t
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin hcle, hfin (haE (t+1))⟩) hd
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (hfin (haE t)),
      ENNReal.toReal_add (hfin hcle) (hfin (haE (t+1))),
      ENNReal.toReal_ofReal (by linarith [(abs_le.1 hg).1])] at this
    simp only [a]
    rw [hc]; linarith
  have hsum : ∀ T : ℕ, ((T : ℝ) + 1) * (g + B) + a 0 ≤
      ∑ t ∈ Finset.range (T + 1), (expCostR θ w i t + B) + a (T + 1) := by
    intro T
    induction T with
    | zero => simp; linarith [hstep 0]
    | succ T ih =>
      rw [Finset.sum_range_succ]
      push_cast
      linarith [hstep (T+1)]
  have := hsum T
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  push_cast at this
  linarith [ha_bd 0, ha_bd (T+1)]

lemma sum_upper {M : MDC S Act} (θ : Policy M) (w : S → Act → ℝ) (v : S → ℝ) (g B : ℝ)
    (hw : ∀ j, ∀ a ∈ M.A j, |w j a| ≤ B) (hv : ∀ j, |v j| ≤ B) (hg : |g| ≤ B) (i : S)
    (Q : S → Act → Prop) (hQ : ∀ rest j a, histProb θ i ((j, a) :: rest) ≠ 0 → Q j a)
    (hQA : ∀ j a, Q j a → a ∈ M.A j)
    (hsup : ∀ j a, Q j a → w j a + expNext M j a v ≤ g + v j) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), expCostR θ w i t ≤ ((T : ℝ) + 1) * g + 2 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hg
  have hvB : ∀ j, |v j + B| ≤ 2 * B := fun j => by
    rw [abs_le]; constructor <;> linarith [(abs_le.1 (hv j)).1, (abs_le.1 (hv j)).2]
  have hv0 : ∀ j, 0 ≤ v j + B := fun j => by linarith [(abs_le.1 (hv j)).1]
  set V : S → ℝ≥0∞ := fun j => ENNReal.ofReal (v j + B)
  set W : S → Act → ℝ≥0∞ := fun j a => ENNReal.ofReal (w j a + B)
  have hPV : ∀ j a, ∑' k, M.P j a k * V k = ENNReal.ofReal (expNext M j a v + B) := by
    intro j a
    rw [← expNext_add_const M j a hv B]
    exact (ofReal_expNext M j a hvB hv0).symm
  have hsupE : ∀ j a, Q j a → W j a + ∑' k, M.P j a k * V k ≤ ENNReal.ofReal (g + B) + V j := by
    intro j a hq
    have ha := hQA j a hq
    have hwa := abs_le.1 (hw j a ha)
    have hen := abs_le.1 (abs_expNext_le M j a hv)
    rw [hPV]
    simp only [V, W]
    rw [← ENNReal.ofReal_add (by linarith [(abs_le.1 hg).1]) (hv0 j),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    linarith [hsup j a hq]
  set a : ℕ → ℝ := fun t => (ExL θ i (t+1) (onHead fun j _ => V j)).toReal
  have haE : ∀ t, ExL θ i (t+1) (onHead fun j _ => V j) ≤ ENNReal.ofReal (2 * B) := by
    intro t
    apply ExL_le_const
    intro x _ _
    cases x with
    | nil => simp [onHead]
    | cons p rest => exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hvB p.1)).2])
  have hfin : ∀ {X : ℝ≥0∞} {c : ℝ}, X ≤ ENNReal.ofReal c → X ≠ ⊤ :=
    fun h => ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have ha_bd : ∀ t, 0 ≤ a t ∧ a t ≤ 2 * B := by
    intro t
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (haE t)
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hstep : ∀ t, (expCostR θ w i t + B) + a (t+1) ≤ (g + B) + a t := by
    intro t
    obtain ⟨hc, hcle⟩ := expCostR_eq θ w B hw i t
    have hd := drift_sup θ i Q hQ (ENNReal.ofReal (g + B)) V W hsupE t
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hfin (haE t)⟩) hd
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (hfin (haE t)),
      ENNReal.toReal_add (hfin hcle) (hfin (haE (t+1))),
      ENNReal.toReal_ofReal (by linarith [(abs_le.1 hg).1])] at this
    simp only [a]
    rw [hc]; linarith
  have hsum : ∀ T : ℕ, ∑ t ∈ Finset.range (T + 1), (expCostR θ w i t + B) + a (T + 1) ≤
      ((T : ℝ) + 1) * (g + B) + a 0 := by
    intro T
    induction T with
    | zero => simp; linarith [hstep 0]
    | succ T ih =>
      rw [Finset.sum_range_succ]
      push_cast
      linarith [hstep (T+1)]
  have := hsum T
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  push_cast at this
  linarith [ha_bd 0, ha_bd (T+1)]

end DermanAvgAux


namespace DermanAvgAux

variable {S Act : Type} [Countable S]

lemma abs_expCostR_le {M : MDC S Act} (θ : Policy M) (w : S → Act → ℝ) (B : ℝ)
    (hw : ∀ j, ∀ a ∈ M.A j, |w j a| ≤ B) (i : S) (t : ℕ) : |expCostR θ w i t| ≤ B := by
  obtain ⟨h1, h2⟩ := expCostR_eq θ w B hw i t
  have hB0 : 0 ≤ B := by
    obtain ⟨a, ha⟩ := M.A_nonempty i
    exact (abs_nonneg _).trans (hw i a ha)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  rw [h1, abs_le]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := ExL θ i (t+1)
    (onHead fun j a => ENNReal.ofReal (w j a + B)))]

lemma abs_avg_le {M : MDC S Act} (θ : Policy M) (w : S → Act → ℝ) (B : ℝ)
    (hw : ∀ j, ∀ a ∈ M.A j, |w j a| ≤ B) (i : S) (T : ℕ) :
    |((T : ℝ) + 1)⁻¹ * ∑ t ∈ Finset.range (T + 1), expCostR θ w i t| ≤ B := by
  have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.2 hpos), inv_mul_le_iff₀ hpos]
  calc |∑ t ∈ Finset.range (T + 1), expCostR θ w i t|
      ≤ ∑ t ∈ Finset.range (T + 1), |expCostR θ w i t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range (T + 1), B := Finset.sum_le_sum fun t _ => abs_expCostR_le θ w B hw i t
    _ = ((T : ℝ) + 1) * B := by simp

lemma avg_ge {u : ℕ → ℝ} {g C : ℝ} (h : ∀ T : ℕ, ((T : ℝ) + 1) * g - C ≤ u T) (T : ℕ) :
    g - C * (1 / ((T : ℝ) + 1)) ≤ ((T : ℝ) + 1)⁻¹ * u T := by
  have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have : g - C * (1 / ((T : ℝ) + 1)) = ((T : ℝ) + 1)⁻¹ * (((T : ℝ) + 1) * g - C) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (h T) (inv_nonneg.2 hpos.le)

lemma avg_le {u : ℕ → ℝ} {g C : ℝ} (h : ∀ T : ℕ, u T ≤ ((T : ℝ) + 1) * g + C) (T : ℕ) :
    ((T : ℝ) + 1)⁻¹ * u T ≤ g + C * (1 / ((T : ℝ) + 1)) := by
  have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have : g + C * (1 / ((T : ℝ) + 1)) = ((T : ℝ) + 1)⁻¹ * (((T : ℝ) + 1) * g + C) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (h T) (inv_nonneg.2 hpos.le)

lemma tendsto_aux (g C : ℝ) (s : ℝ) :
    Tendsto (fun T : ℕ => g + s * C * (1 / ((T : ℝ) + 1))) atTop (𝓝 g) := by
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (s * C)
  simpa using this.const_add g

lemma le_limsup_aux {u : ℕ → ℝ} {g C B : ℝ} (hlo : ∀ T : ℕ, g - C * (1 / ((T : ℝ) + 1)) ≤ u T)
    (hB : ∀ T, |u T| ≤ B) : g ≤ limsup u atTop := by
  apply le_of_forall_sub_le
  intro ε hε
  have ht := tendsto_aux g C (-1)
  have hev : ∀ᶠ T : ℕ in atTop, g - ε < g + -1 * C * (1 / ((T : ℝ) + 1)) :=
    ht.eventually (lt_mem_nhds (by linarith))
  apply le_limsup_of_frequently_le
  · refine (hev.mono fun T hT => ?_).frequently
    have := hlo T
    linarith
  · exact isBoundedUnder_of ⟨B, fun T => (abs_le.1 (hB T)).2⟩

/-- Core of Theorem 1: a bounded subsolution of (1) bounds every policy's average cost below. -/
lemma avgCost_ge {M : MDC S Act} (w : S → Act → ℝ) (v : S → ℝ) (g B : ℝ)
    (hw : ∀ j, ∀ a ∈ M.A j, |w j a| ≤ B) (hv : ∀ j, |v j| ≤ B) (hg : |g| ≤ B)
    (hsub : ∀ j, ∀ a ∈ M.A j, g + v j ≤ w j a + expNext M j a v) (θ : Policy M) (i : S) :
    g ≤ avgCostR θ w i := by
  have hs := sum_lower θ w v g B hw hv hg i (fun j a => a ∈ M.A j)
    (fun rest j a h => mem_of_hp h) (fun j a h => h) hsub
  exact le_limsup_aux (avg_ge hs) (abs_avg_le θ w B hw i)

/-- Core of (4). -/
lemma avg_tendsto_stat {M : MDC S Act} (w : S → Act → ℝ) (v : S → ℝ) (g B : ℝ)
    (hw : ∀ j, ∀ a ∈ M.A j, |w j a| ≤ B) (hv : ∀ j, |v j| ≤ B) (hg : |g| ≤ B)
    (e : StationaryPolicy M) (hD : IsEvaluation M w e g v) (i : S) :
    Tendsto (fun T : ℕ => ((T : ℝ) + 1)⁻¹ *
          ∑ t ∈ Finset.range (T + 1), expCostR e.toPolicy w i t) atTop (𝓝 g) ∧
        avgCostR e.toPolicy w i = g := by
  have hQ : ∀ rest j a, histProb e.toPolicy i ((j, a) :: rest) ≠ 0 → a = e.f j :=
    fun rest j a h => eq_of_hp_stat e h
  have hQA : ∀ j a, a = e.f j → a ∈ M.A j := fun j a h => h ▸ e.mem j
  have hs1 := sum_lower e.toPolicy w v g B hw hv hg i (fun j a => a = e.f j) hQ hQA
    (fun j a h => by subst h; exact (hD j).le)
  have hs2 := sum_upper e.toPolicy w v g B hw hv hg i (fun j a => a = e.f j) hQ hQA
    (fun j a h => by subst h; exact (hD j).ge)
  have ht : Tendsto (fun T : ℕ => ((T : ℝ) + 1)⁻¹ *
          ∑ t ∈ Finset.range (T + 1), expCostR e.toPolicy w i t) atTop (𝓝 g) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_aux g (2 * B) (-1))
      (tendsto_aux g (2 * B) 1) (fun T => ?_) (fun T => ?_)
    · have := avg_ge hs1 T; simp only at this ⊢; linarith
    · have := avg_le hs2 T; simp only at this ⊢; linarith
  exact ⟨ht, ht.limsup_eq⟩

lemma bound_of_CostBounded {M : MDC S Act} {w : S → Act → ℝ} (hB : CostBounded M w) (B' : ℝ) :
    ∃ B, B' ≤ B ∧ ∀ j, ∀ a ∈ M.A j, |w j a| ≤ B := by
  obtain ⟨B, hB⟩ := hB
  exact ⟨max B B', le_max_right _ _, fun j a ha => (hB j a ha).trans (le_max_left _ _)⟩

theorem theorem1_core (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (g : ℝ) (v : S → ℝ) (hv : BddFun v)
    (h1 : IsACOE M w g v) :
    (∃ e : StationaryPolicy M, IsMinimizer M w v e) ∧
      ∀ e : StationaryPolicy M, IsMinimizer M w v e →
        ∀ i : S, avgCostR e.toPolicy w i = g ∧ ∀ R : Policy M, g ≤ avgCostR R w i := by
  obtain ⟨Bv, hBv⟩ := hv
  obtain ⟨B, hBB, hw⟩ := bound_of_CostBounded hB (max Bv |g|)
  have hvB : ∀ j, |v j| ≤ B := fun j => (hBv j).trans ((le_max_left _ _).trans hBB)
  have hgB : |g| ≤ B := (le_max_right _ _).trans hBB
  refine ⟨?_, ?_⟩
  · have hex : ∀ i, ∃ a ∈ M.A i, ∀ b ∈ M.A i,
        w i a + expNext M i a v ≤ w i b + expNext M i b v := fun i =>
      (M.A i).exists_min_image (fun a => w i a + expNext M i a v) (M.A_nonempty i)
    choose f hf hmin using hex
    exact ⟨⟨f, hf⟩, fun i a ha => hmin i a ha⟩
  · intro e he i
    have hD : IsEvaluation M w e g v := by
      intro j
      obtain ⟨⟨a, ha, heq⟩, hle⟩ := h1 j
      exact le_antisymm (hle _ (e.mem j)) ((he j a ha).trans heq.ge)
    exact ⟨(avg_tendsto_stat w v g B hw hvB hgB e hD i).2,
      fun R => avgCost_ge w v g B hw hvB hgB (fun j a ha => (h1 j).2 a ha) R i⟩

theorem eq4_core (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (e : StationaryPolicy M) (g : ℝ) (v : S → ℝ)
    (hv : BddFun v) (hD : IsEvaluation M w e g v) :
    ∀ i : S,
      Tendsto (fun T : ℕ => ((T : ℝ) + 1)⁻¹ *
          ∑ t ∈ Finset.range (T + 1), expCostR e.toPolicy w i t) atTop (𝓝 g) ∧
        avgCostR e.toPolicy w i = g := by
  obtain ⟨Bv, hBv⟩ := hv
  obtain ⟨B, hBB, hw⟩ := bound_of_CostBounded hB (max Bv |g|)
  have hvB : ∀ j, |v j| ≤ B := fun j => (hBv j).trans ((le_max_left _ _).trans hBB)
  have hgB : |g| ≤ B := (le_max_right _ _).trans hBB
  exact fun i => avg_tendsto_stat w v g B hw hvB hgB e hD i

end DermanAvgAux


namespace DermanAvgAux

variable {S Act : Type} [Countable S]

open SennottDP.MarkovCost in
lemma nStep_succ' (M : MDC S Act) (e : StationaryPolicy M) (t : ℕ) (i j : S) :
    nStep (chainOf M e) (t+1) i j = ∑' k, nStep (chainOf M e) t i k * M.P k (e.f k) j := rfl

open SennottDP.MarkovCost in
lemma nStep_sum (M : MDC S Act) (e : StationaryPolicy M) (t : ℕ) (i : S) :
    ∑' j, nStep (chainOf M e) t i j = 1 := by
  induction t with
  | zero =>
    simp only [nStep]
    rw [tsum_eq_single i (fun j hj => by simp [Ne.symm hj])]; simp
  | succ t ih =>
    simp_rw [nStep_succ']
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, M.P_sum, mul_one]
    exact ih

open SennottDP.MarkovCost in
lemma nStep_push (M : MDC S Act) (e : StationaryPolicy M) (t : ℕ) (i : S) (X : S → ℝ≥0∞) :
    ∑' k, nStep (chainOf M e) t i k * ∑' j, M.P k (e.f k) j * X j =
      ∑' j, nStep (chainOf M e) (t+1) i j * X j := by
  simp_rw [nStep_succ', ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1; funext j; congr 1; funext k; ring

open SennottDP.MarkovCost in
lemma wsum_le (M : MDC S Act) (e : StationaryPolicy M) (t : ℕ) (i : S) {X : S → ℝ≥0∞}
    (c : ℝ≥0∞) (h : ∀ k, X k ≤ c) : ∑' k, nStep (chainOf M e) t i k * X k ≤ c := by
  calc ∑' k, nStep (chainOf M e) t i k * X k ≤ ∑' k, nStep (chainOf M e) t i k * c :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul_right (h k) _
    _ = c := by rw [ENNReal.tsum_mul_right, nStep_sum, one_mul]

open SennottDP.MarkovCost in
/-- The Cesàro estimate behind Lemma 2. -/
lemma cesaro_bound (M : MDC S Act) (e : StationaryPolicy M) (D ε : S → ℝ) (c Bd Be : ℝ)
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ Bd) (hε0 : ∀ k, 0 ≤ ε k) (hεB : ∀ k, ε k ≤ Be)
    (heq : ∀ k, D k + c = ε k + expNext M k (e.f k) D) (i j : S) (T : ℕ) :
    ((T : ℝ) + 1) * cesaro M e i j T * ε j ≤ ((T : ℝ) + 1) * c + Bd := by
  have hDabs : ∀ k, |D k| ≤ Bd := fun k => abs_le.2 ⟨by linarith [hD0 k, hD k], hD k⟩
  set μ := fun t k => nStep (chainOf M e) t i k
  set m : ℕ → ℝ := fun t => (∑' k, μ t k * ENNReal.ofReal (D k)).toReal
  set E : ℕ → ℝ := fun t => (∑' k, μ t k * ENNReal.ofReal (ε k)).toReal
  have hmE : ∀ t, ∑' k, μ t k * ENNReal.ofReal (D k) ≤ ENNReal.ofReal Bd :=
    fun t => wsum_le M e t i _ fun k => ENNReal.ofReal_le_ofReal (hD k)
  have hEE : ∀ t, ∑' k, μ t k * ENNReal.ofReal (ε k) ≤ ENNReal.ofReal Be :=
    fun t => wsum_le M e t i _ fun k => ENNReal.ofReal_le_ofReal (hεB k)
  have hfin : ∀ {X : ℝ≥0∞} {c : ℝ}, X ≤ ENNReal.ofReal c → X ≠ ⊤ :=
    fun h => ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hBd0 : 0 ≤ Bd := (hD0 j).trans (hD j)
  have hm_bd : ∀ t, 0 ≤ m t ∧ m t ≤ Bd := by
    intro t
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmE t)
    rwa [ENNReal.toReal_ofReal hBd0] at this
  have hLD0 : ∀ k, 0 ≤ expNext M k (e.f k) D := by
    intro k
    have h0 : ∀ j : S, |(fun _ => (0:ℝ)) j| ≤ Bd := fun _ => by simpa using hBd0
    have := expNext_mono M k (e.f k) h0 hDabs (fun j => hD0 j)
    rwa [expNext_const] at this
  -- pointwise ENNReal identity
  have hpt : ∀ k, ENNReal.ofReal (D k) + ENNReal.ofReal (max c 0) =
      ENNReal.ofReal (ε k) + ∑' j, M.P k (e.f k) j * ENNReal.ofReal (D j) +
        ENNReal.ofReal (max (-c) 0) := by
    intro k
    rw [← ofReal_expNext M k (e.f k) hDabs hD0,
      ← ENNReal.ofReal_add (hD0 k) (le_max_right _ _),
      ← ENNReal.ofReal_add (hε0 k) (hLD0 k),
      ← ENNReal.ofReal_add (by linarith [hε0 k, hLD0 k]) (le_max_right _ _)]
    congr 1
    have := heq k
    rcases le_total 0 c with hc | hc
    · rw [max_eq_left hc, max_eq_right (by linarith)]; linarith
    · rw [max_eq_right hc, max_eq_left (by linarith)]; linarith
  have hstep : ∀ t, m t + c = E t + m (t+1) := by
    intro t
    have hE : ∑' k, μ t k * (ENNReal.ofReal (D k) + ENNReal.ofReal (max c 0)) =
        ∑' k, μ t k * (ENNReal.ofReal (ε k) + ∑' j, M.P k (e.f k) j * ENNReal.ofReal (D j) +
          ENNReal.ofReal (max (-c) 0)) := by
      congr 1; funext k; rw [hpt k]
    simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right] at hE
    rw [nStep_sum] at hE
    simp only [μ] at hE
    rw [nStep_push] at hE
    simp only [one_mul] at hE
    have := congrArg ENNReal.toReal hE
    rw [ENNReal.toReal_add (hfin (hmE t)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfin (hEE t), hfin (hmE (t+1))⟩)
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_add (hfin (hEE t)) (hfin (hmE (t+1))),
      ENNReal.toReal_ofReal (le_max_right _ _), ENNReal.toReal_ofReal (le_max_right _ _)] at this
    simp only [m, E, μ]
    have hmx : max c 0 - max (-c) 0 = c := by
      rcases le_total 0 c with hc | hc
      · rw [max_eq_left hc, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hc, max_eq_left (by linarith)]; ring
    linarith
  have hsum : ∀ T : ℕ, ∑ t ∈ Finset.range (T + 1), E t = m 0 - m (T+1) + ((T : ℝ) + 1) * c := by
    intro T
    induction T with
    | zero => simp; linarith [hstep 0]
    | succ T ih =>
      rw [Finset.sum_range_succ, ih]; push_cast; linarith [hstep (T+1)]
  have hEj : ∀ t, (μ t j).toReal * ε j ≤ E t := by
    intro t
    have h1 : μ t j * ENNReal.ofReal (ε j) ≤ ∑' k, μ t k * ENNReal.ofReal (ε k) :=
      ENNReal.le_tsum (f := fun k => μ t k * ENNReal.ofReal (ε k)) j
    have := ENNReal.toReal_mono (hfin (hEE t)) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hε0 j)] at this
  have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hces : ((T : ℝ) + 1) * cesaro M e i j T =
      ∑ t ∈ Finset.range (T + 1), (μ t j).toReal := by
    unfold cesaro; field_simp; rfl
  rw [hces, Finset.sum_mul]
  calc ∑ t ∈ Finset.range (T + 1), (μ t j).toReal * ε j ≤ ∑ t ∈ Finset.range (T + 1), E t :=
        Finset.sum_le_sum fun t _ => hEj t
    _ ≤ _ := by rw [hsum T]; linarith [hm_bd 0, hm_bd (T+1)]

/-- One policy-improvement step: `0 ≤ ε_j` and `δ_j ε_j ≤ g_n - g_{n+1}`. -/
lemma pi_step (M : MDC S Act) (w : S → Act → ℝ) (B : ℝ) (hw : ∀ j, ∀ a ∈ M.A j, |w j a| ≤ B)
    (gR : StationaryPolicy M → ℝ) (vR : StationaryPolicy M → S → ℝ)
    (hEv : ∀ e, IsEvaluation M w e (gR e) (vR e)) (hb : ∀ e, |gR e| ≤ B ∧ ∀ j, |vR e j| ≤ B)
    (hF : CondF M) (e0 e1 : StationaryPolicy M) (hmin : IsMinimizer M w (vR e0) e1) (j : S) :
    0 ≤ gap M w gR vR e0 e1 j ∧
      ∀ δ : ℝ, (∀ (e : StationaryPolicy M) (i : S),
        ∃ π : ℝ, Tendsto (cesaro M e i j) atTop (𝓝 π) ∧ δ ≤ π) →
        δ * gap M w gR vR e0 e1 j ≤ gR e0 - gR e1 := by
  have hv0 := (hb e0).2
  have hv1 := (hb e1).2
  have hg0 := abs_le.1 (hb e0).1
  have hg1 := abs_le.1 (hb e1).1
  have hgap0 : ∀ k, 0 ≤ gap M w gR vR e0 e1 k := by
    intro k
    unfold gap
    have := hmin k (e0.f k) (e0.mem k)
    have h := hEv e0 k
    linarith
  refine ⟨hgap0 j, ?_⟩
  intro δ hπ
  obtain ⟨π, hπt, hδπ⟩ := hπ e1 j
  set c := gR e0 - gR e1
  set D : S → ℝ := fun k => vR e0 k - vR e1 k + 2 * B
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb e0).1
  have hdiff : ∀ k, |vR e0 k - vR e1 k| ≤ 2 * B := fun k => by
    rw [abs_le]; constructor <;> linarith [abs_le.1 (hv0 k), abs_le.1 (hv1 k)]
  have hD0 : ∀ k, 0 ≤ D k := fun k => by simp only [D]; linarith [(abs_le.1 (hdiff k)).1]
  have hD : ∀ k, D k ≤ 4 * B := fun k => by simp only [D]; linarith [(abs_le.1 (hdiff k)).2]
  have hεB : ∀ k, gap M w gR vR e0 e1 k ≤ 4 * B := by
    intro k; unfold gap
    have := abs_le.1 (hw k (e1.f k) (e1.mem k))
    have := abs_le.1 (abs_expNext_le M k (e1.f k) hv0)
    linarith [abs_le.1 (hv0 k)]
  have heq : ∀ k, D k + c = gap M w gR vR e0 e1 k + expNext M k (e1.f k) D := by
    intro k
    have h1 : expNext M k (e1.f k) D =
        expNext M k (e1.f k) (vR e0) - expNext M k (e1.f k) (vR e1) + 2 * B := by
      simp only [D]
      rw [expNext_add_const M k (e1.f k) hdiff, expNext_sub M k (e1.f k) hv0 hv1]
    rw [h1]
    have h2 := hEv e1 k
    unfold gap
    simp only [D, c]
    linarith
  have hbd := cesaro_bound M e1 D (gap M w gR vR e0 e1) c (4 * B) (4 * B) hD0 hD hgap0 hεB heq j j
  -- pass to the limit
  have hlim : π * gap M w gR vR e0 e1 j ≤ c := by
    have hL : Tendsto (fun T : ℕ => cesaro M e1 j j T * gap M w gR vR e0 e1 j) atTop
        (𝓝 (π * gap M w gR vR e0 e1 j)) := hπt.mul_const _
    have hR : Tendsto (fun T : ℕ => c + 1 * (4 * B) * (1 / ((T : ℝ) + 1))) atTop (𝓝 c) :=
      tendsto_aux c (4 * B) 1
    refine le_of_tendsto_of_tendsto' hL hR fun T => ?_
    have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have := hbd T
    have h' : cesaro M e1 j j T * gap M w gR vR e0 e1 j ≤
        ((T : ℝ) + 1)⁻¹ * (((T : ℝ) + 1) * c + 4 * B) := by
      rw [le_inv_mul_iff₀ hpos]; linarith
    calc _ ≤ ((T : ℝ) + 1)⁻¹ * (((T : ℝ) + 1) * c + 4 * B) := h'
      _ = c + 1 * (4 * B) * (1 / ((T : ℝ) + 1)) := by field_simp
  calc δ * gap M w gR vR e0 e1 j ≤ π * gap M w gR vR e0 e1 j :=
        mul_le_mul_of_nonneg_right hδπ (hgap0 j)
    _ ≤ c := hlim

lemma setup_bounds (M : MDC S Act) (w : S → Act → ℝ) (hB : CostBounded M w)
    (gR : StationaryPolicy M → ℝ) (vR : StationaryPolicy M → S → ℝ)
    (hE : IsUniformEvaluation M w gR vR) :
    ∃ B, (∀ j, ∀ a ∈ M.A j, |w j a| ≤ B) ∧ ∀ e, |gR e| ≤ B ∧ ∀ j, |vR e j| ≤ B := by
  obtain ⟨_, B1, hB1⟩ := hE
  obtain ⟨B, hBB, hw⟩ := bound_of_CostBounded hB B1
  exact ⟨B, hw, fun e => ⟨(hB1 e).1.trans hBB, fun j => ((hB1 e).2 j).trans hBB⟩⟩

/-- `g^{R_n}` is antitone, converges, and `ε^{R_n} → 0`. -/
lemma pi_chain (M : MDC S Act) (w : S → Act → ℝ) (hB : CostBounded M w)
    (gR : StationaryPolicy M → ℝ) (vR : StationaryPolicy M → S → ℝ)
    (hE : IsUniformEvaluation M w gR vR) (hF : CondF M)
    (R : ℕ → StationaryPolicy M) (hR : IsPISequence M w vR R) :
    (Nonempty S → ∃ gs, Tendsto (fun n => gR (R n)) atTop (𝓝 gs)) ∧
    ∀ i : S, Tendsto (fun n : ℕ => gap M w gR vR (R n) (R (n + 1)) i) atTop (𝓝 0) := by
  obtain ⟨B, hw, hb⟩ := setup_bounds M w hB gR vR hE
  have hstep := fun n j => pi_step M w B hw gR vR hE.1 hb hF (R n) (R (n+1)) (hR n) j
  have hanti_of : ∀ j : S, Antitone (fun n => gR (R n)) := by
    intro j
    apply antitone_nat_of_succ_le
    intro n
    obtain ⟨δ, hδ, hπ⟩ := hF j
    obtain ⟨h0, h1⟩ := hstep n j
    have := h1 δ hπ
    have : 0 ≤ δ * gap M w gR vR (R n) (R (n+1)) j := mul_nonneg hδ.le h0
    linarith
  have hbdd : BddBelow (Set.range fun n => gR (R n)) :=
    ⟨-B, by rintro _ ⟨n, rfl⟩; exact (abs_le.1 (hb (R n)).1).1⟩
  have hconv : ∀ j : S, ∃ gs, Tendsto (fun n => gR (R n)) atTop (𝓝 gs) :=
    fun j => ⟨_, tendsto_atTop_ciInf (hanti_of j) hbdd⟩
  refine ⟨fun ⟨j⟩ => hconv j, fun i => ?_⟩
  obtain ⟨gs, hgs⟩ := hconv i
  obtain ⟨δ, hδ, hπ⟩ := hF i
  have hc : Tendsto (fun n => (gR (R n) - gR (R (n+1))) / δ) atTop (𝓝 0) := by
    have := (hgs.sub (hgs.comp (tendsto_add_atTop_nat 1))).div_const δ
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun n => (hstep n i).1) (fun n => ?_)
  rw [le_div_iff₀ hδ, mul_comm]
  exact (hstep n i).2 δ hπ

theorem lemma2_core (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (hC : CondC M) (gR : StationaryPolicy M → ℝ)
    (vR : StationaryPolicy M → S → ℝ) (hE : IsUniformEvaluation M w gR vR) (hF : CondF M)
    (R : ℕ → StationaryPolicy M) (hR : IsPISequence M w vR R) :
    ∀ i : S, Tendsto (fun n : ℕ => gap M w gR vR (R n) (R (n + 1)) i) atTop (𝓝 0) :=
  (pi_chain M w hB gR vR hE hF R hR).2

end DermanAvgAux


namespace DermanAvgAux

variable {S Act : Type} [Countable S]

lemma exists_limitPoint (M : MDC S Act) (R : ℕ → StationaryPolicy M) :
    ∃ e, IsLimitPoint R e := by
  letI : ∀ i, TopologicalSpace {a // a ∈ M.A i} := fun _ => ⊥
  haveI : ∀ i, DiscreteTopology {a // a ∈ M.A i} := fun _ => ⟨rfl⟩
  let x : ℕ → (∀ i, {a // a ∈ M.A i}) := fun n i => ⟨(R n).f i, (R n).mem i⟩
  obtain ⟨y, φ, hφ, hy⟩ := SeqCompactSpace.tendsto_subseq x
  refine ⟨⟨fun i => (y i).1, fun i => (y i).2⟩, φ, hφ, fun i => ?_⟩
  have := ((continuous_apply i).tendsto y).comp hy
  rw [nhds_discrete, tendsto_pure] at this
  filter_upwards [this] with k hk
  exact congrArg Subtype.val hk

lemma exists_subseq_fun (u : ℕ → S → ℝ) (B : ℝ) (hu : ∀ n j, |u n j| ≤ B) :
    ∃ v : S → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ j, Tendsto (fun k => u (φ k) j) atTop (𝓝 (v j))) ∧ ∀ j, |v j| ≤ B := by
  have hK : IsCompact (Set.pi Set.univ fun _ : S => Set.Icc (-B) B) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨v, hv, φ, hφ, ht⟩ := hK.tendsto_subseq (x := u)
    (fun n => by
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
      intro j; exact abs_le.1 (hu n j))
  refine ⟨v, φ, hφ, fun j => ((continuous_apply j).tendsto v).comp ht, fun j => ?_⟩
  exact abs_le.2 (hv j (Set.mem_univ _))

lemma tendsto_expNext (M : MDC S Act) (i : S) (a : Act) {u : ℕ → S → ℝ} {v : S → ℝ} {B : ℝ}
    (hu : ∀ n j, |u n j| ≤ B) (ht : ∀ j, Tendsto (fun n => u n j) atTop (𝓝 (v j))) :
    Tendsto (fun n => expNext M i a (u n)) atTop (𝓝 (expNext M i a v)) := by
  unfold expNext
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => (M.P i a j).toReal * B)
    ((summable_P M i a).mul_right B) (fun j => (ht j).const_mul _)
    (Eventually.of_forall fun n j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hu n j) ENNReal.toReal_nonneg

theorem theorem4_core (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (hC : CondC M) (gR : StationaryPolicy M → ℝ)
    (vR : StationaryPolicy M → S → ℝ) (hE : IsUniformEvaluation M w gR vR) (hF : CondF M)
    (R : ℕ → StationaryPolicy M) (hR : IsPISequence M w vR R) :
    (∃ e : StationaryPolicy M, IsLimitPoint R e) ∧
      ∀ e : StationaryPolicy M, IsLimitPoint R e →
        OptimalOverC w e.toPolicy ∧
          ∀ i : S, Tendsto (fun n : ℕ => gR (R n)) atTop (𝓝 (avgCostR e.toPolicy w i)) := by
  obtain ⟨B, hw, hb⟩ := setup_bounds M w hB gR vR hE
  obtain ⟨hg, hgap⟩ := pi_chain M w hB gR vR hE hF R hR
  refine ⟨exists_limitPoint M R, fun e he => ?_⟩
  obtain ⟨r, hr, hre⟩ := he
  by_cases hS : Nonempty S
  swap
  · have hS' : IsEmpty S := not_nonempty_iff.1 hS
    exact ⟨fun _ i => (hS'.false i).elim, fun i => (hS'.false i).elim⟩
  obtain ⟨gs, hgs⟩ := hg hS
  set m : ℕ → ℕ := fun k => r (k+1) - 1 with hm
  have hm1 : ∀ k, m k + 1 = r (k+1) := fun k => by
    have := hr.id_le (k+1); simp only [hm, id] at this ⊢; omega
  have hmT : Tendsto m atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    have := hr.id_le (k+1); simp only [hm, id] at this ⊢; omega
  obtain ⟨vs, φ, hφ, hvt, hvs⟩ :=
    exists_subseq_fun (fun k => vR (R (m k))) B (fun n j => (hb _).2 j)
  set n : ℕ → ℕ := fun k => m (φ k) with hn
  have hnT : Tendsto n atTop atTop := hmT.comp hφ.tendsto_atTop
  have hgn : Tendsto (fun k => gR (R (n k))) atTop (𝓝 gs) := hgs.comp hnT
  have hvt' : ∀ j, Tendsto (fun k => vR (R (n k)) j) atTop (𝓝 (vs j)) := hvt
  have hev : ∀ i, ∀ᶠ k in atTop, (R (n k + 1)).f i = e.f i := by
    intro i
    have h1 : Tendsto (fun k => φ k + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
    filter_upwards [h1.eventually (hre i)] with k hk
    simp only [hn]; rw [hm1]; exact hk
  have hEN : ∀ i a, Tendsto (fun k => expNext M i a (vR (R (n k)))) atTop
      (𝓝 (expNext M i a vs)) := fun i a =>
    tendsto_expNext M i a (fun k j => (hb (R (n k))).2 j) hvt'
  have hEq : ∀ i, gs + vs i = w i (e.f i) + expNext M i (e.f i) vs := by
    intro i
    have h0 := (hgap i).comp hnT
    have h1 : Tendsto (fun k => gR (R (n k)) + vR (R (n k)) i -
        (w i (e.f i) + expNext M i (e.f i) (vR (R (n k))))) atTop
        (𝓝 (gs + vs i - (w i (e.f i) + expNext M i (e.f i) vs))) :=
      (hgn.add (hvt' i)).sub (tendsto_const_nhds.add (hEN i (e.f i)))
    have h2 : Tendsto (fun k => gR (R (n k)) + vR (R (n k)) i -
        (w i (e.f i) + expNext M i (e.f i) (vR (R (n k))))) atTop (𝓝 0) := by
      refine h0.congr' ?_
      filter_upwards [hev i] with k hk
      simp only [Function.comp, gap, hk]
    have := tendsto_nhds_unique h1 h2
    linarith
  have hMin : ∀ i, ∀ a ∈ M.A i, w i (e.f i) + expNext M i (e.f i) vs ≤ w i a + expNext M i a vs := by
    intro i a ha
    refine le_of_tendsto_of_tendsto (tendsto_const_nhds.add (hEN i (e.f i)))
      (tendsto_const_nhds.add (hEN i a)) ?_
    filter_upwards [hev i] with k hk
    have := hR (n k) i a ha
    rw [hk] at this
    exact this
  have hACOE : IsACOE M w gs vs := fun i =>
    ⟨⟨e.f i, e.mem i, hEq i⟩, fun a ha => (hEq i).trans_le (hMin i a ha)⟩
  have hT1 := (theorem1_core M w hB gs vs ⟨B, hvs⟩ hACOE).2 e hMin
  refine ⟨fun R' i => ?_, fun i => ?_⟩
  · rw [(hT1 i).1]; exact (hT1 i).2 R'
  · rw [(hT1 i).1]; exact hgs

end DermanAvgAux


theorem solution {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (hC : CondC M) (gR : StationaryPolicy M → ℝ)
    (vR : StationaryPolicy M → S → ℝ) (hE : IsUniformEvaluation M w gR vR) (hF : CondF M)
    (R : ℕ → StationaryPolicy M) (hR : IsPISequence M w vR R) :
    ∀ i : S, Tendsto (fun n : ℕ => gap M w gR vR (R n) (R (n + 1)) i) atTop (𝓝 0) :=
  DermanAvgAux.lemma2_core M w hB hC gR vR hE hF R hR
