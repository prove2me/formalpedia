-- Prove2me | solution 1 for G26G.ref_block_alg
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:31:31.475338+00:00
-- url     : https://prove2.me/submissions/7fb9502d-0384-4d09-97b4-dd815279ef90

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_IAFTRL_lemma_G_12
import Theorems.Thm_IAFTRL_lemma_J_4

-- ===== Solutions.G2.Run =====

/-! ### Basic facts about GIA-FTRL runs -/

open MeasureTheory ProbabilityTheory Set IAFTRL
open scoped ENNReal

namespace G2R

variable {d : ℕ}

/-! #### Geometry -/

/-! #### Runs -/

section Run

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma feas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsFeasible3_6 ℬ e (t + 1) (R.cumEst t ω) (R.p t ω) :=
  ((hR t ht).2.1.2 ω).1

lemma p_supp (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    R.p t ω (Kset ℬ)ᶜ = 0 :=
  (feas hR ht ω).2.1

end Run

/-! #### Deterministic range bounds -/

lemma gB_pos : 0 < gB d := by unfold gB; positivity

section Bounds

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

end Bounds

end G2R


-- ===== Solutions.G26.Freeze =====

/-! ### Freezing an affine field at a predictable stopping rule -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma survS_anti (A : ℕ → Set Ω) {m n : ℕ} (h : m ≤ n) : survS A n ⊆ survS A m := by
  intro ω hω
  simp only [survS, Set.mem_iInter, Finset.mem_range] at hω ⊢
  exact fun i hi => hω i (by omega)

/-- on the surviving set the frozen field is the field -/
lemma frz_eq {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) :
    ∀ n ω, (n = 0 ∨ ω ∈ survS A (n - 1)) → frz X A n ω = X n ω := by
  intro n ω h
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Nat.add_sub_cancel] at h
    rcases h with h | h
    · omega
    · simp only [frz, if_pos h]

lemma frz_succ_of_notMem {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {n : ℕ} {ω : Ω}
    (h : ω ∉ survS A n) : frz X A (n + 1) ω = frz X A n ω := by
  simp only [frz, if_neg h]

/-- once frozen at the first failure `i`, the field stays at its value at `i` -/
lemma frz_stop {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {i : ℕ} {ω : Ω}
    (hi : i = 0 ∨ ω ∈ survS A (i - 1)) (hfail : ω ∉ A i) :
    ∀ N, i ≤ N → frz X A N ω = X i ω := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact frz_eq X A i ω hi
  | succ N hiN ih =>
    have hnot : ω ∉ survS A N := by
      intro h
      have := survS_anti A hiN h
      simp only [survS, Set.mem_iInter, Finset.mem_range] at this
      exact hfail (this i (by omega))
    rw [frz_succ_of_notMem X A hnot, ih]

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end

end G26


-- ===== Solutions.G26.NegRec =====

/-! ### The negative integral moment recurrence (Lemmas G.24, G.25) -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma neg_fz (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : Fin d → ℝ) :
    -fz V c n ω u = u ⬝ᵥ (-V n ω) + (-c n ω) := by
  unfold fz; rw [dotProduct_neg]; ring

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma vneg_lt (k : ℕ) (hk : 2 ≤ k) (B : ℝ) (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) :
    1 + 1024 * (4 * k : ℝ) ^ 2 / B < 3 * k := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := by nlinarith
  have : 1024 * (4 * k : ℝ) ^ 2 / B ≤ k := by
    rw [div_le_iff₀ hB0]; nlinarith
  linarith

end G26


-- ===== Solutions.G26.SIFreeze =====

/-! ### Freezing a scalar interface at a predictable success rule (Lemma G.29, (G.653)–(G.659)) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

open Classical in
/-- the freezing index: the first failure of the rule before `n`, or `n` -/
noncomputable def fidx (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℕ :=
  if h : ∃ i, i < n ∧ ω ∉ A i then Nat.find h else n

lemma frz_fidx {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    frz X A n ω = X (fidx A n ω) ω ∧ fidx A n ω ≤ n ∧
      (fidx A n ω = n ∨ ω ∉ A (fidx A n ω)) ∧ ∀ j < fidx A n ω, ω ∈ A j := by
  classical
  unfold fidx
  split_ifs with h
  · have hspec := Nat.find_spec h
    have hmin : ∀ j < Nat.find h, ω ∈ A j := fun j hj => by
      by_contra hj'
      exact Nat.find_min h hj ⟨by have := hspec.1; omega, hj'⟩
    have hsurv : Nat.find h = 0 ∨ ω ∈ survS A (Nat.find h - 1) := by
      rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
      · exact Or.inl h0
      · right
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj; exact hmin j (by omega)
    exact ⟨frz_stop X A hsurv hspec.2 n hspec.1.le, hspec.1.le, Or.inr hspec.2, hmin⟩
  · push Not at h
    have hs : n = 0 ∨ ω ∈ survS A (n - 1) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact Or.inl h0
      · right
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj; exact h j (by omega)
    exact ⟨frz_eq X A n ω hs, le_rfl, Or.inl rfl, fun j hj => h j hj⟩

lemma frz_before {E : Type*} (X : ℕ → Ω → E) {A : ℕ → Set Ω} {u : ℕ} (hA : ∀ n < u, A n = univ) :
    frz X A u = X u := by
  funext ω
  refine frz_eq X A u ω ?_
  rcases Nat.eq_zero_or_pos u with h | h
  · exact Or.inl h
  · right
    simp only [survS, Set.mem_iInter, Finset.mem_range]
    intro j hj; rw [hA j (by omega)]; trivial

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

end G26

namespace G26

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

end G26


-- ===== Solutions.G26.RunEnv =====

/-! ### Envelopes of the run fields: absolute maxima and block crossings (Lemmas G.15, G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26

variable {d : ℕ} {Ω : Type*}

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma kk_facts (d : ℕ) : 2 ≤ kk d ∧ 4 ≤ 4 * kk d ∧ Even (4 * kk d) ∧ d ≤ 4 * kk d ∧
    2 ^ 20 * ((4 * kk d : ℕ) : ℝ) ≤ gB d := by
  unfold kk gB
  refine ⟨by omega, by omega, ⟨2 * (1024 * (d + 1)), by ring⟩, by omega, ?_⟩
  push_cast; nlinarith

lemma cK_nonneg (d : ℕ) : 0 ≤ cK d := by
  unfold cK Cabs; positivity

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.Params =====

/-! ### Thresholds: buffers `τ_s = (s+1)^{7/8} + 4z` and logarithmic gap cutoffs -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

lemma p78_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x ^ ((7 : ℝ) / 8) :=
  Real.one_le_rpow hx (by norm_num)

lemma tauB_ge {z : ℝ} (hz : 0 ≤ z) (s : ℕ) :
    ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) ≤ tauB z s ∧ 4 * z ≤ tauB z s ∧ 1 ≤ tauB z s := by
  unfold tauB
  have h1 := p78_ge_one (x := (s : ℝ) + 1) (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  refine ⟨by linarith, ?_, by linarith⟩
  have : 0 ≤ ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) := by positivity
  linarith

lemma tauB_pos {z : ℝ} (hz : 0 ≤ z) (s : ℕ) : 0 < tauB z s := by
  linarith [(tauB_ge hz s).2.2]

lemma root8_pow {x : ℝ} (hx : 0 ≤ x) : root8 x ^ 8 = x := by
  unfold root8
  have h1 : Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt (Real.sqrt x) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  calc Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 8 =
      ((Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2) ^ 2) ^ 2 := by ring
    _ = x := by rw [h1, h2, h3]

lemma root8_nonneg (x : ℝ) : 0 ≤ root8 x := Real.sqrt_nonneg _

lemma root8_mono {x y : ℝ} (hxy : x ≤ y) : root8 x ≤ root8 y := by
  unfold root8
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy))

lemma le_root8 {x a : ℝ} (ha : 0 ≤ a) (h : a ^ 8 ≤ x) : a ≤ root8 x := by
  have hx : 0 ≤ x := le_trans (by positivity) h
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt (root8_nonneg x) (by norm_num : (8 : ℕ) ≠ 0)
  rw [root8_pow hx] at this
  linarith

end G26G

namespace G26G

lemma root8_eq_rpow {x : ℝ} (hx : 0 ≤ x) : root8 x = x ^ ((1 : ℝ) / 8) := by
  have h1 : (x ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  have h2 := root8_pow hx
  have hn1 : 0 ≤ x ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hx _
  exact (pow_left_inj₀ (root8_nonneg x) hn1 (by norm_num : (8 : ℕ) ≠ 0)).1 (h2.trans h1.symm)

lemma rpow78_eq {x : ℝ} (hx : 0 ≤ x) : x ^ ((7 : ℝ) / 8) = root8 x ^ 7 := by
  rw [root8_eq_rpow hx, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma one_le_root8 {x : ℝ} (hx : 1 ≤ x) : 1 ≤ root8 x :=
  le_root8 zero_le_one (by simpa using hx)

end G26G


-- ===== Solutions.G26.RefBlock =====

/-! ### Uniform reference control on a block (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma add_pow_le_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x + y) ^ n ≤ 2 ^ n * (x ^ n + y ^ n) := by
  rcases le_total x y with h | h
  · have h1 : (x + y) ^ n ≤ (2 * y) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at h1
    have : 0 ≤ x ^ n := pow_nonneg hx n
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
  · have h1 : (x + y) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at h1
    have : 0 ≤ y ^ n := pow_nonneg hy n
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]

lemma frz_univ {E : Type*} (X : ℕ → Ω → E) (n : ℕ) : frz X (fun _ => univ) n = X n := by
  funext ω
  obtain ⟨h1, -, h3, -⟩ := frz_fidx X (fun _ => (univ : Set Ω)) n ω
  rcases h3 with h | h
  · rw [h1, h]
  · exact absurd trivial h

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

variable (he : Function.Surjective e)
include he

end Sharp

end G26G


-- ===== Solutions.G26.RefAlg =====

/-! ### Real-variable estimates for the reference block bound -/

open IAFTRL

namespace G26G

lemma alg_N {c : ℝ} (hc : 0 ≤ c) (u : ℕ) {P : ℕ} (hP : 2 ≤ P) :
    ∑ s ∈ Finset.Icc u (2 * u), c * ((s : ℝ) + 1) ^ P / (((s : ℝ) + 2) ^ 4 / 2) ^ P ≤
      c * 2 ^ P / ((u : ℝ) + 1) ^ 4 := by
  have hu1 : (1 : ℝ) ≤ (u : ℝ) + 1 := by linarith [(Nat.cast_nonneg u : (0:ℝ) ≤ u)]
  have hterm : ∀ s ∈ Finset.Icc u (2 * u), c * ((s : ℝ) + 1) ^ P / (((s : ℝ) + 2) ^ 4 / 2) ^ P ≤
      c * 2 ^ P / ((u : ℝ) + 1) ^ 5 := by
    intro s hs
    have hus : (u : ℝ) ≤ s := by exact_mod_cast (Finset.mem_Icc.1 hs).1
    have hs1 : (1 : ℝ) ≤ (s : ℝ) + 1 := by linarith
    have h1 : ((s : ℝ) + 1) ^ 4 / 2 ≤ ((s : ℝ) + 2) ^ 4 / 2 := by
      have := pow_le_pow_left₀ (by linarith) (by linarith : (s : ℝ) + 1 ≤ (s : ℝ) + 2) 4
      linarith
    have h2 : (((s : ℝ) + 1) ^ 4 / 2) ^ P ≤ (((s : ℝ) + 2) ^ 4 / 2) ^ P :=
      pow_le_pow_left₀ (by positivity) h1 P
    have hpos : 0 < (((s : ℝ) + 1) ^ 4 / 2) ^ P := by positivity
    calc c * ((s : ℝ) + 1) ^ P / (((s : ℝ) + 2) ^ 4 / 2) ^ P
        ≤ c * ((s : ℝ) + 1) ^ P / (((s : ℝ) + 1) ^ 4 / 2) ^ P :=
          div_le_div_of_nonneg_left (by positivity) hpos h2
      _ = c * 2 ^ P / ((s : ℝ) + 1) ^ (3 * P) := by
          rw [div_pow, ← pow_mul]
          have : ((s : ℝ) + 1) ^ (4 * P) = ((s : ℝ) + 1) ^ P * ((s : ℝ) + 1) ^ (3 * P) := by
            rw [← pow_add]; ring_nf
          rw [this]; field_simp
      _ ≤ c * 2 ^ P / ((s : ℝ) + 1) ^ 5 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact pow_le_pow_right₀ hs1 (by omega)
      _ ≤ c * 2 ^ P / ((u : ℝ) + 1) ^ 5 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact pow_le_pow_left₀ (by positivity) (by linarith) 5
  calc _ ≤ ∑ _s ∈ Finset.Icc u (2 * u), c * 2 ^ P / ((u : ℝ) + 1) ^ 5 := Finset.sum_le_sum hterm
    _ = ((u : ℝ) + 1) * (c * 2 ^ P / ((u : ℝ) + 1) ^ 5) := by
        rw [Finset.sum_const, Nat.card_Icc, show 2 * u + 1 - u = u + 1 by omega, nsmul_eq_mul]
        push_cast; ring
    _ = c * 2 ^ P / ((u : ℝ) + 1) ^ 4 := by field_simp

/-- `root8 (2y) ≤ 2 root8 y` -/
lemma root8_two_mul {y : ℝ} (hy : 0 ≤ y) : root8 (2 * y) ≤ 2 * root8 y := by
  have h1 := root8_pow hy
  have h2 : (2 * root8 y) ^ 8 = 256 * y := by rw [mul_pow, h1]; norm_num
  by_contra h
  push Not at h
  have h3 := pow_lt_pow_left₀ h (by have := root8_nonneg y; positivity) (by norm_num : (8 : ℕ) ≠ 0)
  rw [root8_pow (by linarith), h2] at h3
  linarith

/-- the second-moment ratio `(nC+1)/(4z)` -/
lemma ratio_z {u nC : ℕ} (hnC : 1 ≤ nC) :
    (((nC : ℝ) + 1) / (4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)))) ^ 2 ≤
      ((nC : ℝ) + 1) / ((u : ℝ) + 1) / 8 := by
  have hn : (1 : ℝ) ≤ nC := by exact_mod_cast hnC
  have hu : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), div_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_pos (show (0:ℝ) < (nC:ℝ) by linarith) hu]

/-- bounding `x^(2j)` by `r^4` from `x^2 ≤ r ≤ 1` -/
lemma pow_even_le {x r : ℝ} (hx : 0 ≤ x) (hxr : x ^ 2 ≤ r) (hr1 : r ≤ 1) {j : ℕ} (hj : 4 ≤ j) :
    x ^ (2 * j) ≤ r ^ 4 := by
  have hr0 : 0 ≤ r := le_trans (sq_nonneg x) hxr
  rw [pow_mul]
  exact (pow_le_pow_left₀ (sq_nonneg x) hxr j).trans (pow_le_pow_of_le_one hr0 hr1 hj)

lemma alg_B2 {d k m0 u : ℕ} {lam Hn Rr : ℝ} (hlam : root8 ((m0 : ℝ) + 1) ^ 7 ≤ lam)
    (hu : (u : ℝ) + 1 ≤ 4 * ((m0 : ℝ) + 1)) (hkd : 8 * d + 32 ≤ 4 * k) (hR0 : 0 ≤ Rr)
    (hRu : Rr ≤ (u : ℝ) + 1) (hHn : 0 ≤ Hn) :
    2 ^ (4 * k) * 4 ^ d * Rr ^ d / lam ^ (4 * k) * (Hn * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k)) ≤
      2 ^ (4 * k) * 4 ^ d * Hn * 4 ^ d * 8 ^ (3 * k) * 256 / ((u : ℝ) + 1) ^ 4 := by
  set r := root8 ((m0 : ℝ) + 1)
  have hr1 : 1 ≤ r := one_le_root8 (by linarith [(Nat.cast_nonneg m0 : (0:ℝ) ≤ m0)])
  have hr8 : r ^ 8 = (m0 : ℝ) + 1 := root8_pow (by positivity)
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have e1 : r ^ (8 * d) = ((m0 : ℝ) + 1) ^ d := by rw [pow_mul r 8 d, hr8]
  have e2 : r ^ (24 * k) = ((m0 : ℝ) + 1) ^ (3 * k) := by
    rw [show 24 * k = 8 * (3 * k) by ring, pow_mul r 8 (3 * k), hr8]
  have e3 : r ^ 32 = ((m0 : ℝ) + 1) ^ 4 := by rw [show 32 = 8 * 4 by ring, pow_mul r 8 4, hr8]
  have h1 : Rr ^ d ≤ 4 ^ d * r ^ (8 * d) := by
    rw [e1, ← mul_pow]; exact pow_le_pow_left₀ hR0 (by linarith) d
  have h2 : (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k) ≤ 8 ^ (3 * k) * r ^ (24 * k) := by
    rw [e2, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _
  have h3 : ((u : ℝ) + 1) ^ 4 ≤ 256 * r ^ 32 := by
    rw [e3]
    have := pow_le_pow_left₀ hu1.le hu 4
    rw [mul_pow] at this; norm_num at this; linarith
  have h4 : r ^ (8 * d) * r ^ (24 * k) * r ^ 32 ≤ r ^ (28 * k) := by
    rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hr1 (by omega)
  have h5 : r ^ (28 * k) ≤ lam ^ (4 * k) := by
    rw [show 28 * k = 7 * (4 * k) by ring, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hlam _
  have key : Rr ^ d * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k) * ((u : ℝ) + 1) ^ 4 ≤
      4 ^ d * 8 ^ (3 * k) * 256 * lam ^ (4 * k) := by
    calc Rr ^ d * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k) * ((u : ℝ) + 1) ^ 4
        ≤ (4 ^ d * r ^ (8 * d)) * (8 ^ (3 * k) * r ^ (24 * k)) * (256 * r ^ 32) := by
          gcongr
      _ = 4 ^ d * 8 ^ (3 * k) * 256 * (r ^ (8 * d) * r ^ (24 * k) * r ^ 32) := by ring
      _ ≤ 4 ^ d * 8 ^ (3 * k) * 256 * lam ^ (4 * k) := by gcongr; exact h4.trans h5
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : (0 : ℝ) ≤ 2 ^ (4 * k) * 4 ^ d * Hn := by positivity
  calc 2 ^ (4 * k) * 4 ^ d * Rr ^ d * (Hn * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k)) * ((u : ℝ) + 1) ^ 4
      = (2 ^ (4 * k) * 4 ^ d * Hn) *
          (Rr ^ d * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k) * ((u : ℝ) + 1) ^ 4) := by ring
    _ ≤ (2 ^ (4 * k) * 4 ^ d * Hn) * (4 ^ d * 8 ^ (3 * k) * 256 * lam ^ (4 * k)) :=
        mul_le_mul_of_nonneg_left key hc
    _ = _ := by ring

lemma alg_B3 {d k u nC : ℕ} {lam C cK : ℝ} (hnC : 1 ≤ nC) (hnu : nC ≤ u) (hC0 : 0 ≤ C)
    (hC : C ≤ nC) (hcK : 0 ≤ cK) (hlam : 4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) ≤ lam)
    (hkd : 2 * d + 6 ≤ 2 * k) :
    2 ^ (4 * k) * 4 ^ d * (((u : ℝ) + 1) / ((nC : ℝ) + 1)) ^ d / lam ^ (4 * k) *
      ((((2 * u : ℕ) : ℝ) + 1) / ((nC : ℝ) + 1)) ^ (d + 2) *
        (2 ^ (4 * k) * (cK * ((nC : ℝ) + 1) ^ (4 * k) + (2 * C) ^ (4 * k))) ≤
      2 ^ (4 * k) * 4 ^ d * 2 ^ (d + 2) * 2 ^ (4 * k) * (cK + 2 ^ (4 * k)) *
        (((nC : ℝ) + 1) / ((u : ℝ) + 1)) ^ 4 := by
  have hn1 : (0 : ℝ) < (nC : ℝ) + 1 := by positivity
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hn : (1 : ℝ) ≤ nC := by exact_mod_cast hnC
  have hz : 0 < Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) := Real.sqrt_pos.2 (by positivity)
  have hlam0 : 0 < lam := by linarith
  set rp := ((nC : ℝ) + 1) / ((u : ℝ) + 1)
  set Rr := ((u : ℝ) + 1) / ((nC : ℝ) + 1)
  have hrR : rp * Rr = 1 := by simp only [rp, Rr]; field_simp
  have hrp0 : 0 < rp := by positivity
  have hrp1 : rp ≤ 1 := by
    simp only [rp]; rw [div_le_one hu1]; have : (nC : ℝ) ≤ u := by exact_mod_cast hnu
    linarith
  set y := ((nC : ℝ) + 1) / lam
  have hy0 : 0 ≤ y := by positivity
  have hy2 : y ^ 2 ≤ rp := by
    have h1 : y ≤ ((nC : ℝ) + 1) / (4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlam
    have h2 := ratio_z (u := u) hnC
    have h3 := pow_le_pow_left₀ hy0 h1 2
    have : rp / 8 ≤ rp := by linarith
    linarith
  have hyP : y ^ (4 * k) ≤ rp ^ (2 * k) := by
    rw [show 4 * k = 2 * (2 * k) by ring, pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hy2 _
  have hbr : (2 * C) ^ (4 * k) ≤ 2 ^ (4 * k) * ((nC : ℝ) + 1) ^ (4 * k) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hq : (((2 * u : ℕ) : ℝ) + 1) / ((nC : ℝ) + 1) ≤ 2 * Rr := by
    simp only [Rr]; rw [mul_div_assoc', div_le_div_iff_of_pos_right hn1]; push_cast; linarith
  have hk : rp ^ (2 * k) * Rr ^ (2 * d + 2) ≤ rp ^ 4 := by
    have e : rp ^ (2 * k) = rp ^ (2 * k - (2 * d + 2)) * rp ^ (2 * d + 2) := by
      rw [← pow_add]; congr 1; omega
    rw [e, mul_assoc, ← mul_pow, hrR, one_pow, mul_one]
    exact pow_le_pow_of_le_one hrp0.le hrp1 (by omega)
  -- assemble
  have hcK2 : 0 ≤ cK + 2 ^ (4 * k) := by positivity
  have hB : 2 ^ (4 * k) * (cK * ((nC : ℝ) + 1) ^ (4 * k) + (2 * C) ^ (4 * k)) ≤
      2 ^ (4 * k) * (cK + 2 ^ (4 * k)) * ((nC : ℝ) + 1) ^ (4 * k) := by
    have := mul_le_mul_of_nonneg_left hbr (show (0:ℝ) ≤ 2 ^ (4 * k) by positivity)
    nlinarith
  have hpow : ((((2 * u : ℕ) : ℝ) + 1) / ((nC : ℝ) + 1)) ^ (d + 2) ≤ 2 ^ (d + 2) * Rr ^ (d + 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hq _
  have e2 : ((nC : ℝ) + 1) ^ (4 * k) / lam ^ (4 * k) = y ^ (4 * k) := by rw [div_pow]
  calc 2 ^ (4 * k) * 4 ^ d * Rr ^ d / lam ^ (4 * k) *
        ((((2 * u : ℕ) : ℝ) + 1) / ((nC : ℝ) + 1)) ^ (d + 2) *
        (2 ^ (4 * k) * (cK * ((nC : ℝ) + 1) ^ (4 * k) + (2 * C) ^ (4 * k)))
      ≤ 2 ^ (4 * k) * 4 ^ d * Rr ^ d / lam ^ (4 * k) * (2 ^ (d + 2) * Rr ^ (d + 2)) *
          (2 ^ (4 * k) * (cK + 2 ^ (4 * k)) * ((nC : ℝ) + 1) ^ (4 * k)) := by
        gcongr
    _ = 2 ^ (4 * k) * 4 ^ d * 2 ^ (d + 2) * 2 ^ (4 * k) * (cK + 2 ^ (4 * k)) *
          (Rr ^ (2 * d + 2) * (((nC : ℝ) + 1) ^ (4 * k) / lam ^ (4 * k))) := by
        rw [show 2 * d + 2 = d + (d + 2) by ring, pow_add]; ring
    _ ≤ 2 ^ (4 * k) * 4 ^ d * 2 ^ (d + 2) * 2 ^ (4 * k) * (cK + 2 ^ (4 * k)) * rp ^ 4 := by
        rw [e2]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc Rr ^ (2 * d + 2) * y ^ (4 * k) ≤ Rr ^ (2 * d + 2) * rp ^ (2 * k) :=
              mul_le_mul_of_nonneg_left hyP (by positivity)
          _ = rp ^ (2 * k) * Rr ^ (2 * d + 2) := by ring
          _ ≤ rp ^ 4 := hk

lemma alg_v {u nC : ℕ} :
    4 * tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u) / ((u : ℝ) + 1) ≤
      512 / root8 ((u : ℝ) + 1) + 16 * Real.sqrt (((nC : ℝ) + 1) / ((u : ℝ) + 1)) := by
  unfold tauB
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  set ry := root8 ((u : ℝ) + 1)
  have hry8 : ry ^ 8 = (u : ℝ) + 1 := root8_pow (by positivity)
  have hr1 : 1 ≤ ry := one_le_root8 (by linarith [(Nat.cast_nonneg u : (0:ℝ) ≤ u)])
  have hy : ((2 * u : ℕ) : ℝ) + 1 ≤ 2 * ((u : ℝ) + 1) := by push_cast; linarith
  have h1 : (((2 * u : ℕ) : ℝ) + 1) ^ ((7 : ℝ) / 8) ≤ (2 * ry) ^ 7 := by
    rw [rpow78_eq (by positivity)]
    exact pow_le_pow_left₀ (root8_nonneg _)
      ((root8_mono hy).trans (root8_two_mul (by positivity))) 7
  have h2 : 4 * (2 * ry) ^ 7 / ((u : ℝ) + 1) = 512 / ry := by
    rw [← hry8]; field_simp; ring
  have h3 : 4 * (4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) / ((u : ℝ) + 1) ≤
      16 * Real.sqrt (((nC : ℝ) + 1) / ((u : ℝ) + 1)) := by
    have e : Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) / ((u : ℝ) + 1) =
        Real.sqrt ((nC : ℝ) / ((u : ℝ) + 1)) := by
      rw [show (nC : ℝ) / ((u : ℝ) + 1) = ((nC : ℝ) * ((u : ℝ) + 1)) / ((u : ℝ) + 1) ^ 2 by
        field_simp, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hu1.le]
    have h4 : Real.sqrt ((nC : ℝ) / ((u : ℝ) + 1)) ≤ Real.sqrt (((nC : ℝ) + 1) / ((u : ℝ) + 1)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hu1.le)
    calc 4 * (4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) / ((u : ℝ) + 1) =
        16 * (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) / ((u : ℝ) + 1)) := by ring
      _ ≤ _ := by rw [e]; linarith
  calc 4 * ((((2 * u : ℕ) : ℝ) + 1) ^ ((7 : ℝ) / 8) + 4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) /
        ((u : ℝ) + 1)
      = 4 * (((2 * u : ℕ) : ℝ) + 1) ^ ((7 : ℝ) / 8) / ((u : ℝ) + 1) +
          4 * (4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) / ((u : ℝ) + 1) := by ring
    _ ≤ 4 * (2 * ry) ^ 7 / ((u : ℝ) + 1) + 16 * Real.sqrt (((nC : ℝ) + 1) / ((u : ℝ) + 1)) := by
        gcongr
    _ = _ := by rw [h2]

lemma alg_x12 {u nC : ℕ} (N : ℕ) :
    (512 / root8 ((u : ℝ) + 1)) ^ (8 * N) = 512 ^ (8 * N) / ((u : ℝ) + 1) ^ N ∧
    (16 * Real.sqrt (((nC : ℝ) + 1) / ((u : ℝ) + 1))) ^ (8 * N) =
      16 ^ (8 * N) * (((nC : ℝ) + 1) / ((u : ℝ) + 1)) ^ (4 * N) := by
  constructor
  · rw [div_pow, pow_mul (root8 _) 8 N, root8_pow (by positivity)]
  · rw [mul_pow, show 8 * N = 2 * (4 * N) by ring, pow_mul (Real.sqrt _) 2,
      Real.sq_sqrt (by positivity)]

end G26G


-- ===== Solutions.G26.RefAlg3 =====

/-! ### The reference block bound (Lemma G.29): algebra -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma alg_C1 {P u : ℕ} (hP : 32 ≤ P) {a cK x1 x2 : ℝ} (ha0 : 0 < a) (hau : a ≤ (u : ℝ) + 1)
    (hv : a / ((u : ℝ) + 1) ≤ x1 + x2) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hcK : 0 ≤ cK) :
    2 ^ P * cK * (((2 * u : ℕ) : ℝ) + 1) ^ P / (2 * ((u : ℝ) + 1) ^ 2 / a) ^ P ≤
      2 ^ P * cK * (2 ^ 32 * (x1 ^ 32 + x2 ^ 32)) := by
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  set v := a / ((u : ℝ) + 1)
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 := by simp only [v]; rw [div_le_one hu1]; exact hau
  set w := (((2 * u : ℕ) : ℝ) + 1) / (2 * ((u : ℝ) + 1) ^ 2 / a)
  have hw0 : 0 ≤ w := by positivity
  have hwv : w ≤ v := by
    simp only [w, v]
    rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hu1]
    push_cast; nlinarith
  have e : 2 ^ P * cK * (((2 * u : ℕ) : ℝ) + 1) ^ P / (2 * ((u : ℝ) + 1) ^ 2 / a) ^ P =
      2 ^ P * cK * w ^ P := by simp only [w]; rw [mul_div_assoc, ← div_pow]
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc w ^ P ≤ w ^ 32 := pow_le_pow_of_le_one hw0 (hwv.trans hv1) hP
    _ ≤ v ^ 32 := pow_le_pow_left₀ hw0 hwv 32
    _ ≤ (x1 + x2) ^ 32 := pow_le_pow_left₀ hv0 hv 32
    _ ≤ 2 ^ 32 * (x1 ^ 32 + x2 ^ 32) := add_pow_le_two hx1 hx2 32

lemma alg_C2 {P d u M q : ℕ} (hPq : P = 8 * q) (hM : 8 * M + 2 * d ≤ P) {a sig L x1 x2 : ℝ}
    (ha0 : 0 < a) (hau : a ≤ (u : ℝ) + 1) (hv : a / ((u : ℝ) + 1) ≤ x1 + x2) (hx1 : 0 ≤ x1)
    (hx2 : 0 ≤ x2) (hs : 0 < sig) (hL : 0 ≤ L) (hrL : 0 < root8 L) :
    (2 * a) ^ P * ((2 * ((u : ℝ) + 1) ^ 2 / a) / a) ^ d *
      (2 ^ P * (4 / (((u : ℝ) + 1) * (sig / root8 L))) ^ P) ≤
      2 ^ (2 * P + d) * 4 ^ P * sig⁻¹ ^ P * L ^ q * (2 ^ (8 * M) * (x1 ^ (8 * M) + x2 ^ (8 * M))) := by
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hv0 : 0 < a / ((u : ℝ) + 1) := by positivity
  have hv1 : a / ((u : ℝ) + 1) ≤ 1 := by rw [div_le_one hu1]; exact hau
  have hroot : root8 L ^ P = L ^ q := by rw [hPq, pow_mul, root8_pow hL]
  have hane : a ≠ 0 := ha0.ne'
  have hune : (u : ℝ) + 1 ≠ 0 := hu1.ne'
  have hsne : sig ≠ 0 := hs.ne'
  have hrne : root8 L ≠ 0 := hrL.ne'
  have e : (2 * a) ^ P * ((2 * ((u : ℝ) + 1) ^ 2 / a) / a) ^ d *
      (2 ^ P * (4 / (((u : ℝ) + 1) * (sig / root8 L))) ^ P) =
      2 ^ (2 * P + d) * 4 ^ P * sig⁻¹ ^ P * L ^ q *
        ((a / ((u : ℝ) + 1)) ^ P / (a / ((u : ℝ) + 1)) ^ (2 * d)) := by
    obtain ⟨w, hw⟩ : ∃ w, a / ((u : ℝ) + 1) = w := ⟨_, rfl⟩
    have hwne : w ≠ 0 := by rw [← hw]; exact hv0.ne'
    have haw : a = w * ((u : ℝ) + 1) := by rw [← hw]; field_simp
    have h1 : (2 * ((u : ℝ) + 1) ^ 2 / a) / a = 2 / w ^ 2 := by rw [haw]; field_simp
    have h2 : 4 / (((u : ℝ) + 1) * (sig / root8 L)) = 4 * root8 L / (((u : ℝ) + 1) * sig) := by
      field_simp
    have h3 : 2 * a = 2 * w * ((u : ℝ) + 1) := by rw [haw]; ring
    rw [hw, h1, h2, h3, ← hroot, show (2 : ℝ) ^ (2 * P + d) = 2 ^ P * 2 ^ P * 2 ^ d by
      rw [← pow_add, ← pow_add]; ring_nf]
    rw [mul_pow, mul_pow, div_pow, div_pow, mul_pow, mul_pow, inv_pow, ← pow_mul]
    field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have e2 : (a / ((u : ℝ) + 1)) ^ P / (a / ((u : ℝ) + 1)) ^ (2 * d) =
      (a / ((u : ℝ) + 1)) ^ (P - 2 * d) := by
    rw [div_eq_iff (by positivity), ← pow_add]; congr 1; omega
  rw [e2]
  calc (a / ((u : ℝ) + 1)) ^ (P - 2 * d) ≤ (a / ((u : ℝ) + 1)) ^ (8 * M) :=
        pow_le_pow_of_le_one hv0.le hv1 (by omega)
    _ ≤ (x1 + x2) ^ (8 * M) := pow_le_pow_left₀ hv0.le hv _
    _ ≤ 2 ^ (8 * M) * (x1 ^ (8 * M) + x2 ^ (8 * M)) := add_pow_le_two hx1 hx2 _

lemma comb6 {T1 T2 T3 T4 T5 T6 r iu : ℝ} (t1 : 0 ≤ T1) (t2 : 0 ≤ T2) (t3 : 0 ≤ T3) (t4 : 0 ≤ T4)
    (hr : 0 ≤ r) (hiu : 0 ≤ iu) :
    T1 * iu + (T2 * r + (T3 * iu + T4 * r)) + T5 * (r + iu) + T6 * (r + iu) ≤
      (T1 + T2 + T3 + T4 + T5 + T6) * (r + iu) := by
  nlinarith [mul_nonneg t1 hr, mul_nonneg t2 hiu, mul_nonneg t3 hr, mul_nonneg t4 hiu]

lemma alg_C2f {K6 W Lq A U Bc RM F c5q r iu : ℝ} (hK : 0 ≤ K6) (hW : 0 ≤ W)
    (h : Lq * (A / U + Bc * RM) ≤ (A * F + Bc * c5q) * (r + iu)) :
    K6 * Lq * (W * (A / U + Bc * RM)) ≤ K6 * (W * (A * F + Bc * c5q)) * (r + iu) := by
  have := mul_le_mul_of_nonneg_left h (mul_nonneg hK hW)
  calc K6 * Lq * (W * (A / U + Bc * RM)) = K6 * W * (Lq * (A / U + Bc * RM)) := by ring
    _ ≤ K6 * W * ((A * F + Bc * c5q) * (r + iu)) := this
    _ = _ := by ring

lemma alg_C1f {X Y r iu : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hiu : 0 ≤ iu) : X * iu + Y * r ^ 16 ≤ (X + Y) * (r ^ 4 + iu) := by
  have h : r ^ 16 ≤ r ^ 4 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have h4 : 0 ≤ r ^ 4 := by positivity
  nlinarith [mul_nonneg hX h4, mul_nonneg hY hiu, mul_le_mul_of_nonneg_left h hY]

lemma alg_Lq {q M : ℕ} {L c5 cL rp Rr y A Bc : ℝ} (hL0 : 0 ≤ L) (hc5 : 0 ≤ c5) (hcL : 0 ≤ cL)
    (hA : 0 ≤ A) (hBc : 0 ≤ Bc) (hrp0 : 0 ≤ rp) (hrp1 : rp ≤ 1) (hrR : rp * Rr = 1)
    (hL5 : L ≤ c5 * Rr) (hLq : L ^ q ≤ cL * y) (hy : 1 ≤ y) (hqM : q + 4 ≤ 4 * M) (hM : 5 ≤ M) :
    L ^ q * (A / y ^ M + Bc * rp ^ (4 * M)) ≤ (A * cL + Bc * c5 ^ q) * (rp ^ 4 + 1 / y ^ 4) := by
  have hy0 : 0 < y := by linarith
  have h1 : L ^ q / y ^ M ≤ cL * (1 / y ^ 4) := by
    rw [div_le_iff₀ (by positivity)]
    calc L ^ q ≤ cL * y := hLq
      _ ≤ cL * (y ^ M / y ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ hcL
          rw [le_div_iff₀ (by positivity), ← pow_succ']
          exact pow_le_pow_right₀ hy (by omega)
      _ = cL * (1 / y ^ 4) * y ^ M := by field_simp
  have hR0 : 0 ≤ Rr := by
    by_contra h
    push_neg at h
    nlinarith
  have h2 : L ^ q * rp ^ (4 * M) ≤ c5 ^ q * rp ^ 4 := by
    have hLq' : L ^ q ≤ (c5 * Rr) ^ q := pow_le_pow_left₀ hL0 hL5 q
    have e : (c5 * Rr) ^ q * rp ^ (4 * M) = c5 ^ q * rp ^ (4 * M - q) := by
      rw [mul_pow, show 4 * M = q + (4 * M - q) by omega, pow_add]
      rw [show q + (4 * M - q) - q = 4 * M - q by omega]
      have : Rr ^ q * rp ^ q = 1 := by rw [← mul_pow, mul_comm, hrR, one_pow]
      calc c5 ^ q * Rr ^ q * (rp ^ q * rp ^ (4 * M - q)) =
          c5 ^ q * (Rr ^ q * rp ^ q) * rp ^ (4 * M - q) := by ring
        _ = _ := by rw [this, mul_one]
    calc L ^ q * rp ^ (4 * M) ≤ (c5 * Rr) ^ q * rp ^ (4 * M) :=
          mul_le_mul_of_nonneg_right hLq' (by positivity)
      _ = c5 ^ q * rp ^ (4 * M - q) := e
      _ ≤ c5 ^ q * rp ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hrp0 hrp1 (by omega)) (by positivity)
  have e : L ^ q * (A / y ^ M + Bc * rp ^ (4 * M)) =
      A * (L ^ q / y ^ M) + Bc * (L ^ q * rp ^ (4 * M)) := by ring
  rw [e]
  have h4 : 0 ≤ rp ^ 4 := by positivity
  have hiu : 0 ≤ 1 / y ^ 4 := by positivity
  have h1' := mul_le_mul_of_nonneg_left h1 hA
  have h2' := mul_le_mul_of_nonneg_left h2 hBc
  nlinarith [mul_nonneg (mul_nonneg hA hcL) h4, mul_nonneg (mul_nonneg hBc (pow_nonneg hc5 q)) hiu]

set_option maxHeartbeats 1000000 in
/-- **the algebra of the reference block bound** -/
theorem ref_block_alg {d u nC m0 : ℕ} {C sig c0 τm L : ℝ} (hsig : 0 < sig) (hc0 : 0 ≤ c0)
    (hnC1 : 1 ≤ nC) (hnu : nC ≤ u) (hC0 : 0 ≤ C) (hCn : C ≤ nC)
    (hu4 : (u : ℝ) + 1 ≤ 4 * ((m0 : ℝ) + 1))
    (hτm7 : root8 ((m0 : ℝ) + 1) ^ 7 ≤ τm) (hτmz : 4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) ≤ τm)
    (hτ2 : tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u) ≤ ((u : ℝ) + 1) / 4)
    (hL1 : 1 ≤ L)
    (hLq : L ^ (512 * (d + 1)) ≤
      ((4 + c0) ^ (512 * (d + 1)) * ((512 * (d + 1)).factorial : ℝ) * 6) * ((u : ℝ) + 1))
    (hL5 : L ≤ (12 + c0) * (((u : ℝ) + 1) / ((nC : ℝ) + 1))) :
    ∑ s ∈ Finset.Icc u (2 * u), cK d * ((s : ℝ) + 1) ^ (4 * kk d) /
          (((s : ℝ) + 2) ^ 4 / 2) ^ (4 * kk d) +
      (2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) /
          (τm * (((u : ℝ) + 1) / ((nC : ℝ) + 1))) ^ (4 * kk d) +
        2 ^ (4 * kk d) * 4 ^ d * ((τm * (((u : ℝ) + 1) / ((nC : ℝ) + 1))) / τm) ^ d /
          τm ^ (4 * kk d) *
          (Hneg (kk d) (16 * d + 1) (gB d) * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * kk d) +
            ((((2 * u : ℕ) : ℝ) + 1) / ((nC : ℝ) + 1)) ^ (d + 2) *
              (2 ^ (4 * kk d) * (cK d * ((nC : ℝ) + 1) ^ (4 * kk d) + (2 * C) ^ (4 * kk d))))) +
      2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) /
        (2 * ((u : ℝ) + 1) ^ 2 / (4 * tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u))) ^
          (4 * kk d) +
      (2 * (4 * tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u))) ^ (4 * kk d) *
        ((2 * ((u : ℝ) + 1) ^ 2 / (4 * tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u))) /
          (4 * tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u))) ^ d *
        (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * (sig / root8 L))) ^ (4 * kk d)) ≤
      Dexpr d sig c0 * ((((nC : ℝ) + 1) / ((u : ℝ) + 1)) ^ 4 + 1 / ((u : ℝ) + 1) ^ 4) := by
  have hkk : kk d = 1024 * (d + 1) := by unfold kk; rfl
  have hk2P : 2 ≤ 4 * kk d := by rw [hkk]; omega
  have hk4 : 4 ≤ 2 * kk d := by rw [hkk]; omega
  have hkB2 : 8 * d + 32 ≤ 4 * kk d := by rw [hkk]; omega
  have hkB3 : 2 * d + 6 ≤ 2 * kk d := by rw [hkk]; omega
  have hk32 : 32 ≤ 4 * kk d := by rw [hkk]; omega
  have hkq : 4 * kk d = 8 * (512 * (d + 1)) := by rw [hkk]; ring
  have hkM : 8 * (256 * (d + 1)) + 2 * d ≤ 4 * kk d := by rw [hkk]; omega
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hn1 : (0 : ℝ) < (nC : ℝ) + 1 := by positivity
  have hcK := cK_nonneg d
  have hz0 : 0 ≤ Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) := Real.sqrt_nonneg _
  have hzp : 0 < Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) := by
    have : (1 : ℝ) ≤ nC := by exact_mod_cast hnC1
    exact Real.sqrt_pos.2 (by positivity)
  obtain ⟨z, hz⟩ : ∃ z, Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) = z := ⟨_, rfl⟩
  rw [hz] at hτmz hτ2 hz0 hzp ⊢
  obtain ⟨rp, hrp⟩ : ∃ rp, ((nC : ℝ) + 1) / ((u : ℝ) + 1) = rp := ⟨_, rfl⟩
  obtain ⟨Rr, hRr⟩ : ∃ Rr, ((u : ℝ) + 1) / ((nC : ℝ) + 1) = Rr := ⟨_, rfl⟩
  rw [hRr] at hL5
  rw [hrp, hRr]
  have hrp0 : 0 ≤ rp := by rw [← hrp]; positivity
  have hrp1 : rp ≤ 1 := by
    rw [← hrp, div_le_one hu1]; have : (nC : ℝ) ≤ u := by exact_mod_cast hnu
    linarith
  have hR1 : 1 ≤ Rr := by
    rw [← hRr, le_div_iff₀ hn1]; have : (nC : ℝ) ≤ u := by exact_mod_cast hnu
    linarith
  have hRr0 : 0 ≤ Rr := by linarith
  have hrR : rp * Rr = 1 := by rw [← hrp, ← hRr]; field_simp
  have hτm0 : 0 < τm := by linarith
  -- near failures
  have hN := alg_N hcK u (P := 4 * kk d) hk2P
  -- B1
  have hB1 : 2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) / (τm * Rr) ^ (4 * kk d) ≤
      2 ^ (4 * kk d) * cK d * rp ^ 4 := by
    have hρ1p : 0 < τm * Rr := by positivity
    obtain ⟨x, hx⟩ : ∃ x, (((2 * u : ℕ) : ℝ) + 1) / (τm * Rr) = x := ⟨_, rfl⟩
    have hx0 : 0 ≤ x := by rw [← hx]; positivity
    have hxle : x ≤ ((nC : ℝ) + 1) / (2 * z) := by
      have h2u : (((2 * u : ℕ) : ℝ) + 1) ≤ 2 * ((u : ℝ) + 1) := by push_cast; linarith
      rw [← hx]
      calc (((2 * u : ℕ) : ℝ) + 1) / (τm * Rr) ≤ (2 * ((u : ℝ) + 1)) / (4 * z * Rr) :=
            div_le_div₀ (by positivity) h2u (by positivity) (mul_le_mul_of_nonneg_right hτmz hRr0)
        _ = ((nC : ℝ) + 1) / (2 * z) := by rw [← hRr]; field_simp; ring
    have hx2 : x ^ 2 ≤ rp := by
      have h1 := pow_le_pow_left₀ hx0 hxle 2
      have h2 := ratio_z (u := u) hnC1
      rw [hz, hrp] at h2
      have e : (((nC : ℝ) + 1) / (2 * z)) ^ 2 = 4 * (((nC : ℝ) + 1) / (4 * z)) ^ 2 := by
        field_simp; ring
      calc x ^ 2 ≤ (((nC : ℝ) + 1) / (2 * z)) ^ 2 := h1
        _ = 4 * (((nC : ℝ) + 1) / (4 * z)) ^ 2 := e
        _ ≤ 4 * (rp / 8) := by linarith
        _ ≤ rp := by linarith
    have e : 2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) / (τm * Rr) ^ (4 * kk d) =
        2 ^ (4 * kk d) * cK d * x ^ (4 * kk d) := by rw [← hx, mul_div_assoc, ← div_pow]
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg (by norm_num) _) hcK)
    rw [show 4 * kk d = 2 * (2 * kk d) by ring]
    exact pow_even_le hx0 hx2 hrp1 hk4
  -- B2, B3
  have hHn : 0 ≤ Hneg (kk d) (16 * d + 1) (gB d) := by
    obtain ⟨hk2, -, -, -, hB⟩ := kk_facts d
    have hB' : 2 ^ 20 * (4 * (kk d : ℝ)) ≤ gB d := by exact_mod_cast hB
    have hBp := G2R.gB_pos (d := d)
    unfold Hneg Kneg
    have := vneg_lt (kk d) hk2 (gB d) hB'
    exact div_nonneg (by positivity) (by linarith)
  have eR : τm * Rr / τm = Rr := by field_simp
  rw [eR]
  have hRu : Rr ≤ (u : ℝ) + 1 := by
    rw [← hRr]; exact div_le_self hu1.le (by linarith [(Nat.cast_nonneg nC : (0:ℝ) ≤ nC)])
  have hB2 := alg_B2 (d := d) (k := kk d) (m0 := m0) (u := u) (lam := τm)
    (Hn := Hneg (kk d) (16 * d + 1) (gB d)) (Rr := Rr) hτm7 hu4 hkB2 hRr0 hRu hHn
  have hB3 := alg_B3 (d := d) (k := kk d) (lam := τm) (C := C) (cK := cK d) hnC1 hnu hC0 hCn hcK
    (by rw [hz]; exact hτmz) hkB3
  rw [hRr, hrp] at hB3
  rw [mul_add]
  -- C1, C2
  have hτB0 : 0 < 4 * tauB z (2 * u) := by have := tauB_pos hz0 (2 * u); positivity
  have hau : 4 * tauB z (2 * u) ≤ (u : ℝ) + 1 := by linarith
  have hv := alg_v (u := u) (nC := nC)
  rw [hz, hrp] at hv
  have hx1 : 0 ≤ 512 / root8 ((u : ℝ) + 1) := div_nonneg (by norm_num) (root8_nonneg _)
  have hx2 : 0 ≤ 16 * Real.sqrt rp := by positivity
  have hC1 := alg_C1 (P := 4 * kk d) (u := u) hk32 hτB0 hau hv hx1 hx2 hcK
  have hL0 : 0 ≤ L := by linarith
  have hrL : 0 < root8 L := lt_of_lt_of_le one_pos (one_le_root8 hL1)
  have hC2 := alg_C2 (P := 4 * kk d) (d := d) (u := u) (M := 256 * (d + 1)) (q := 512 * (d + 1))
    hkq hkM hτB0 hau hv hx1 hx2 hsig hL0 hrL
  obtain ⟨hx4a, hx4b⟩ := alg_x12 (u := u) (nC := nC) 4
  obtain ⟨hxMa, hxMb⟩ := alg_x12 (u := u) (nC := nC) (256 * (d + 1))
  rw [hrp] at hx4b hxMb
  rw [show (8 : ℕ) * 4 = 32 from rfl] at hx4a hx4b
  rw [show (4 : ℕ) * 4 = 16 from rfl] at hx4b
  rw [hx4a, hx4b] at hC1
  rw [hxMa, hxMb] at hC2
  obtain ⟨iu, hiu⟩ : ∃ iu, 1 / ((u : ℝ) + 1) ^ 4 = iu := ⟨_, rfl⟩
  have hiu0 : 0 ≤ iu := by rw [← hiu]; positivity
  have hr40 : 0 ≤ rp ^ 4 := by positivity
  rw [hiu]
  have hdiv : ∀ c : ℝ, c / ((u : ℝ) + 1) ^ 4 = c * iu := fun c => by rw [← hiu]; ring
  rw [hdiv] at hN hB2
  rw [div_eq_mul_one_div (512 ^ 32 : ℝ), hiu] at hC1
  have hC1' : 2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) /
      (2 * ((u : ℝ) + 1) ^ 2 / (4 * tauB z (2 * u))) ^ (4 * kk d) ≤
      2 ^ (4 * kk d) * cK d * (2 ^ 32 * (512 ^ 32 + 16 ^ 32)) * (rp ^ 4 + iu) := by
    refine hC1.trans ?_
    have h := alg_C1f (X := (512 : ℝ) ^ 32) (Y := (16 : ℝ) ^ 32) (by positivity) (by positivity)
      hrp0 hrp1 hiu0
    have h2 : (0 : ℝ) ≤ 2 ^ (4 * kk d) * cK d * 2 ^ 32 := by positivity
    have := mul_le_mul_of_nonneg_left h h2
    calc 2 ^ (4 * kk d) * cK d * (2 ^ 32 * (512 ^ 32 * iu + 16 ^ 32 * rp ^ 16))
        = 2 ^ (4 * kk d) * cK d * 2 ^ 32 * (512 ^ 32 * iu + 16 ^ 32 * rp ^ 16) := by ring
      _ ≤ 2 ^ (4 * kk d) * cK d * 2 ^ 32 * ((512 ^ 32 + 16 ^ 32) * (rp ^ 4 + iu)) := this
      _ = _ := by ring
  have hLq' := alg_Lq (q := 512 * (d + 1)) (M := 256 * (d + 1)) (L := L) (c5 := 12 + c0)
    (cL := (4 + c0) ^ (512 * (d + 1)) * ((512 * (d + 1)).factorial : ℝ) * 6) (rp := rp) (Rr := Rr)
    (y := (u : ℝ) + 1) (A := 512 ^ (8 * (256 * (d + 1)))) (Bc := 16 ^ (8 * (256 * (d + 1))))
    hL0 (by linarith) (by positivity) (by positivity) (by positivity) hrp0 hrp1 hrR hL5 hLq
    (by linarith [(Nat.cast_nonneg u : (0:ℝ) ≤ u)]) (by omega) (by omega)
  rw [hiu] at hLq'
  obtain ⟨K6, hK6⟩ : ∃ K, (2 : ℝ) ^ (2 * (4 * kk d) + d) * 4 ^ (4 * kk d) * sig⁻¹ ^ (4 * kk d) = K :=
    ⟨_, rfl⟩
  have hK60 : 0 ≤ K6 := by rw [← hK6]; have := hsig.le; positivity
  rw [hK6] at hC2
  have hC2' : (2 * (4 * tauB z (2 * u))) ^ (4 * kk d) *
      (2 * ((u : ℝ) + 1) ^ 2 / (4 * tauB z (2 * u)) / (4 * tauB z (2 * u))) ^ d *
        (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * (sig / root8 L))) ^ (4 * kk d)) ≤
      K6 * (2 ^ (8 * (256 * (d + 1))) *
        (512 ^ (8 * (256 * (d + 1))) *
            ((4 + c0) ^ (512 * (d + 1)) * ((512 * (d + 1)).factorial : ℝ) * 6) +
          16 ^ (8 * (256 * (d + 1))) * (12 + c0) ^ (512 * (d + 1)))) * (rp ^ 4 + iu) := by
    refine hC2.trans (alg_C2f hK60 (by positivity) hLq')
  have hB3' : 2 ^ (4 * kk d) * 4 ^ d * Rr ^ d / τm ^ (4 * kk d) *
      (((((2 * u : ℕ) : ℝ) + 1) / ((nC : ℝ) + 1)) ^ (d + 2) *
        (2 ^ (4 * kk d) * (cK d * ((nC : ℝ) + 1) ^ (4 * kk d) + (2 * C) ^ (4 * kk d)))) ≤
      2 ^ (4 * kk d) * 4 ^ d * 2 ^ (d + 2) * 2 ^ (4 * kk d) * (cK d + 2 ^ (4 * kk d)) * rp ^ 4 := by
    rw [← mul_assoc]; exact hB3
  have hsum := add_le_add (add_le_add (add_le_add hN (add_le_add hB1 (add_le_add hB2 hB3'))) hC1') hC2'
  refine hsum.trans ?_
  unfold Dexpr
  rw [← hK6]
  have t1 : 0 ≤ cK d * 2 ^ (4 * kk d) := by positivity
  have t2 : 0 ≤ (2 : ℝ) ^ (4 * kk d) * cK d := by positivity
  have t3 : 0 ≤ (2 : ℝ) ^ (4 * kk d) * 4 ^ d * Hneg (kk d) (16 * d + 1) (gB d) * 4 ^ d *
    8 ^ (3 * kk d) * 256 := by positivity
  have t4 : 0 ≤ (2 : ℝ) ^ (4 * kk d) * 4 ^ d * 2 ^ (d + 2) * 2 ^ (4 * kk d) *
    (cK d + 2 ^ (4 * kk d)) := by positivity
  exact comb6 t1 t2 t3 t4 hr40 hiu0

end G26G


theorem _root_.solution : type_of% @G26G.ref_block_alg := @G26G.ref_block_alg
