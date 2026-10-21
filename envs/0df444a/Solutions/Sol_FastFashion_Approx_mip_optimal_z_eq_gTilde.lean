-- Prove2me | solution 1 for FastFashion.Approx.mip_optimal_z_eq_gTilde
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:52:59.576654+00:00
-- url     : https://prove2.me/submissions/8da2947f-3a2e-4826-b35d-db35353a6915

import Mathlib
import Definitions.Def_FastFashion_Approx_Tangents
import Definitions.Def_FastFashion_Approx_MIP

set_option autoImplicit false
open FastFashion.Approx

theorem lg_succ (k : ℕ) (b : ℝ) :
    lowerGamma (k + 2) b = (k + 1) * lowerGamma (k + 1) b - b ^ (k + 1) * Real.exp (-b) := by
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 1 - 1 = k := by omega
  unfold lowerGamma
  rw [e1, e2]
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) b, HasDerivAt (fun x : ℝ => x ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
    intro x _
    simpa using hasDerivAt_pow (k + 1) x
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) b, HasDerivAt (fun x : ℝ => -Real.exp (-x)) (Real.exp (-x)) x := by
    intro x _
    have := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    exact this.neg.congr_deriv (by ring)
  have hu' : IntervalIntegrable (fun x : ℝ => ((k + 1 : ℕ) : ℝ) * x ^ k) MeasureTheory.volume 0 b :=
    (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x : ℝ => Real.exp (-x)) MeasureTheory.volume 0 b :=
    (Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _
  have := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [this]
  have h3 : ∫ x in (0:ℝ)..b, ((k + 1 : ℕ) : ℝ) * x ^ k * -Real.exp (-x)
      = -(((k + 1 : ℕ) : ℝ) * ∫ x in (0:ℝ)..b, x ^ k * Real.exp (-x)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  rw [h3]
  simp
  ring

theorem lg_pos (k : ℕ) (b : ℝ) (hb : 0 < b) : 0 < lowerGamma (k + 1) b := by
  unfold lowerGamma
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (((continuous_pow _).mul (Real.continuous_exp.comp continuous_neg))).intervalIntegrable _ _
  · intro x hx
    exact mul_pos (pow_pos hx.1 _) (Real.exp_pos _)
  · exact hb

theorem ffa_slopes (lam T : ℝ) (hlam : 0 < lam) (hT : 0 < T) (k : ℕ) :
    0 < a lam T k ∧ a lam T (k + 1) < a lam T k := by
  have hb : 0 < lam * T := mul_pos hlam hT
  have hf : (0:ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  constructor
  · unfold a
    exact div_pos (lg_pos k _ hb) (mul_pos hlam hf)
  · unfold a
    have hrec := lg_succ k (lam * T)
    have e : k + 1 + 1 = k + 2 := rfl
    rw [e, hrec]
    have hfs : (Nat.factorial (k + 1) : ℝ) = (k + 1) * Nat.factorial k := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfs]
    have hpos : 0 < (lam * T) ^ (k + 1) * Real.exp (-(lam * T)) :=
      mul_pos (pow_pos hb _) (Real.exp_pos _)
    have hk : (0:ℝ) < (k + 1) := by positivity
    rw [div_lt_div_iff₀ (by positivity) (mul_pos hlam hf)]
    nlinarith [mul_pos hpos (mul_pos hlam hf)]


lemma ffa_tangent_nonneg (lam T : ℝ) (hlam : 0 < lam) (hT : 0 < T) (i : WithTop ℕ) (q : ℕ) :
    0 ≤ tangent lam T i (q : ℝ) := by
  induction i using WithTop.recTopCoe with
  | top => simp [tangent, hT.le]
  | coe n =>
    have hapos : ∀ k, 0 < a lam T k := fun k => (ffa_slopes lam T hlam hT k).1
    have hanti : Antitone (a lam T) :=
      antitone_nat_of_succ_le (fun k => (ffa_slopes lam T hlam hT k).2.le)
    have hb : (n : ℝ) * a lam T n ≤ b lam T n := by
      unfold b
      have : ∑ k ∈ Finset.range n, a lam T n ≤ ∑ k ∈ Finset.range n, a lam T k :=
        Finset.sum_le_sum (fun k hk => hanti (Finset.mem_range.1 hk).le)
      simpa using this
    show 0 ≤ a lam T n * ((q : ℝ) - (n : ℝ)) + b lam T n
    have h1 := hapos n
    have h2 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith

lemma ffa_env_nonneg (lam T : ℝ) (hlam : 0 < lam) (hT : 0 < T) (Nf : Finset (WithTop ℕ))
    (hNf : Nf.Nonempty) (q : ℕ) : 0 ≤ envelope lam T Nf hNf (q : ℝ) := by
  unfold envelope
  exact Finset.le_inf' hNf _ (fun i _ => ffa_tangent_nonneg lam T hlam hT i q)

theorem solution {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J]
    (P : J → ℝ) (hP : ∀ j, 0 < P j) (K : ℝ) (lam : S → J → ℝ) (hlam : ∀ s j, 0 < lam s j)
    (T : ℝ) (hT : 0 < T) (Sp : Finset S) (hSp : Sp.Nonempty)
    (Nset : S → J → Finset (WithTop ℕ)) (hNset : ∀ s j, (Nset s j).Nonempty)
    (W : S → ℕ) (I : S → J → ℕ) (sol : MIPSol S J)
    (hopt : MIPOptimal P K lam T Sp Nset W I sol) :
    ∀ j, sol.z j = gTilde (fun s => lam s j) T Sp hSp (fun s => Nset s j) (fun s => hNset s j)
      (fun s => I s j + sol.x s j) := by
  obtain ⟨hfeas, hbest⟩ := hopt
  obtain ⟨h14, h15, h16, h17, h18, h19, h19'⟩ := hfeas
  -- notation
  let q : J → S → ℕ := fun j s => I s j + sol.x s j
  let Y : J → ℝ := fun j => sizeMin (fun s => lam s j) T (fun s => Nset s j) (fun s => hNset s j) Sp hSp (q j)
  let V : S → J → ℝ := fun s j => sizeMin (fun s => lam s j) T (fun s => Nset s j) (fun s => hNset s j)
    (insert s Sp) (Finset.insert_nonempty s Sp) (q j)
  let G : J → ℝ := fun j => gTilde (fun s => lam s j) T Sp hSp (fun s => Nset s j) (fun s => hNset s j) (q j)
  have hG : ∀ j, G j = (∑ s ∈ Sp, lam s j) * Y j + ∑ s ∈ Spᶜ, lam s j * V s j := fun j => rfl
  have hcast : ∀ j s, (q j s : ℝ) = (I s j : ℝ) + (sol.x s j : ℝ) := fun j s => by simp [q]
  have hY0 : ∀ j, 0 ≤ Y j := fun j => by
    apply Finset.le_inf' 
    intro s _
    exact ffa_env_nonneg _ _ (hlam s j) hT _ _ _
  have hV0 : ∀ s j, 0 ≤ V s j := fun s j => by
    apply Finset.le_inf'
    intro s' _
    exact ffa_env_nonneg _ _ (hlam s' j) hT _ _ _
  have hG0 : ∀ j, 0 ≤ G j := fun j => by
    rw [hG]
    apply add_nonneg
    · exact mul_nonneg (Finset.sum_nonneg (fun s _ => (hlam s j).le)) (hY0 j)
    · exact Finset.sum_nonneg (fun s _ => mul_nonneg (hlam s j).le (hV0 s j))
  -- upper bounds for a feasible solution
  have hyle : ∀ j, sol.y j ≤ Y j := fun j => by
    apply Finset.le_inf'
    intro s hs
    unfold envelope
    apply Finset.le_inf'
    intro i hi
    have := h16 j s hs i hi
    rw [hcast]; exact this
  have hvle : ∀ s j, s ∈ Spᶜ → sol.v s j ≤ V s j := fun s j hs => by
    apply Finset.le_inf'
    intro s' hs'
    rcases Finset.mem_insert.1 hs' with rfl | hs'
    · unfold envelope
      apply Finset.le_inf'
      intro i hi
      have := h17 j s' hs i hi
      rw [hcast]; exact this
    · refine le_trans (h18 j s hs) (le_trans (hyle j) ?_)
      exact Finset.inf'_le _ hs'
  have hzle : ∀ j, sol.z j ≤ G j := fun j => by
    rw [hG]
    refine le_trans (h15 j) (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (hyle j) (Finset.sum_nonneg (fun s _ => (hlam s j).le))
    · exact Finset.sum_le_sum (fun s hs => mul_le_mul_of_nonneg_left (hvle s j hs) (hlam s j).le)
  -- the improved solution
  let sol' : MIPSol S J := { x := sol.x, z := G, y := Y, v := V }
  have hfeas' : MIPFeasible lam T Sp Nset W I sol' := by
    refine ⟨h14, fun j => (hG j).le, ?_, ?_, ?_, fun j => ⟨hG0 j, hY0 j⟩, fun j s _ => hV0 s j⟩
    · intro j s hs i hi
      show Y j ≤ _
      rw [← Nat.cast_add]
      change Y j ≤ tangent (lam s j) T i ((q j s : ℝ))
      refine le_trans (Finset.inf'_le _ hs) ?_
      exact Finset.inf'_le _ hi
    · intro j s hs i hi
      show V s j ≤ _
      rw [← Nat.cast_add]
      change V s j ≤ tangent (lam s j) T i ((q j s : ℝ))
      refine le_trans (Finset.inf'_le _ (Finset.mem_insert_self s Sp)) ?_
      exact Finset.inf'_le _ hi
    · intro j s hs
      exact Finset.inf'_mono _ (Finset.subset_insert s Sp) hSp
  have hobj := hbest sol' hfeas'
  unfold mipObjective at hobj
  have hsum : ∑ j, P j * G j ≤ ∑ j, P j * sol.z j := by
    have : (∑ j, P j * G j + K * ∑ s, ((W s : ℝ) - ∑ j, (sol.x s j : ℝ))) ≤
        ∑ j, P j * sol.z j + K * ∑ s, ((W s : ℝ) - ∑ j, (sol.x s j : ℝ)) := hobj
    linarith
  have hzero : ∀ j ∈ Finset.univ, P j * (G j - sol.z j) = 0 := by
    have hle : ∀ j ∈ (Finset.univ : Finset J), 0 ≤ P j * (G j - sol.z j) := fun j _ =>
      mul_nonneg (hP j).le (sub_nonneg.2 (hzle j))
    have hs : ∑ j, P j * (G j - sol.z j) = 0 := by
      apply le_antisymm
      · have : ∑ j, P j * (G j - sol.z j) = ∑ j, P j * G j - ∑ j, P j * sol.z j := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
        linarith
      · exact Finset.sum_nonneg hle
    exact (Finset.sum_eq_zero_iff_of_nonneg hle).1 hs
  intro j
  have := hzero j (Finset.mem_univ j)
  have h2 : G j - sol.z j = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hP j).ne'
    · exact h
  exact (sub_eq_zero.1 h2).symm
