-- Prove2me | solution 1 for FiniteTD.Markov.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T08:41:06.022291+00:00
-- url     : https://prove2.me/submissions/43c352bc-9928-49df-8853-dd3c6f53ebbe

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Theorems.Thm_FiniteTD_Markov_lemma_1
import Theorems.Thm_FiniteTD_Markov_lemma_8
import Theorems.Thm_FiniteTD_Markov_lemma_11

set_option autoImplicit false
open FiniteTD.Markov
open scoped InnerProductSpace

/-! ### Expectations over trajectories -/

theorem t3_pathProb_snoc {S : Type} [Fintype S] (π : S → ℝ) (P : S → S → ℝ) (k : ℕ)
    (w : Fin (k + 1) → S) (s : S) :
    pathProb π P (k + 1) (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S) =
      pathProb π P k w * P (w (Fin.last k)) s := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S) 0 = w 0 :=
    Fin.snoc_apply_zero (α := fun _ => S) s w
  rw [h0]
  simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

theorem t3_pathExp_succ {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (k : ℕ) (F : (Fin (k + 2) → S) → ℝ) :
    pathExp π P (k + 1) F = pathExp π P k (fun w => ∑ s,
      P (w (Fin.last k)) s * F (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S)) := by
  unfold pathExp
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 2) => S)).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  show ∑ s, pathProb π P (k + 1) (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S) *
      F (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S) =
    pathProb π P k w * ∑ s, P (w (Fin.last k)) s * F (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [t3_pathProb_snoc]
  ring

theorem t3_pathExp_zero {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (F : (Fin 1 → S) → ℝ) : pathExp π P 0 F = ∑ a, π a * F (fun _ => a) := by
  unfold pathExp pathProb
  rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
  simp
  rfl

theorem t3_pathExp_const {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (k : ℕ) (c : ℝ) :
    pathExp π P k (fun _ => c) = c := by
  induction k with
  | zero => rw [t3_pathExp_zero, ← Finset.sum_mul, hπ.2.1, one_mul]
  | succ k ih =>
    rw [t3_pathExp_succ]
    have : (fun w : Fin (k + 1) → S => ∑ s, P (w (Fin.last k)) s * c) = fun _ => c := by
      funext w
      rw [← Finset.sum_mul, hP.2, one_mul]
    rw [this, ih]

theorem t3_pathProb_nonneg {S : Type} [Fintype S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (k : ℕ) (w : Fin (k + 1) → S) :
    0 ≤ pathProb π P k w :=
  mul_nonneg (hπ.1 _) (Finset.prod_nonneg fun _ _ => hP.1 _ _)

theorem t3_pathExp_mono {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (k : ℕ) (F G : (Fin (k + 1) → S) → ℝ)
    (h : ∀ w, F w ≤ G w) : pathExp π P k F ≤ pathExp π P k G :=
  Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (t3_pathProb_nonneg π P hP hπ k w)

theorem t3_pathExp_nonneg {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (k : ℕ) (F : (Fin (k + 1) → S) → ℝ)
    (h : ∀ w, 0 ≤ F w) : 0 ≤ pathExp π P k F := by
  have := t3_pathExp_mono π P hP hπ k (fun _ => 0) F h
  rwa [t3_pathExp_const π P hP hπ] at this

theorem t3_pathExp_lin {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (k : ℕ) (A B C : (Fin (k + 1) → S) → ℝ)
    (b c e : ℝ) :
    pathExp π P k (fun w => A w - b * B w + c * C w + e) =
      pathExp π P k A - b * pathExp π P k B + c * pathExp π P k C + e := by
  have he : ∑ w, pathProb π P k w * e = e := t3_pathExp_const π P hP hπ k e
  show ∑ w, pathProb π P k w * (A w - b * B w + c * C w + e) =
    ∑ w, pathProb π P k w * A w - b * ∑ w, pathProb π P k w * B w
      + c * ∑ w, pathProb π P k w * C w + e
  calc ∑ w, pathProb π P k w * (A w - b * B w + c * C w + e)
      = ∑ w, (pathProb π P k w * A w - b * (pathProb π P k w * B w)
          + c * (pathProb π P k w * C w) + pathProb π P k w * e) :=
        Finset.sum_congr rfl fun w _ => by ring
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, Finset.mul_sum, he]

theorem t3_pathExp_sum {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (k : ℕ) (n : ℕ) (F : ℕ → (Fin (k + 1) → S) → ℝ) (c : ℝ) :
    pathExp π P k (fun w => c * ∑ t ∈ Finset.range n, F t w) =
      c * ∑ t ∈ Finset.range n, pathExp π P k (F t) := by
  show ∑ w, pathProb π P k w * (c * ∑ t ∈ Finset.range n, F t w) =
    c * ∑ t ∈ Finset.range n, ∑ w, pathProb π P k w * F t w
  calc ∑ w, pathProb π P k w * (c * ∑ t ∈ Finset.range n, F t w)
      = ∑ w, ∑ t ∈ Finset.range n, c * (pathProb π P k w * F t w) :=
        Finset.sum_congr rfl fun w _ => by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
    _ = ∑ t ∈ Finset.range n, ∑ w, c * (pathProb π P k w * F t w) := Finset.sum_comm
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [Finset.mul_sum]

theorem t3_pathExp_cmul {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (k : ℕ) (F : (Fin (k + 1) → S) → ℝ) (c : ℝ) :
    pathExp π P k (fun w => c * F w) = c * pathExp π P k F := by
  show ∑ w, pathProb π P k w * (c * F w) = c * ∑ w, pathProb π P k w * F w
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-! ### Deterministic facts about projected TD(0) -/

theorem t3_ptd_congr_alpha {S : Type} {d : ℕ} (γ : ℝ) (Rw : S → S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (α α' : ℕ → ℝ) (θ0 : EuclideanSpace ℝ (Fin d))
    (w : ℕ → S) (T : ℕ) (h : ∀ t < T, α t = α' t) :
    ∀ t ≤ T, ptd γ Rw φ R α θ0 w t = ptd γ Rw φ R α' θ0 w t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    show projBall R (ptd γ Rw φ R α θ0 w n +
        α n • tdDir γ Rw φ (ptd γ Rw φ R α θ0 w n) (w n) (w (n + 1))) =
      projBall R (ptd γ Rw φ R α' θ0 w n +
        α' n • tdDir γ Rw φ (ptd γ Rw φ R α' θ0 w n) (w n) (w (n + 1)))
    rw [ih (by omega), h n (by omega)]

theorem t3_jensen {S : Type} [Fintype S] {d : ℕ} (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d))
    (hπ0 : ∀ s, 0 ≤ π s) (T : ℕ) (hT : 1 ≤ T) (x : ℕ → EuclideanSpace ℝ (Fin d)) :
    dNormSq π φ ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t) ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, dNormSq π φ (x t) := by
  unfold dNormSq
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [inner_smul_right, inner_sum]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range T) (f := fun t => ⟪φ s, x t⟫_ℝ)
  rw [Finset.card_range] at hcs
  have key : ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ⟪φ s, x t⟫_ℝ) ^ 2 ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ⟪φ s, x t⟫_ℝ ^ 2 := by
    rw [mul_pow]
    have h1 : ((T : ℝ)⁻¹) ^ 2 * (T : ℝ) = (T : ℝ)⁻¹ := by field_simp
    calc ((T : ℝ)⁻¹) ^ 2 * (∑ t ∈ Finset.range T, ⟪φ s, x t⟫_ℝ) ^ 2
        ≤ ((T : ℝ)⁻¹) ^ 2 * ((T : ℝ) * ∑ t ∈ Finset.range T, ⟪φ s, x t⟫_ℝ ^ 2) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hcs) (by positivity)
      _ = _ := by rw [← mul_assoc, h1]
  calc π s * ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ⟪φ s, x t⟫_ℝ) ^ 2
      ≤ π s * ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ⟪φ s, x t⟫_ℝ ^ 2) :=
        mul_le_mul_of_nonneg_left key (hπ0 s)
    _ = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, π s * ⟪φ s, x t⟫_ℝ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring

theorem t3_avg_sub {d : ℕ} (T : ℕ) (hT : 1 ≤ T) (θstar : EuclideanSpace ℝ (Fin d))
    (x : ℕ → EuclideanSpace ℝ (Fin d)) :
    θstar - (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t =
      (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (θstar - x t) := by
  have hTpos : (T : ℝ) ≠ 0 := by
    have : (0 : ℝ) < T := by exact_mod_cast hT
    exact this.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hTpos, one_smul]

/-- Averaged-iterate bound: E‖V* − V_{θ̄_T}‖²_D ≤ T⁻¹ Σ_{t<T} E‖V* − V_{θ_t}‖²_D. -/
theorem t3_avg_bound {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (α : ℕ → ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (T : ℕ) (hT : 1 ≤ T) :
    pathExp π P T (fun w => dNormSq π φ (θstar - avgIter γ Rw φ R α θ0 T (extendPath w))) ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        pathExp π P T (fun w => dNormSq π φ (θstar - ptd γ Rw φ R α θ0 (extendPath w) t)) := by
  rw [← t3_pathExp_sum]
  refine t3_pathExp_mono π P hP hπ T _ _ fun w => ?_
  unfold avgIter
  rw [t3_avg_sub T hT]
  exact t3_jensen π φ hπ.1 T hT _

/-- Lemma 8 in expectation (equation (eq:mc_basic_rec) in the paper). -/
theorem t3_rec {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (α : ℕ → ℝ)
    (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hstar : gbar π P γ Rw φ θstar = 0) (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R)
    (hα : ∀ t, 0 ≤ α t) (T t : ℕ) :
    pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α θ0 (extendPath w) (t + 1)‖ ^ 2) ≤
      pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α θ0 (extendPath w) t‖ ^ 2)
      - 2 * α t * (1 - γ) *
          pathExp π P T (fun w => dNormSq π φ (θstar - ptd γ Rw φ R α θ0 (extendPath w) t))
      + 2 * α t * pathExp π P T (fun w => zeta π P γ Rw φ θstar
          (ptd γ Rw φ R α θ0 (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
      + α t ^ 2 * (rmax + 2 * R) ^ 2 := by
  rw [← t3_pathExp_lin π P hP hπ]
  exact t3_pathExp_mono π P hP hπ T _ _ fun w =>
    lemma_8 P π Rw rmax γ φ R α θstar θ0 hP hπ hRw hγ0 hγ1 hφ hstar hR hθ0 hα (extendPath w) t

/-- ω‖x‖² ≤ ‖V_x‖²_D (from Lemma 1). -/
theorem t3_strong {S : Type} [Fintype S] {d : ℕ} [NeZero d]
    (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ)
    (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω) (x : EuclideanSpace ℝ (Fin d)) :
    ω * ‖x‖ ^ 2 ≤ dNormSq π φ x := by
  have h := (lemma_1 π φ ω hπ0 hπ1 hφ hω hω0 x).1
  have hD : 0 ≤ dNormSq π φ x := Finset.sum_nonneg fun s _ => mul_nonneg (hπ0 s) (sq_nonneg _)
  have h2 := pow_le_pow_left₀ (by positivity) h 2
  rwa [mul_pow, Real.sq_sqrt hω0.le, Real.sq_sqrt hD] at h2

/-! ### Elementary sums for part (c) -/

theorem t3_count (τ T : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ t ∈ Finset.range T, (if 1 ≤ t ∧ t ≤ τ then c else 0) ≤ τ * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hc
  have : (Finset.filter (fun t => 1 ≤ t ∧ t ≤ τ) (Finset.range T)) ⊆ Finset.Icc 1 τ := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    simp only [Finset.mem_Icc]
    exact ht.2
  have h2 := Finset.card_le_card this
  rw [Nat.card_Icc] at h2
  exact_mod_cast (show _ ≤ τ by omega)

theorem t3_shift (τ T : ℕ) (α : ℕ → ℝ) (hα : ∀ t, 0 ≤ α t) :
    ∑ t ∈ Finset.range T, (if τ < t then α (t - τ) else 0) ≤ ∑ t ∈ Finset.range T, α t := by
  rcases Nat.lt_or_ge (τ + 1) T with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, T = (τ + 1) + k := ⟨T - (τ + 1), by omega⟩
    rw [Finset.sum_range_add]
    have h0 : ∑ t ∈ Finset.range (τ + 1), (if τ < t then α (t - τ) else 0) = 0 :=
      Finset.sum_eq_zero fun t ht => by
        rw [Finset.mem_range] at ht
        rw [if_neg (by omega)]
    rw [h0, zero_add]
    have h1 : ∑ x ∈ Finset.range k, (if τ < τ + 1 + x then α (τ + 1 + x - τ) else 0) =
        ∑ x ∈ Finset.range k, α (x + 1) :=
      Finset.sum_congr rfl fun x _ => by
        rw [if_pos (by omega)]
        congr 1
        omega
    rw [h1]
    have h2 : ∑ x ∈ Finset.range (k + 1), α x ≤ ∑ x ∈ Finset.range (τ + 1 + k), α x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        fun i _ _ => hα i
    rw [Finset.sum_range_succ'] at h2
    linarith [hα 0]
  · have h0 : ∑ t ∈ Finset.range T, (if τ < t then α (t - τ) else 0) = 0 :=
      Finset.sum_eq_zero fun t ht => by
        rw [Finset.mem_range] at ht
        rw [if_neg (by omega)]
    rw [h0]
    exact Finset.sum_nonneg fun i _ => hα i

theorem t3_harmonic (T : ℕ) :
    ∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1) ≤ 1 + Real.log T := by
  have h := harmonic_le_one_add_log T
  have he : ((harmonic T : ℚ) : ℝ) = ∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1) := by
    unfold harmonic
    push_cast
    exact Finset.sum_congr rfl fun t _ => by rw [one_div]
  rw [← he]
  exact h

theorem t3_c_arith (G τ A SD SZ W u ω L T : ℝ) (hu : 0 < u) (hω : 0 < ω) (hT : 0 < T)
    (hfin : SD + W ≤ 2 / u * SZ + G ^ 2 / u * A) (hW : 0 ≤ W)
    (hZ : SZ ≤ G ^ 2 * (4 + 12 * τ) * A) (hA : A ≤ L / (ω * u)) (hτ : 0 ≤ τ) :
    T⁻¹ * SD ≤ G ^ 2 * (9 + 24 * τ) / (T * u ^ 2 * ω) * L := by
  have h0 := mul_le_mul_of_nonneg_left hZ (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hu.le)
  have e1 : 2 / u * (G ^ 2 * (4 + 12 * τ) * A) + G ^ 2 / u * A
      = G ^ 2 * (9 + 24 * τ) * A / u := by ring
  have h1 : SD ≤ G ^ 2 * (9 + 24 * τ) * A / u := by linarith
  have hc : 0 ≤ G ^ 2 * (9 + 24 * τ) := by positivity
  have h2 : G ^ 2 * (9 + 24 * τ) * A / u ≤ G ^ 2 * (9 + 24 * τ) * (L / (ω * u)) / u :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA hc) hu.le
  have h3 : T⁻¹ * SD ≤ T⁻¹ * (G ^ 2 * (9 + 24 * τ) * (L / (ω * u)) / u) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (inv_nonneg.mpr hT.le)
  have e2 : T⁻¹ * (G ^ 2 * (9 + 24 * τ) * (L / (ω * u)) / u)
      = G ^ 2 * (9 + 24 * τ) / (T * u ^ 2 * ω) * L := by
    field_simp
  linarith

/-! ### Main theorem -/

set_option maxHeartbeats 1000000 in
theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {d : ℕ} [NeZero d]
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω m ρ R : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hstar : gbar π P γ Rw φ θstar = 0) (hA1 : Assumption1 P π m ρ)
    (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) :
    -- (a) constant step size 1/√T, averaged iterate
    (∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = 1 / Real.sqrt T) →
      pathExp π P T (fun w => dNormSq π φ (θstar - avgIter γ Rw φ R α θ0 T (extendPath w))) ≤
        (‖θstar - θ0‖ ^ 2 + (rmax + 2 * R) ^ 2 * (9 + 12 * (tauMix m ρ (1 / Real.sqrt T) : ℝ)))
          / (2 * Real.sqrt T * (1 - γ))) ∧
    -- (b) constant step size α₀ < 1/(2ω(1-γ)), last iterate
    (∀ α0 : ℝ, 0 < α0 → α0 < 1 / (2 * ω * (1 - γ)) →
      ∀ T : ℕ, ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = α0) →
      pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α θ0 (extendPath w) T‖ ^ 2) ≤
        Real.exp (-2 * α0 * (1 - γ) * ω * T) * ‖θstar - θ0‖ ^ 2
          + α0 * ((rmax + 2 * R) ^ 2 * (9 + 12 * (tauMix m ρ α0 : ℝ)) / (2 * (1 - γ) * ω))) ∧
    -- (c) decaying step size 1/(ω(t+1)(1-γ)), averaged iterate
    (∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ, (∀ t : ℕ, α t = 1 / (ω * ((t : ℝ) + 1) * (1 - γ))) →
      pathExp π P T (fun w => dNormSq π φ (θstar - avgIter γ Rw φ R α θ0 T (extendPath w))) ≤
        (rmax + 2 * R) ^ 2 * (9 + 24 * (tauMix m ρ (α T) : ℝ)) / (T * (1 - γ) ^ 2 * ω)
          * (1 + Real.log T)) := by
  have hu : 0 < 1 - γ := by linarith
  set G := rmax + 2 * R with hG
  -- E‖θ* − θ_t‖² is nonnegative
  have he_nn : ∀ (α : ℕ → ℝ) (T t : ℕ),
      0 ≤ pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α θ0 (extendPath w) t‖ ^ 2) :=
    fun α T t => t3_pathExp_nonneg π P hP hπ T _ fun w => sq_nonneg _
  have he0 : ∀ (α : ℕ → ℝ) (T : ℕ),
      pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α θ0 (extendPath w) 0‖ ^ 2)
        = ‖θstar - θ0‖ ^ 2 := fun α T => by
    show pathExp π P T (fun _ => ‖θstar - θ0‖ ^ 2) = _
    exact t3_pathExp_const π P hP hπ T _
  have hDe : ∀ (α : ℕ → ℝ) (T t : ℕ),
      ω * pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α θ0 (extendPath w) t‖ ^ 2) ≤
        pathExp π P T (fun w => dNormSq π φ (θstar - ptd γ Rw φ R α θ0 (extendPath w) t)) := by
    intro α T t
    rw [← t3_pathExp_cmul]
    exact t3_pathExp_mono π P hP hπ T _ _ fun w =>
      t3_strong π φ ω hπ.1 hπ.2.1 hφ hω hω0 _
  refine ⟨?_, ?_, ?_⟩
  -- Part (a)
  · intro T hT α hα
    set a : ℝ := 1 / Real.sqrt T with ha
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
    have hapos : 0 < a := by positivity
    have ha2 : (T : ℝ) * a ^ 2 = 1 := by
      rw [ha, div_pow, Real.sq_sqrt hTpos.le]; field_simp
    set α' : ℕ → ℝ := fun _ => a with hα'
    have hcongr : ∀ w : ℕ → S, ∀ t ≤ T,
        ptd γ Rw φ R α θ0 w t = ptd γ Rw φ R α' θ0 w t :=
      fun w => t3_ptd_congr_alpha γ Rw φ R α α' θ0 w T fun t ht => hα t ht.le
    have havg : ∀ w : ℕ → S, avgIter γ Rw φ R α θ0 T w = avgIter γ Rw φ R α' θ0 T w := by
      intro w
      unfold avgIter
      congr 1
      exact Finset.sum_congr rfl fun t ht => hcongr w t (Finset.mem_range.mp ht).le
    simp only [havg]
    set τ := tauMix m ρ a with hτ
    -- notation
    set e : ℕ → ℝ := fun t =>
      pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α' θ0 (extendPath w) t‖ ^ 2) with he
    set D : ℕ → ℝ := fun t =>
      pathExp π P T (fun w => dNormSq π φ (θstar - ptd γ Rw φ R α' θ0 (extendPath w) t)) with hD
    set Z : ℕ → ℝ := fun t => pathExp π P T (fun w => zeta π P γ Rw φ θstar
          (ptd γ Rw φ R α' θ0 (extendPath w) t) (extendPath w t) (extendPath w (t + 1))) with hZ
    have hrec : ∀ t, e (t + 1) ≤ e t - 2 * a * (1 - γ) * D t + 2 * a * Z t + a ^ 2 * G ^ 2 :=
      fun t => t3_rec P π Rw rmax γ φ R α' θstar θ0 hP hπ hRw hγ0 hγ1 hφ hstar hR hθ0
        (fun _ => hapos.le) T t
    have hZb : ∀ t < T, Z t ≤ G ^ 2 * (4 + 6 * (τ : ℝ)) * a := fun t ht =>
      (lemma_11 P π Rw rmax γ φ m ρ R θstar θ0 hP hπ hRw hγ0 hγ1 hφ hstar hA1 hR hθ0 T α'
        (fun _ _ _ _ => le_rfl) hapos t ht).1
    have hind : ∀ n ≤ T, e n + 2 * a * (1 - γ) * ∑ t ∈ Finset.range n, D t ≤
        e 0 + n * (a ^ 2 * G ^ 2 * (9 + 12 * (τ : ℝ))) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have h1 := ih (by omega)
        have h2 := hrec n
        have h3 := mul_le_mul_of_nonneg_left (hZb n (by omega)) (by positivity : (0:ℝ) ≤ 2 * a)
        rw [Finset.sum_range_succ]
        push_cast
        nlinarith
    have hfin := hind T le_rfl
    have heT : 0 ≤ e T := he_nn α' T T
    have he0' : e 0 = ‖θstar - θ0‖ ^ 2 := he0 α' T
    have hsum : 2 * a * (1 - γ) * ∑ t ∈ Finset.range T, D t ≤
        ‖θstar - θ0‖ ^ 2 + G ^ 2 * (9 + 12 * (τ : ℝ)) := by
      have : (T : ℝ) * (a ^ 2 * G ^ 2 * (9 + 12 * (τ : ℝ))) = G ^ 2 * (9 + 12 * (τ : ℝ)) := by
        rw [← mul_assoc, ← mul_assoc, ha2, one_mul]
      linarith
    calc _ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, D t :=
          t3_avg_bound P π Rw γ φ R α' θstar θ0 hP hπ T hT
      _ ≤ _ := by
          rw [le_div_iff₀ (by positivity)]
          have hsT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hTpos.le
          have hka : (T : ℝ)⁻¹ * (2 * Real.sqrt T * (1 - γ)) = 2 * a * (1 - γ) := by
            have hinv : (T : ℝ)⁻¹ = (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ := by
              rw [← mul_inv, hsT]
            rw [hinv, ha]; field_simp
          calc ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, D t) * (2 * Real.sqrt T * (1 - γ))
              = 2 * a * (1 - γ) * ∑ t ∈ Finset.range T, D t := by
                rw [← hka]; ring
            _ ≤ _ := hsum
  -- Part (b)
  · intro α0 hα0 hα0' T α hα
    set α' : ℕ → ℝ := fun _ => α0 with hα'
    have hcongr : ∀ w : ℕ → S, ∀ t ≤ T,
        ptd γ Rw φ R α θ0 w t = ptd γ Rw φ R α' θ0 w t :=
      fun w => t3_ptd_congr_alpha γ Rw φ R α α' θ0 w T fun t ht => hα t ht.le
    simp only [hcongr _ T le_rfl]
    set τ := tauMix m ρ α0 with hτ
    set e : ℕ → ℝ := fun t =>
      pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α' θ0 (extendPath w) t‖ ^ 2) with he
    set c : ℝ := 1 - 2 * α0 * (1 - γ) * ω with hc
    set B : ℝ := α0 ^ 2 * G ^ 2 * (9 + 12 * (τ : ℝ)) with hB
    have hx : 2 * α0 * (1 - γ) * ω < 1 := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * ω * (1 - γ))).mp hα0'
      linarith
    have hc0 : 0 ≤ c := by linarith
    have hc1 : c < 1 := by
      have : 0 < 2 * α0 * (1 - γ) * ω := by positivity
      linarith
    have hB0 : 0 ≤ B := by positivity
    have hstep : ∀ t < T, e (t + 1) ≤ c * e t + B := by
      intro t ht
      have h1 := t3_rec P π Rw rmax γ φ R α' θstar θ0 hP hπ hRw hγ0 hγ1 hφ hstar hR hθ0
        (fun _ => hα0.le) T t
      have h2 := (lemma_11 P π Rw rmax γ φ m ρ R θstar θ0 hP hπ hRw hγ0 hγ1 hφ hstar hA1 hR hθ0
        T α' (fun _ _ _ _ => le_rfl) hα0 t ht).1
      have h3 := hDe α' T t
      have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * α0)
      have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2 * α0 * (1 - γ))
      simp only [hα'] at h1 h4
      simp only [he, hc, hB]
      nlinarith
    have hind : ∀ n ≤ T, e n ≤ c ^ n * e 0 + B * ∑ k ∈ Finset.range n, c ^ k := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have h1 := ih (by omega)
        have h2 := hstep n (by omega)
        have hg : ∑ k ∈ Finset.range (n + 1), c ^ k = c * ∑ k ∈ Finset.range n, c ^ k + 1 := by
          rw [Finset.sum_range_succ', Finset.mul_sum]
          simp [pow_succ, mul_comm]
        rw [hg, pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left h1 hc0]
    have hfin := hind T le_rfl
    have hgeom : B * ∑ k ∈ Finset.range T, c ^ k ≤ B / (1 - c) := by
      have hgs := geom_sum_mul c T
      have hpos : 0 < 1 - c := by linarith
      have hle : ∑ k ∈ Finset.range T, c ^ k ≤ 1 / (1 - c) := by
        rw [le_div_iff₀ hpos]
        have : 0 ≤ c ^ T := pow_nonneg hc0 T
        nlinarith
      calc B * ∑ k ∈ Finset.range T, c ^ k ≤ B * (1 / (1 - c)) := mul_le_mul_of_nonneg_left hle hB0
        _ = B / (1 - c) := by ring
    have hexp : c ^ T ≤ Real.exp (-2 * α0 * (1 - γ) * ω * T) := by
      have h1 : c ≤ Real.exp (-(2 * α0 * (1 - γ) * ω)) := by
        have := Real.add_one_le_exp (-(2 * α0 * (1 - γ) * ω))
        linarith
      calc c ^ T ≤ Real.exp (-(2 * α0 * (1 - γ) * ω)) ^ T := pow_le_pow_left₀ hc0 h1 T
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
    have he0' : e 0 = ‖θstar - θ0‖ ^ 2 := he0 α' T
    have hBc : B / (1 - c) = α0 * (G ^ 2 * (9 + 12 * (τ : ℝ)) / (2 * (1 - γ) * ω)) := by
      rw [hB, hc]
      field_simp
      ring
    rw [← hBc]
    have := mul_le_mul_of_nonneg_right hexp (sq_nonneg ‖θstar - θ0‖)
    show e T ≤ _
    rw [he0'] at hfin
    linarith
  -- Part (c)
  · intro T hT α hα
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have hαpos : ∀ t, 0 < α t := fun t => by rw [hα]; positivity
    have hαmono : ∀ i j, i ≤ j → j ≤ T → α j ≤ α i := by
      intro i j hij _
      rw [hα, hα]
      apply one_div_le_one_div_of_le (by positivity)
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      have := mul_le_mul_of_nonneg_left this hω0.le
      nlinarith
    set τ := tauMix m ρ (α T) with hτ
    set e : ℕ → ℝ := fun t =>
      pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α θ0 (extendPath w) t‖ ^ 2) with he
    set D : ℕ → ℝ := fun t =>
      pathExp π P T (fun w => dNormSq π φ (θstar - ptd γ Rw φ R α θ0 (extendPath w) t)) with hD
    set Z : ℕ → ℝ := fun t => pathExp π P T (fun w => zeta π P γ Rw φ θstar
          (ptd γ Rw φ R α θ0 (extendPath w) t) (extendPath w t) (extendPath w (t + 1))) with hZ
    set A : ℝ := ∑ t ∈ Finset.range T, α t with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun t _ => (hαpos t).le
    -- per-step inequality
    have hstep : ∀ t, D t ≤ ω * t * e t - ω * (t + 1) * e (t + 1)
        + 2 * Z t / (1 - γ) + α t * G ^ 2 / (1 - γ) := by
      intro t
      have hrec := t3_rec P π Rw rmax γ φ R α θstar θ0 hP hπ hRw hγ0 hγ1 hφ hstar hR hθ0
        (fun t => (hαpos t).le) T t
      have hDe' := hDe α T t
      set q : ℝ := ω * ((t : ℝ) + 1) with hq
      have hqpos : 0 < q := by positivity
      have hqa : q * α t * (1 - γ) = 1 := by rw [hα, hq]; field_simp
      have hqa' : q * α t = 1 / (1 - γ) := by
        rw [eq_div_iff hu.ne']; linarith [hqa]
      have h1 := mul_le_mul_of_nonneg_left hrec hqpos.le
      have e1 : q * (2 * α t * (1 - γ) * D t) = 2 * D t := by
        rw [show q * (2 * α t * (1 - γ) * D t) = 2 * D t * (q * α t * (1 - γ)) by ring, hqa,
          mul_one]
      have e2 : q * (2 * α t * Z t) = 2 * Z t / (1 - γ) := by
        rw [show q * (2 * α t * Z t) = 2 * Z t * (q * α t) by ring, hqa']; ring
      have e3 : q * (α t ^ 2 * G ^ 2) = α t * G ^ 2 / (1 - γ) := by
        rw [show q * (α t ^ 2 * G ^ 2) = α t * G ^ 2 * (q * α t) by ring, hqa']; ring
      have e4 : q * (e t - 2 * α t * (1 - γ) * D t + 2 * α t * Z t + α t ^ 2 * G ^ 2)
          = q * e t - q * (2 * α t * (1 - γ) * D t) + q * (2 * α t * Z t)
            + q * (α t ^ 2 * G ^ 2) := by ring
      rw [e4, e1, e2, e3] at h1
      have hqt : q = ω * t + ω := by rw [hq]; ring
      simp only [he, hD, hZ] at h1 hDe' ⊢
      rw [hqt] at h1
      nlinarith
    -- telescoped sum
    have hind : ∀ n ≤ T, ∑ t ∈ Finset.range n, D t + ω * n * e n ≤
        2 / (1 - γ) * ∑ t ∈ Finset.range n, Z t
          + G ^ 2 / (1 - γ) * ∑ t ∈ Finset.range n, α t := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have h1 := ih (by omega)
        have h2 := hstep n
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        push_cast
        have e1 : 2 / (1 - γ) * Z n = 2 * Z n / (1 - γ) := by ring
        have e2 : G ^ 2 / (1 - γ) * α n = α n * G ^ 2 / (1 - γ) := by ring
        nlinarith
    have hfin := hind T le_rfl
    have heT : 0 ≤ ω * T * e T := by
      have := he_nn α T T
      positivity
    -- bound on the sum of gradient biases
    have hZsum : ∑ t ∈ Finset.range T, Z t ≤ G ^ 2 * (4 + 12 * (τ : ℝ)) * A := by
      have hpt : ∀ t ∈ Finset.range T, Z t ≤
          (if 1 ≤ t ∧ t ≤ τ then 6 * G ^ 2 * A else 0)
            + G ^ 2 * (4 + 6 * (τ : ℝ)) * (if τ < t then α (t - τ) else 0) := by
        intro t ht
        rw [Finset.mem_range] at ht
        obtain ⟨hb1, hb2⟩ := lemma_11 P π Rw rmax γ φ m ρ R θstar θ0 hP hπ hRw hγ0 hγ1 hφ hstar
          hA1 hR hθ0 T α hαmono (hαpos T) t ht
        by_cases h0 : t = 0
        · subst h0
          simp only [Finset.range_zero, Finset.sum_empty, mul_zero] at hb2
          have : ¬ (1 ≤ 0 ∧ 0 ≤ τ) := by omega
          rw [if_neg this, zero_add]
          split_ifs
          · have := (hαpos (0 - τ)).le
            have : 0 ≤ G ^ 2 * (4 + 6 * (τ : ℝ)) * α (0 - τ) := by positivity
            linarith
          · simp only [mul_zero]; exact hb2
        · by_cases htτ : t ≤ τ
          · rw [if_pos ⟨by omega, htτ⟩, if_neg (by omega), mul_zero, add_zero]
            have hs : ∑ i ∈ Finset.range t, α i ≤ A :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht.le)
                fun i _ _ => (hαpos i).le
            have : 6 * G ^ 2 * ∑ i ∈ Finset.range t, α i ≤ 6 * G ^ 2 * A :=
              mul_le_mul_of_nonneg_left hs (by positivity)
            linarith
          · rw [if_neg (by omega), if_pos (by omega), zero_add]
            exact hb1
      calc ∑ t ∈ Finset.range T, Z t
          ≤ ∑ t ∈ Finset.range T, ((if 1 ≤ t ∧ t ≤ τ then 6 * G ^ 2 * A else 0)
            + G ^ 2 * (4 + 6 * (τ : ℝ)) * (if τ < t then α (t - τ) else 0)) :=
            Finset.sum_le_sum hpt
        _ = ∑ t ∈ Finset.range T, (if 1 ≤ t ∧ t ≤ τ then 6 * G ^ 2 * A else 0)
            + G ^ 2 * (4 + 6 * (τ : ℝ)) *
              ∑ t ∈ Finset.range T, (if τ < t then α (t - τ) else 0) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ τ * (6 * G ^ 2 * A) + G ^ 2 * (4 + 6 * (τ : ℝ)) * A := by
            gcongr
            · exact t3_count τ T _ (by positivity)
            · exact t3_shift τ T α fun t => (hαpos t).le
        _ = G ^ 2 * (4 + 12 * (τ : ℝ)) * A := by ring
    -- bound on the sum of step sizes
    have hAb : A ≤ (1 + Real.log T) / (ω * (1 - γ)) := by
      have hh := t3_harmonic T
      have : A = (1 / (ω * (1 - γ))) * ∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1) := by
        rw [hA, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hα]
        field_simp
      rw [this]
      calc 1 / (ω * (1 - γ)) * ∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1)
          ≤ 1 / (ω * (1 - γ)) * (1 + Real.log T) :=
            mul_le_mul_of_nonneg_left hh (div_nonneg zero_le_one (mul_pos hω0 hu).le)
        _ = _ := by ring
    exact le_trans (t3_avg_bound P π Rw γ φ R α θstar θ0 hP hπ T hT)
      (t3_c_arith G τ A _ _ _ (1 - γ) ω (1 + Real.log T) T hu hω0 hTpos hfin heT hZsum hAb
        (Nat.cast_nonneg τ))
