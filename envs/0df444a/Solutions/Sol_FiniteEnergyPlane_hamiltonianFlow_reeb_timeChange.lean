-- Prove2me | solution 1 for FiniteEnergyPlane.hamiltonianFlow_reeb_timeChange
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T17:30:59.357343+00:00
-- url     : https://prove2.me/submissions/37d99f3a-ca4f-45fc-b4c0-f27a78edb090

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics

open FiniteEnergyPlane
open Set Filter Topology Metric
open scoped NNReal
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open scoped ContDiff Topology in
open scoped ContDiff Topology
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real NNReal

namespace AsymptoticOperator

/-- For a continuous family `B : ℝ → (E →L[ℝ] E)` of bounded operators on a real Banach space
and any initial value `x₀`, the linear equation `x' = B(t) x` has exactly one solution
`x : ℝ → E` defined on all of `ℝ` with `x 0 = x₀`. -/
theorem linearODE_existsUnique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : E) :
    ∃! x : ℝ → E, x 0 = x₀ ∧ ∀ t, HasDerivAt x (B t (x t)) t := by
  -- bounds on compact intervals
  have bound : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ‖B t‖ ≤ C := by
    intro a b
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hB.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun t ht => (hC t ht).trans (le_max_left _ _)⟩
  -- uniqueness on open intervals
  have U : ∀ (a b t₀ : ℝ) (f g : ℝ → E), t₀ ∈ Ioo a b →
      (∀ t ∈ Ioo a b, HasDerivAt f (B t (f t)) t) →
      (∀ t ∈ Ioo a b, HasDerivAt g (B t (g t)) t) → f t₀ = g t₀ → EqOn f g (Ioo a b) := by
    intro a b t₀ f g ht hf hg heq
    obtain ⟨C, hC0, hC⟩ := bound a b
    refine ODE_solution_unique_of_mem_Ioo (v := fun t x => B t x) (s := fun _ => univ)
      (K := ⟨C, hC0⟩) (fun t ht' => ?_) ht (fun t ht' => ⟨hf t ht', trivial⟩)
      (fun t ht' => ⟨hg t ht', trivial⟩) heq
    refine ((B t).lipschitz.weaken ?_).lipschitzOnWith
    change ‖B t‖ ≤ C
    exact hC t (Ioo_subset_Icc_self ht')
  -- local existence with a uniform step on bounded sets of centres
  have L : ∀ T : ℝ, ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ ∀ s ∈ Icc (-T) T, ∀ x : E, ∃ y : ℝ → E, y s = x ∧
      ∀ t ∈ Ioo (s - h) (s + h), HasDerivAt y (B t (y t)) t := by
    intro T
    obtain ⟨C, hC0, hC⟩ := bound (-T - 1) (T + 1)
    refine ⟨1 / (2 * C + 2), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]; linarith
    intro s hs x
    set h := 1 / (2 * C + 2) with hh
    have hpos : 0 < h := by positivity
    have hh1 : h ≤ 1 := by rw [hh, div_le_one (by positivity)]; linarith
    have hs0 : s ∈ Icc (s - h) (s + h) := ⟨by linarith, by linarith⟩
    have hsub : Icc (s - h) (s + h) ⊆ Icc (-T - 1) (T + 1) := by
      intro t ht; exact ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
    have hPL : IsPicardLindelof (fun t y => B t y) (⟨s, hs0⟩ : Icc (s - h) (s + h)) x
        ⟨‖x‖ + 1, by positivity⟩ 0 ⟨C * (2 * ‖x‖ + 1), by positivity⟩ ⟨C, hC0⟩ := by
      refine ⟨fun t ht => ?_, fun y _ => ?_, fun t ht y hy => ?_, ?_⟩
      · refine ((B t).lipschitz.weaken ?_).lipschitzOnWith
        change ‖B t‖ ≤ C
        exact hC t (hsub ht)
      · exact ((hB.clm_apply continuous_const).continuousOn)
      · change ‖B t y‖ ≤ C * (2 * ‖x‖ + 1)
        have hy' : ‖y‖ ≤ 2 * ‖x‖ + 1 := by
          have h3 : dist y x ≤ ‖x‖ + 1 := mem_closedBall.mp hy
          have h2 := norm_le_insert' y x
          rw [← dist_eq_norm] at h2
          linarith
        calc ‖B t y‖ ≤ ‖B t‖ * ‖y‖ := (B t).le_opNorm y
          _ ≤ C * (2 * ‖x‖ + 1) :=
            mul_le_mul (hC t (hsub ht)) hy' (norm_nonneg _) hC0
      · simp only [NNReal.coe_mk]
        have hm : max (s + h - s) (s - (s - h)) = h := by
          rw [show s + h - s = h by ring, show s - (s - h) = h by ring, max_self]
        rw [hm, hh]
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        have e0 : ((0 : ℝ≥0) : ℝ) = 0 := rfl
        rw [e0]
        change C * (2 * ‖x‖ + 1) ≤ (‖x‖ + 1 - 0) * (2 * C + 2)
        nlinarith [norm_nonneg x]
    obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨α, hα0, fun t ht => ?_⟩
    exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- gluing two solutions that agree on an overlap
  have G : ∀ (a b c d : ℝ) (y z : ℝ → E), a < b → c < b → b ≤ d →
      (∀ t ∈ Ioo a b, HasDerivAt y (B t (y t)) t) →
      (∀ t ∈ Ioo c d, HasDerivAt z (B t (z t)) t) → EqOn y z (Ioo (max a c) b) →
      ∃ w : ℝ → E, (∀ t ∈ Ioo a d, HasDerivAt w (B t (w t)) t) ∧ EqOn w y (Ioo a b) ∧
        EqOn w z (Ioo (max a c) d) := by
    intro a b c d y z hab hcb hbd hy hz hyz
    refine ⟨fun t => if t < b then y t else z t, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · by_cases htb : t < b
      · have hev : (fun t => if t < b then y t else z t) =ᶠ[𝓝 t] y := by
          filter_upwards [Iio_mem_nhds htb] with u hu
          simp [show u < b from hu]
        have := (hy t ⟨ht.1, htb⟩).congr_of_eventuallyEq hev
        simpa [htb] using this
      · have hct : c < t := lt_of_lt_of_le hcb (not_lt.mp htb)
        have hev : (fun t => if t < b then y t else z t) =ᶠ[𝓝 t] z := by
          filter_upwards [Ioi_mem_nhds (show max a c < t from max_lt ht.1 hct)] with u hu
          by_cases hub : u < b
          · simp only [hub, if_true]; exact hyz ⟨hu, hub⟩
          · simp [hub]
        have := (hz t ⟨hct, ht.2⟩).congr_of_eventuallyEq hev
        simpa [htb] using this
    · simp [ht.2]
    · by_cases htb : t < b
      · simp only [htb, if_true]; exact hyz ⟨ht.1, htb⟩
      · simp [htb]
  -- existence on every symmetric interval
  have Ex : ∀ T : ℝ, ∃ y : ℝ → E, y 0 = x₀ ∧ ∀ t ∈ Ioo (-T) T, HasDerivAt y (B t (y t)) t := by
    intro T
    obtain ⟨h, hpos, hh1, hloc⟩ := L (|T| + 1)
    have P : ∀ N : ℕ, (N : ℝ) * (h / 2) ≤ |T| + 1 → ∃ y : ℝ → E, y 0 = x₀ ∧
        ∀ t ∈ Ioo (-((N + 1) * (h / 2))) ((N + 1) * (h / 2)), HasDerivAt y (B t (y t)) t := by
      intro N
      induction N with
      | zero =>
        intro _
        obtain ⟨y, hy0, hy⟩ := hloc 0 ⟨by linarith [abs_nonneg T], by linarith [abs_nonneg T]⟩ x₀
        refine ⟨y, hy0, fun t ht => hy t ⟨?_, ?_⟩⟩
        · simp at ht; linarith [ht.1]
        · simp at ht; linarith [ht.2]
      | succ N ih =>
        intro hN
        push_cast at hN
        obtain ⟨y, hy0, hy⟩ := ih (by nlinarith)
        set r : ℝ := (N + 1) * (h / 2) with hr
        have hr0 : h / 2 ≤ r := by rw [hr]; nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
        set s : ℝ := r - h / 2 with hs
        have hs0 : 0 ≤ s := by linarith
        have hsT : s ≤ |T| + 1 := by rw [hs, hr]; nlinarith
        -- right extension
        obtain ⟨z, hz0, hz⟩ := hloc s ⟨by linarith [abs_nonneg T], hsT⟩ (y s)
        have hyz : EqOn y z (Ioo (max (-r) (s - h)) r) :=
          U _ _ s y z ⟨max_lt (by linarith) (by linarith), by linarith⟩
            (fun t ht => hy t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩)
            (fun t ht => hz t ⟨(le_max_right _ _).trans_lt ht.1, by linarith [ht.2]⟩) hz0.symm
        obtain ⟨w, hw, hwy, -⟩ := G (-r) r (s - h) (s + h) y z (by linarith) (by linarith)
          (by linarith) hy hz hyz
        -- left extension
        have hsT' : -s ∈ Icc (-(|T| + 1)) (|T| + 1) := ⟨by linarith, by linarith⟩
        obtain ⟨z', hz'0, hz'⟩ := hloc (-s) hsT' (w (-s))
        have hz'w : EqOn z' w (Ioo (max (-s - h) (-r)) (-s + h)) :=
          U _ _ (-s) z' w ⟨max_lt (by linarith) (by linarith), by linarith⟩
            (fun t ht => hz' t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩)
            (fun t ht => hw t ⟨(le_max_right _ _).trans_lt ht.1, by linarith [ht.2]⟩) hz'0
        obtain ⟨w', hw', -, hw'w⟩ := G (-s - h) (-s + h) (-r) (s + h) z' w (by linarith)
          (by linarith) (by linarith) hz' hw hz'w
        refine ⟨w', ?_, fun t ht => hw' t ⟨?_, ?_⟩⟩
        · rw [hw'w ⟨max_lt (by linarith) (by linarith), by linarith⟩,
            hwy ⟨by linarith, by linarith⟩, hy0]
        · have := ht.1; push_cast at this; linarith
        · have := ht.2; push_cast at this; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * (|T| + 1) / h)
    -- choose the least admissible step count
    classical
    let N₀ := Nat.find (⟨N, hN⟩ : ∃ N : ℕ, 2 * (|T| + 1) / h < N)
    have hN₀ : 2 * (|T| + 1) / h < N₀ := Nat.find_spec (⟨N, hN⟩ : ∃ N : ℕ, 2 * (|T| + 1) / h < N)
    have hN₀pos : 0 < N₀ := by
      have : (0 : ℝ) < N₀ := lt_of_le_of_lt (by positivity) hN₀
      exact_mod_cast this
    obtain ⟨M, hM⟩ : ∃ M, N₀ = M + 1 := ⟨N₀ - 1, by omega⟩
    have hMle : ¬ (2 * (|T| + 1) / h < M) := Nat.find_min _ (by omega : M < N₀)
    push_neg at hMle
    have hMb : (M : ℝ) * (h / 2) ≤ |T| + 1 := by
      rw [le_div_iff₀ hpos] at hMle; linarith
    obtain ⟨y, hy0, hy⟩ := P M hMb
    refine ⟨y, hy0, fun t ht => hy t ⟨?_, ?_⟩⟩
    · have h1 : 2 * (|T| + 1) < (M + 1 : ℝ) * h := by
        have := hN₀; rw [hM, div_lt_iff₀ hpos] at this; push_cast at this; linarith
      have := ht.1; have := le_abs_self T; nlinarith
    · have h1 : 2 * (|T| + 1) < (M + 1 : ℝ) * h := by
        have := hN₀; rw [hM, div_lt_iff₀ hpos] at this; push_cast at this; linarith
      have := ht.2; have := le_abs_self T; nlinarith
  choose Y hY0 hY using Ex
  -- global solution
  have agree : ∀ T₁ T₂ u, |u| < T₁ → |u| < T₂ → Y T₁ u = Y T₂ u := by
    intro T₁ T₂ u h1 h2
    have hm : |u| < min T₁ T₂ := lt_min h1 h2
    refine U (-(min T₁ T₂)) (min T₁ T₂) 0 (Y T₁) (Y T₂) ⟨?_, ?_⟩
      (fun t ht => hY T₁ t ⟨?_, ?_⟩) (fun t ht => hY T₂ t ⟨?_, ?_⟩) (by rw [hY0, hY0]) ?_
    all_goals first
      | (have := abs_nonneg u; linarith [min_le_left T₁ T₂, min_le_right T₁ T₂])
      | (linarith [ht.1, ht.2, min_le_left T₁ T₂, min_le_right T₁ T₂])
      | exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  refine ⟨fun t => Y (|t| + 1) t, ⟨?_, fun t => ?_⟩, ?_⟩
  · simp only; exact hY0 _
  · have hev : (fun u => Y (|u| + 1) u) =ᶠ[𝓝 t] Y (|t| + 1) := by
      have hc : Continuous fun u : ℝ => |u| := continuous_abs
      filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds (show |t| < |t| + 1 by linarith))]
        with u hu
      exact agree _ _ u (by linarith) hu
    have hd := (hY (|t| + 1) t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
    have := hd.congr_of_eventuallyEq hev
    simpa [agree (|t| + 1) (|t| + 1) t (by linarith) (by linarith)] using this
  · rintro Ψ ⟨hΨ0, hΨ⟩
    funext t
    have h1 := U (-(|t| + 1)) (|t| + 1) 0 Ψ (Y (|t| + 1))
      ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
      (fun u _ => hΨ u) (fun u hu => hY _ u hu) (by rw [hΨ0, hY0])
    exact h1 ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

end AsymptoticOperator

/-! Basic identities for the symplectization of a star-shaped level (copied, renamed, from the
`ka_*` helpers of accepted solution a386257a). -/


set_option linter.unusedSimpArgs false

def ka_sig {n : ℕ} (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

def ka_sgn {n : ℕ} (k : Fin (2 * (n + 1))) : ℝ := if (k : ℕ) % 2 = 0 then -1 else 1

theorem ka_sig_val {n : ℕ} (k : Fin (2 * (n + 1))) :
    ((ka_sig k : Fin (2 * (n + 1))) : ℕ) = if (k : ℕ) % 2 = 0 then (k : ℕ) + 1 else (k : ℕ) - 1 := by
  unfold ka_sig; split_ifs <;> rfl

theorem ka_sig_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sig (ka_sig k) = k := by
  ext
  rw [ka_sig_val, ka_sig_val]
  split_ifs <;> omega

theorem ka_sgn_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn (ka_sig k) = - ka_sgn k := by
  unfold ka_sgn
  rw [ka_sig_val]
  split_ifs <;> (try norm_num) <;> omega

theorem ka_sgn_sq {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn k * ka_sgn k = 1 := by
  unfold ka_sgn; split_ifs <;> norm_num

def ka_sigE (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) :=
  Function.Involutive.toPerm ka_sig ka_sig_sig

theorem ka_sigE_apply {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sigE n k = ka_sig k := rfl

theorem ka_j0_apply {n : ℕ} (v : V n) (k : Fin (2 * (n + 1))) :
    j0 v k = ka_sgn k * v (ka_sig k) := by
  unfold j0 ka_sgn ka_sig
  split_ifs <;> simp

theorem ka_j0_j0 {n : ℕ} (v : V n) : j0 (j0 v) = -v := by
  funext k
  rw [ka_j0_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  simp only [Pi.neg_apply]
  have := ka_sgn_sq k
  linear_combination (-(v k)) * this

theorem ka_j0_smul {n : ℕ} (a : ℝ) (v : V n) : j0 (a • v) = a • j0 v := by
  funext k; simp only [ka_j0_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem ka_j0_add {n : ℕ} (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [ka_j0_apply, Pi.add_apply]; ring

theorem ka_j0_sub {n : ℕ} (u v : V n) : j0 (u - v) = j0 u - j0 v := by
  funext k; simp only [ka_j0_apply, Pi.sub_apply]; ring

theorem ka_dot_comm {n : ℕ} (u v : V n) : dot u v = dot v u := by
  unfold dot; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_dot_smul_right {n : ℕ} (a : ℝ) (u v : V n) : dot u (a • v) = a * dot u v := by
  unfold dot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_smul_left {n : ℕ} (a : ℝ) (u v : V n) : dot (a • u) v = a * dot u v := by
  rw [ka_dot_comm, ka_dot_smul_right, ka_dot_comm]

theorem ka_dot_add_right {n : ℕ} (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_add_left {n : ℕ} (u v w : V n) : dot (v + w) u = dot v u + dot w u := by
  rw [ka_dot_comm, ka_dot_add_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_sub_right {n : ℕ} (u v w : V n) : dot u (v - w) = dot u v - dot u w := by
  unfold dot; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_sub_left {n : ℕ} (u v w : V n) : dot (v - w) u = dot v u - dot w u := by
  rw [ka_dot_comm, ka_dot_sub_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_neg_right {n : ℕ} (u v : V n) : dot u (-v) = - dot u v := by
  unfold dot; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp)

theorem ka_dot_neg_left {n : ℕ} (u v : V n) : dot (-u) v = - dot u v := by
  rw [ka_dot_comm, ka_dot_neg_right, ka_dot_comm]

theorem ka_dot_j0_left {n : ℕ} (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (ka_sigE n)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [ka_sigE_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  ring

theorem ka_dot_j0_j0 {n : ℕ} (u v : V n) : dot (j0 u) (j0 v) = dot u v := by
  rw [ka_dot_j0_left, ka_j0_j0, ka_dot_neg_right, neg_neg]

theorem ka_dot_self_j0 {n : ℕ} (u : V n) : dot u (j0 u) = 0 := by
  have := ka_dot_j0_left u u
  rw [ka_dot_comm] at this
  linarith

theorem ka_clm_apply {n : ℕ} (L : V n →L[ℝ] ℝ) (v : V n) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (v k) : V n) = v k • Pi.single k 1 by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul]

theorem ka_fderiv_eq_dot {n : ℕ} (H : V n → ℝ) (x v : V n) :
    fderiv ℝ H x v = dot (grad H x) v := by
  rw [ka_clm_apply]; unfold dot grad
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_liouville_ham {n : ℕ} (H : V n → ℝ) (x : V n) :
    liouville x (hamVF H x) = fderiv ℝ H x x / 2 := by
  unfold liouville omega0 hamVF
  rw [ka_dot_j0_j0, ka_fderiv_eq_dot, ka_dot_comm]

theorem ka_reeb_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  have hpos : 0 < liouville x (hamVF H x) := by
    rw [ka_liouville_ham]; have := hH.2.2 x hx; linarith
  refine ⟨hpos, ?_, ?_, ?_⟩
  · unfold reeb
    have : liouville x ((liouville x (hamVF H x))⁻¹ • hamVF H x) =
        (liouville x (hamVF H x))⁻¹ * liouville x (hamVF H x) := by
      unfold liouville omega0; rw [ka_dot_smul_right]; ring
    rw [this, inv_mul_cancel₀ hpos.ne']
  · unfold reeb hamVF
    rw [map_smul, ka_fderiv_eq_dot, ka_dot_self_j0, smul_zero]
  · intro w hw
    unfold reeb hamVF omega0
    rw [ka_j0_smul, ka_j0_j0, ka_dot_smul_left, ka_dot_neg_left,
      ← ka_fderiv_eq_dot, hw]; ring

theorem ka_om_add_left {n : ℕ} (u v w : V n) : omega0 (u + v) w = omega0 u w + omega0 v w := by
  unfold omega0; rw [ka_j0_add, ka_dot_add_left]
theorem ka_om_add_right {n : ℕ} (u v w : V n) : omega0 w (u + v) = omega0 w u + omega0 w v := by
  unfold omega0; rw [ka_dot_add_right]
theorem ka_om_sub_left {n : ℕ} (u v w : V n) : omega0 (u - v) w = omega0 u w - omega0 v w := by
  unfold omega0; rw [ka_j0_sub, ka_dot_sub_left]
theorem ka_om_sub_right {n : ℕ} (u v w : V n) : omega0 w (u - v) = omega0 w u - omega0 w v := by
  unfold omega0; rw [ka_dot_sub_right]
theorem ka_om_smul_left {n : ℕ} (a : ℝ) (u w : V n) : omega0 (a • u) w = a * omega0 u w := by
  unfold omega0; rw [ka_j0_smul, ka_dot_smul_left]
theorem ka_om_smul_right {n : ℕ} (a : ℝ) (u w : V n) : omega0 w (a • u) = a * omega0 w u := by
  unfold omega0; rw [ka_dot_smul_right]
theorem ka_om_anti {n : ℕ} (u v : V n) : omega0 u v = - omega0 v u := by
  unfold omega0; rw [ka_dot_j0_left, ka_dot_comm]
theorem ka_om_self {n : ℕ} (u : V n) : omega0 u u = 0 := by
  have := ka_om_anti u u; linarith

theorem ka_liouvilleCLM_apply {n : ℕ} (x v : V n) : liouvilleCLM x v = liouville x v := by
  unfold liouvilleCLM liouville omega0 dot
  simp [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem ka_scale_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem ka_scale_unique {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (t : ℝ) (ht : 0 < t) (hHt : H (t • y) = 1) : scaleToS H y = t := by
  obtain ⟨r, _, hu⟩ := hH.2.1 y hy
  have h1 := hu t ⟨ht, hHt⟩
  have h2 := hu (scaleToS H y) (ka_scale_spec H hH y hy)
  rw [h1, h2]

theorem ka_scale_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y₀ : V n)
    (hy₀ : y₀ ≠ 0) : ContDiffAt ℝ ∞ (scaleToS H) y₀ := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y₀ hy₀
  set r := scaleToS H y₀
  set f : V n × ℝ → ℝ := fun p => H (p.2 • p.1) with hf
  have hfc : ContDiff ℝ ∞ f := hH.1.comp (ContDiff.smul contDiff_snd contDiff_fst)
  set u : V n × ℝ := (y₀, r)
  have cdf : ContDiffAt ℝ ∞ f u := hfc.contDiffAt
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- derivative
  have hg : HasFDerivAt (fun p : V n × ℝ => p.2 • p.1)
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀) u := by
    have h1 : HasFDerivAt (fun p : V n × ℝ => p.2) (ContinuousLinearMap.snd ℝ (V n) ℝ) u :=
      hasFDerivAt_snd
    have h2 : HasFDerivAt (fun p : V n × ℝ => p.1) (ContinuousLinearMap.fst ℝ (V n) ℝ) u :=
      hasFDerivAt_fst
    exact h1.smul h2
  have hHd : HasFDerivAt H (fderiv ℝ H (r • y₀)) (r • y₀) :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hfd : HasFDerivAt f ((fderiv ℝ H (r • y₀)).comp
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀)) u :=
    hHd.comp u hg
  have hpos : 0 < fderiv ℝ H (r • y₀) y₀ := by
    have := hH.2.2 (r • y₀) hHx
    rw [map_smul, smul_eq_mul] at this
    exact pos_of_mul_pos_right this hr.le
  set c := fderiv ℝ H (r • y₀) y₀
  have hL1 : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ) 1 = c := by
    rw [hfd.fderiv]; simp [c]
  have if₂ : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
      rw [show c⁻¹ = c⁻¹ • (1:ℝ) by simp, map_smul, hL1, smul_eq_mul, inv_mul_cancel₀ hpos.ne']
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply, hL1]
      simp [inv_mul_cancel₀ hpos.ne']
  set ψ := ContDiffAt.implicitFunction cdf pn if₂
  have hψc : ContDiffAt ℝ ∞ ψ y₀ := ContDiffAt.contDiffAt_implicitFunction cdf pn if₂
  have hψ0 : ψ y₀ = r := ContDiffAt.implicitFunction_apply_self cdf pn if₂
  have hψeq := ContDiffAt.eventually_apply_implicitFunction cdf pn if₂
  have hψpos : ∀ᶠ y in 𝓝 y₀, 0 < ψ y := by
    have := hψc.continuousAt.eventually (lt_mem_nhds (show (0:ℝ) < ψ y₀ by rw [hψ0]; exact hr))
    exact this
  have hne : ∀ᶠ y in 𝓝 y₀, y ≠ 0 := isOpen_ne.mem_nhds hy₀
  have hev : ψ =ᶠ[𝓝 y₀] scaleToS H := by
    filter_upwards [hψeq, hψpos, hne] with y h1 h2 h3
    have h1' : H (ψ y • y) = 1 := by
      have : f (y, ψ y) = f u := h1
      simp only [hf, u] at this
      rw [this, hHx]
    exact (ka_scale_unique H hH y h3 (ψ y) h2 h1').symm
  exact hψc.congr_of_eventuallyEq hev.symm


theorem ka_j0_contDiff {n : ℕ} : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 (fun k => ?_)
  have : (fun v : V n => j0 v k) = fun v => ka_sgn k * v (ka_sig k) := by
    funext v; exact ka_j0_apply v k
  rw [this]
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (ka_sig k))

theorem ka_dH_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)

theorem ka_grad_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (grad H) := by
  refine contDiff_pi.2 (fun k => ?_)
  exact (ka_dH_contDiff H hH).clm_apply contDiff_const

theorem ka_hamVF_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamVF H) := ka_j0_contDiff.comp (ka_grad_contDiff H hH)

theorem ka_liouvilleCLM_contDiff {n : ℕ} : ContDiff ℝ ∞ (liouvilleCLM : V n → V n →L[ℝ] ℝ) := by
  unfold liouvilleCLM
  refine ContDiff.const_smul _ (ContDiff.sum (fun k _ => ?_))
  exact ((contDiff_apply ℝ ℝ k).comp ka_j0_contDiff).smul contDiff_const

theorem ka_reeb_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContDiffAt ℝ ∞ (reeb H) x := by
  have hpos := (ka_reeb_spec H hH x hx).1
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [ka_liouvilleCLM_apply]
  have hc : ContDiff ℝ ∞ (fun x => liouville x (hamVF H x)) := by
    rw [hL]; exact ka_liouvilleCLM_contDiff.clm_apply (ka_hamVF_contDiff H hH.1)
  unfold reeb
  exact (hc.contDiffAt.inv hpos.ne').smul (ka_hamVF_contDiff H hH.1).contDiffAt

theorem ka_scale_hasFDerivAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) :
    HasFDerivAt (scaleToS H)
      ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)) y := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hy
  have hd : DifferentiableAt ℝ (scaleToS H) y :=
    (ka_scale_contDiffAt H hH y hy).differentiableAt (by simp)
  set r := scaleToS H y
  set x := proj H y
  have hxr : x = r • y := rfl
  set L := fderiv ℝ (scaleToS H) y
  have hm : HasFDerivAt (fun y' => scaleToS H y' • y') (r • ContinuousLinearMap.id ℝ (V n) +
      L.smulRight y) y := hd.hasFDerivAt.smul (hasFDerivAt_id y)
  have hHd : HasFDerivAt H (fderiv ℝ H x) x :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg := hHd.comp y hm
  have hev : (H ∘ fun y' => scaleToS H y' • y') =ᶠ[𝓝 y] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hy] with y' hy'
    exact (ka_scale_spec H hH y' hy').2
  have h0 := hg.fderiv
  rw [hev.fderiv_eq, fderiv_fun_const] at h0
  have hD : 0 < fderiv ℝ H x x := hH.2.2 x hHx
  have hL : ∀ v, L v = -(r ^ 2 / fderiv ℝ H x x) * fderiv ℝ H x v := by
    intro v
    have := congrArg (fun T => T v) h0
    simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      smul_eq_mul] at this
    have hxy : fderiv ℝ H x y = fderiv ℝ H x x / r := by
      rw [hxr, map_smul, smul_eq_mul]; field_simp
    rw [hxy] at this
    field_simp
    field_simp at this
    linarith
  have : L = (-(r ^ 2 / fderiv ℝ H x x)) • fderiv ℝ H x := by
    ext1 v; rw [hL v]; rfl
  rw [← this]; exact hd.hasFDerivAt

theorem ka_hol_abstract {n : ℕ} (A B : V n) (P : V n → Prop) (J' : V n →L[ℝ] V n)
    (α β : V n →L[ℝ] ℝ)
    (hW : ∀ v, P (v - α v • A - β v • B)) (hJP : ∀ w, P w → P (J' w))
    (hαA : α A = 1) (hαB : α B = 0) (hβA : β A = 0) (hβB : β B = 1)
    (hαP : ∀ w, P w → α w = 0) (hβP : ∀ w, P w → β w = 0)
    (hB : ∀ w, P w → omega0 B w = 0) (us ut : V n)
    (hhol : us + (α ut • B - β ut • A + J' (ut - α ut • A - β ut • B)) = 0) :
    α us = β ut ∧ α ut = - β us ∧
      omega0 (us - α us • A) (ut - α ut • A) =
        omega0 (ut - α ut • A - β ut • B) (J' (ut - α ut • A - β ut • B)) ∧
      (β us = 0 → β ut = 0 → ut - α ut • A - β ut • B = 0 → us = 0 ∧ ut = 0) := by
  set w := ut - α ut • A - β ut • B with hwdef
  have hPw : P w := hW ut
  have hPJw := hJP _ hPw
  have hs : us = -(α ut • B - β ut • A + J' w) := eq_neg_of_add_eq_zero_left hhol
  have e1 : α us = β ut := by
    rw [hs, map_neg, map_add, hαP _ hPJw]
    simp only [map_sub, map_smul, hαA, hαB, smul_eq_mul]; ring
  have e2 : β us = - α ut := by
    rw [hs, map_neg, map_add, hβP _ hPJw]
    simp only [map_sub, map_smul, hβA, hβB, smul_eq_mul]; ring
  have hus : us - α us • A = β us • B - J' w := by
    rw [e1, e2]; rw [hs]; module
  have hut : ut - α ut • A = β ut • B + w := by rw [hwdef]; module
  have hBB : omega0 B B = 0 := ka_om_self B
  have hJwB : omega0 (J' w) B = 0 := by rw [ka_om_anti, hB _ hPJw, neg_zero]
  refine ⟨e1, by linarith, ?_, ?_⟩
  · rw [hus, hut]
    simp only [ka_om_add_right, ka_om_sub_left, ka_om_smul_left, ka_om_smul_right,
      hBB, hB _ hPw, hJwB]
    rw [ka_om_anti (J' w) w]; ring
  · intro h1 h2 h3
    have hw0 : w = 0 := h3
    have hα : α ut = 0 := by linarith
    have hJ0 : J' w = 0 := by rw [hw0, map_zero]
    constructor
    · rw [hs, hJ0, h2, hα]; simp
    · have : ut = α ut • A + β ut • B + w := by rw [hwdef]; module
      rw [this, hα, h2, hw0]; simp

theorem ka_clm_complex_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) (h1 : L 1 = 0) (hI : L Complex.I = 0) : L = 0 := by
  ext1 z
  have : z = z.re • (1:ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [this, map_add, map_smul, map_smul, h1, hI]; simp

theorem ka_cr {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
    dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  set y := u z with hydef
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hz
  set r := scaleToS H y with hrdef
  set x := proj H y with hxdef
  have hxr : x = r • y := rfl
  have hx : x ∈ energySurface H := hHx
  have hyx : y = r⁻¹ • x := by rw [hxr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨hc, hR1, hRH, hRw⟩ := ka_reeb_spec H hH x hx
  set R := reeb H x
  set D := fderiv ℝ H x x
  have hD : 0 < D := hH.2.2 x hx
  set α : V n →L[ℝ] ℝ := (r / (2 * D)) • fderiv ℝ H x with hαdef
  set β : V n →L[ℝ] ℝ := r • liouvilleCLM x with hβdef
  set A : V n := (2:ℝ) • y
  set B : V n := r⁻¹ • R
  have hLA : liouvilleCLM x A = 0 := by
    simp only [A, hyx, ka_liouvilleCLM_apply]
    unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring
  -- derivatives
  have hS' := ka_scale_hasFDerivAt H hH y hz
  have ha' : HasFDerivAt (aCoord H) α y := by
    have h1 := (hS'.log hr.ne').const_mul (-1/2 : ℝ)
    have : (fun y => (-1/2 : ℝ) * Real.log (scaleToS H y)) = aCoord H := by
      funext y; unfold aCoord; ring
    rw [this] at h1
    have heq : α = ((-1 / 2 : ℝ) • (scaleToS H y)⁻¹ • -(scaleToS H y ^ 2 /
        (fderiv ℝ H (proj H y)) (proj H y)) • fderiv ℝ H (proj H y)) := by
      ext1 v
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ← hrdef, ← hxdef]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      field_simp
      exact mul_comm _ _
    rw [heq]; exact h1
  have hp' : HasFDerivAt (proj H) (r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A)) y := by
    have h1 := hS'.smul (hasFDerivAt_id y)
    have heq : r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A) =
        scaleToS H y • ContinuousLinearMap.id ℝ (V n) +
        ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)).smulRight y := by
      ext1 v
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul, ← hrdef, ← hxdef, smul_sub, smul_smul]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      rw [sub_eq_add_neg, ← neg_smul]
      congr 2
      field_simp
      ring
    rw [heq]; exact h1
  set us := fderiv ℝ u z 1
  set ut := fderiv ℝ u z Complex.I
  have hdsa : ds (fun z => aCoord H (u z)) z = α us := by
    unfold ds; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdta : dt (fun z => aCoord H (u z)) z = α ut := by
    unfold dt; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdsw : ds (fun z => proj H (u z)) z = r • (us - α us • A) := by
    unfold ds; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdtw : dt (fun z => proj H (u z)) z = r • (ut - α ut • A) := by
    unfold dt; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hWgen : ∀ v, IsInXi H x (v - α v • A - β v • B) := by
    intro v
    simp only [hαdef, hβdef, ContinuousLinearMap.smul_apply, ka_liouvilleCLM_apply, smul_eq_mul]
    constructor
    · unfold liouville
      rw [ka_om_sub_right, ka_om_sub_right]
      simp only [A, B, hyx, ka_om_smul_right]
      have h1 : omega0 x x = 0 := ka_om_self x
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h1, h2]; field_simp; ring
    · simp only [A, B, map_sub, map_smul, smul_eq_mul, hRH, hyx]
      field_simp; ring
  have key := ka_hol_abstract A B (IsInXi H x) (J x) α β hWgen
    (fun w hw => (hJ.2 x hx w w hw hw).1)
    (by
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hyx]
      field_simp
      rfl)
    (by simp only [hαdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hRH]; ring)
    (by
      simp only [hβdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hyx]
      unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring)
    (by
      simp only [hβdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply]
      unfold liouville; simp only [ka_om_smul_right]
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h2]; field_simp)
    (fun w hw => by
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, hw.2]; ring)
    (fun w hw => by
      simp only [hβdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hw.1]; ring)
    (fun w hw => by simp only [B]; rw [ka_om_smul_left, hRw w hw.2]; ring)
    us ut hhol
  obtain ⟨e1, e2, e3, e4⟩ := key
  set W := ut - α ut • A - β ut • B
  have hPW : IsInXi H x W := hWgen ut
  have hm : 0 ≤ omega0 W (J x W) := by
    by_cases h0 : W = 0
    · rw [h0, map_zero, ka_om_self]
    · exact ((hJ.2 x hx W W hPW hPW).2.2.1 h0).le
  have hLs : liouville x (r • (us - α us • A)) = β us := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  have hLt : liouville x (r • (ut - α ut • A)) = β ut := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  refine ⟨?_, ?_⟩
  · rw [hdsa, hdtw, hLt, e1]
  · rw [hdta, hdsw, hLs, e2]



namespace KAo
open FiniteEnergyPlane
variable {n : ℕ}

/-- `j0` as a continuous linear map. -/
noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := ka_j0_add, map_smul' := ka_j0_smul }

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def omegaL : V n →L[ℝ] V n →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k)

theorem omegaL_apply (u v : V n) : omegaL u v = omega0 u v := by
  simp [omegaL, omega0, dot, ContinuousLinearMap.sum_apply, j0L]

end KAo

/-!
# T2 child B: the Hamiltonian flow on `S` is a time change of the Reeb flow

For a trajectory `x` of `X_H` on `S` and `σ(t) = ∫₀ᵗ λ₀(X_H)(x)`:
* (B1) a Reeb orbit `Q` with `Q(0) = x(0)` satisfies `Q(σ t) = x t`;
* (B2) the linearized Hamiltonian flow `Y` along `x`, projected to `ξ` along the Reeb field,
  equals the linearized Reeb flow `Φ` at time `σ t` on `ξ_{x(0)}`.
-/


namespace FiniteEnergyPlane

variable {n : ℕ}

lemma t2b_hamVF_eq_smul_reeb (H : V n → ℝ) {y : V n} (hy : liouville y (hamVF H y) ≠ 0) :
    hamVF H y = liouville y (hamVF H y) • reeb H y := by
  unfold reeb; rw [smul_smul, mul_inv_cancel₀ hy, one_smul]

lemma t2b_f_eq (y : V n) (H : V n → ℝ) :
    liouville y (hamVF H y) = (1 / 2 : ℝ) * KAo.omegaL y (hamVF H y) := by
  rw [KAo.omegaL_apply]; unfold liouville; ring

lemma t2b_f_contDiff (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun y => liouville y (hamVF H y)) := by
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [ka_liouvilleCLM_apply]
  rw [hL]; exact ka_liouvilleCLM_contDiff.clm_apply (ka_hamVF_contDiff H hH)

/-- (B1) Time change of orbits. -/
theorem t2b_orbit (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : ℝ → V n)
    (hx : ∀ t, HasDerivAt x (hamVF H (x t)) t) (hxS : ∀ t, x t ∈ energySurface H)
    (Q : ReebOrbit H) (h0 : Q.x 0 = x 0) (t : ℝ) :
    Q.x (∫ s in (0 : ℝ)..t, liouville (x s) (hamVF H (x s))) = x t := by
  set f : V n → ℝ := fun y => liouville y (hamVF H y) with hf
  have hfc : Continuous f := (t2b_f_contDiff H hH.1).continuous
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun s => (hx s).continuousAt
  have hfx : Continuous (fun s => f (x s)) := hfc.comp hxc
  set σ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f (x s) with hσdef
  have hσ : ∀ t, HasDerivAt σ (f (x t)) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hfx.intervalIntegrable _ _)
      (hfx.stronglyMeasurableAtFilter _ _) hfx.continuousAt
  set y : ℝ → V n := fun t => Q.x (σ t) with hydef
  have hy : ∀ t, HasDerivAt y (f (x t) • reeb H (y t)) t := fun t =>
    (Q.hasDerivAt (σ t)).scomp t (hσ t)
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun s => (hy s).continuousAt
  have hx' : ∀ t, HasDerivAt x (f (x t) • reeb H (x t)) t := fun t => by
    have := t2b_hamVF_eq_smul_reeb H (ka_reeb_spec H hH _ (hxS t)).1.ne'
    rw [← this]; exact hx t
  set lo := min 0 t - 1
  set hi := max 0 t + 1
  set K := x '' Icc lo hi ∪ y '' Icc lo hi
  have hK : IsCompact K := (isCompact_Icc.image hxc).union (isCompact_Icc.image hyc)
  have hKS : K ⊆ energySurface H := by
    rintro _ (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩)
    · exact hxS s
    · exact Q.mem _
  have hloc : LocallyLipschitzOn K (reeb H) := by
    intro z hz
    obtain ⟨L, u, hu, hL⟩ :=
      ((ka_reeb_contDiffAt H hH z (hKS hz)).of_le (by simp)).exists_lipschitzOnWith
    exact ⟨L, u, mem_nhdsWithin_of_mem_nhds hu, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
    hfx.continuousOn
  have hv : ∀ s ∈ Ioo lo hi, LipschitzOnWith (Real.toNNReal C * L)
      (fun z => f (x s) • reeb H z) K := by
    intro s hs
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [dist_smul₀]
    have h1 : ‖f (x s)‖ ≤ Real.toNNReal C := by
      rw [Real.coe_toNNReal']; exact (hC s (Ioo_subset_Icc_self hs)).trans (le_max_left _ _)
    have h2 := hL.dist_le_mul a ha b hb
    push_cast
    calc ‖f (x s)‖ * dist (reeb H a) (reeb H b) ≤ (Real.toNNReal C : ℝ) * (L * dist a b) :=
          mul_le_mul h1 h2 dist_nonneg (by positivity)
      _ = _ := by ring
  have ha : (0 : ℝ) ∈ Ioo lo hi := ⟨by simp only [lo]; linarith [min_le_left (0 : ℝ) t],
    by simp only [hi]; linarith [le_max_left (0 : ℝ) t]⟩
  have hsub : Ioo lo hi ⊆ Icc lo hi := Ioo_subset_Icc_self
  have heq := ODE_solution_unique_of_mem_Icc (v := fun s z => f (x s) • reeb H z)
    (s := fun _ => K) hv ha
    hyc.continuousOn (fun s _ => hy s) (fun s hs => Or.inr ⟨s, hsub hs, rfl⟩)
    hxc.continuousOn (fun s _ => hx' s) (fun s hs => Or.inl ⟨s, hsub hs, rfl⟩)
    (by simp [y, σ, h0])
  exact heq ⟨by linarith [min_le_right (0 : ℝ) t], by linarith [le_max_right (0 : ℝ) t]⟩

end FiniteEnergyPlane

/-! # T2 child B2: projected linearized Hamiltonian flow = time-changed linearized Reeb flow -/


namespace FiniteEnergyPlane

variable {n : ℕ}

lemma t2b_omegaL_hasDerivAt {a b : ℝ → V n} {a' b' : V n} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => KAo.omegaL (a s) (b s)) (KAo.omegaL a' (b t) + KAo.omegaL (a t) b') t := by
  have h1 : HasDerivAt (fun s => KAo.omegaL (a s)) (KAo.omegaL a') t :=
    KAo.omegaL.hasFDerivAt.comp_hasDerivAt t ha
  exact h1.clm_apply hb

lemma t2b_dH_hamVF (H : V n → ℝ) (y : V n) : fderiv ℝ H y (hamVF H y) = 0 := by
  unfold hamVF; rw [ka_fderiv_eq_dot, ka_dot_self_j0]

lemma t2b_omega_hamVF (H : V n → ℝ) (y u : V n) :
    omega0 (hamVF H y) u = - fderiv ℝ H y u := by
  unfold omega0 hamVF; rw [ka_j0_j0, ka_dot_neg_left, ← ka_fderiv_eq_dot]

/-- `D²H(y)(X_H, u) = -dH(y)(DX_H(y) u)`. -/
lemma t2b_d2H (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) (y u : V n) :
    fderiv ℝ (fderiv ℝ H) y (hamVF H y) u = - fderiv ℝ H y (fderiv ℝ (hamVF H) y u) := by
  have hdH : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) y) y :=
    ((ka_dH_contDiff H hH).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hX : HasFDerivAt (hamVF H) (fderiv ℝ (hamVF H) y) y :=
    ((ka_hamVF_contDiff H hH).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hk := hdH.clm_apply hX
  have hk0 : (fun y => fderiv ℝ H y (hamVF H y)) = fun _ => (0 : ℝ) :=
    funext (t2b_dH_hamVF H)
  rw [hk0] at hk
  have h0 := congrArg (fun T => T u) (hk.unique (hasFDerivAt_const 0 y))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at h0
  have hsym := (hH.contDiffAt (x := y)).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top) (hamVF H y) u
  rw [hsym]; linarith

/-- `DX_H = f DR + df ⊗ R` at a point of `S`, with `f = λ₀(X_H)`. -/
lemma t2b_dX (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : y ∈ energySurface H) (u : V n) :
    fderiv ℝ (hamVF H) y u = liouville y (hamVF H y) • fderiv ℝ (reeb H) y u +
      ((1 / 2 : ℝ) * (omega0 u (hamVF H y) + omega0 y (fderiv ℝ (hamVF H) y u))) •
        reeb H y := by
  set f : V n → ℝ := fun y => liouville y (hamVF H y) with hf
  have hfc : Continuous f := (t2b_f_contDiff H hH.1).continuous
  have hpos := (ka_reeb_spec H hH y hy).1
  have hev : hamVF H =ᶠ[𝓝 y] fun z => f z • reeb H z := by
    filter_upwards [hfc.continuousAt.eventually_ne hpos.ne'] with z hz
    exact t2b_hamVF_eq_smul_reeb H hz
  have hX : HasFDerivAt (hamVF H) (fderiv ℝ (hamVF H) y) y :=
    ((ka_hamVF_contDiff H hH.1).differentiable (by simp)).differentiableAt.hasFDerivAt
  -- derivative of `f = ½ ω₀(y, X_H y)`
  have hfeq : f = fun y => (1 / 2 : ℝ) * KAo.omegaL y (hamVF H y) := by
    funext z; exact t2b_f_eq z H
  have hO : HasFDerivAt (fun z => KAo.omegaL z) (KAo.omegaL) y := KAo.omegaL.hasFDerivAt
  have hfd : HasFDerivAt f ((1 / 2 : ℝ) • ((KAo.omegaL y).comp (fderiv ℝ (hamVF H) y) +
      KAo.omegaL.flip (hamVF H y))) y := by
    rw [hfeq]; exact (hO.clm_apply hX).const_mul _
  have hR : HasFDerivAt (reeb H) (fderiv ℝ (reeb H) y) y :=
    ((ka_reeb_contDiffAt H hH y hy).differentiableAt (by simp)).hasFDerivAt
  have hprod := hfd.smul hR
  have hX' := hprod.congr_of_eventuallyEq hev
  have e := hX'.fderiv
  conv_lhs => rw [e]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, KAo.omegaL_apply, smul_eq_mul, f]
  congr 2
  ring

/-- (B2) On `ξ_{x(0)}`, the linearized Hamiltonian flow projected to `ξ` along the Reeb field is
the linearized Reeb flow at the changed time `σ`. -/
theorem t2b_lin (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : ℝ → V n)
    (hx : ∀ t, HasDerivAt x (hamVF H (x t)) t) (hxS : ∀ t, x t ∈ energySurface H)
    (Q : ReebOrbit H) (σ : ℝ → ℝ)
    (hσ : ∀ t, HasDerivAt σ (liouville (x t) (hamVF H (x t))) t) (hσ0 : σ 0 = 0)
    (hQ : ∀ t, Q.x (σ t) = x t)
    (Y : ℝ → V n →L[ℝ] V n) (hY0 : Y 0 = ContinuousLinearMap.id ℝ (V n))
    (hY : ∀ t, HasDerivAt Y ((fderiv ℝ (hamVF H) (x t)).comp (Y t)) t)
    (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow Q Φ) (v : V n) (hv : IsInXi H (x 0) v)
    (t : ℝ) :
    piXi H (x t) (Y t v) = Φ (σ t) v := by
  set f : V n → ℝ := fun y => liouville y (hamVF H y) with hf
  have hfc : Continuous f := (t2b_f_contDiff H hH.1).continuous
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun s => (hx s).continuousAt
  set u : ℝ → V n := fun s => Y s v with hudef
  have hu : ∀ s, HasDerivAt u (fderiv ℝ (hamVF H) (x s) (u s)) s := fun s => by
    have := (hY s).clm_apply (hasDerivAt_const s v)
    simpa [u] using this
  -- `dH(x)(u) ≡ 0`
  have hg : ∀ s, fderiv ℝ H (x s) (u s) = 0 := by
    have hdH : ∀ s, HasDerivAt (fun s => fderiv ℝ H (x s))
        (fderiv ℝ (fderiv ℝ H) (x s) (hamVF H (x s))) s := fun s =>
      (((ka_dH_contDiff H hH.1).differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt
        s (hx s)
    have hgd : ∀ s, HasDerivAt (fun s => fderiv ℝ H (x s) (u s)) 0 s := fun s => by
      have := (hdH s).clm_apply (hu s)
      refine this.congr_deriv ?_
      rw [t2b_d2H H hH.1]; ring
    intro s
    have hc := is_const_of_deriv_eq_zero (fun r => (hgd r).differentiableAt)
      (fun r => (hgd r).deriv) s 0
    rw [hc]; simp only [u, hY0, ContinuousLinearMap.id_apply]; exact hv.2
  -- the projected vector
  set ℓ : ℝ → ℝ := fun s => liouville (x s) (u s) with hℓdef
  have hℓ : ∀ s, HasDerivAt ℓ ((1 / 2 : ℝ) * (omega0 (hamVF H (x s)) (u s) +
      omega0 (x s) (fderiv ℝ (hamVF H) (x s) (u s)))) s := fun s => by
    have h := (t2b_omegaL_hasDerivAt (hx s) (hu s)).const_mul (1 / 2 : ℝ)
    have he : ℓ = fun s => (1 / 2 : ℝ) * KAo.omegaL (x s) (u s) := by
      funext r; simp only [ℓ, KAo.omegaL_apply, liouville]; ring
    rw [he]; simpa only [KAo.omegaL_apply] using h
  have hRx : ∀ s, HasDerivAt (fun s => reeb H (x s))
      (fderiv ℝ (reeb H) (x s) (hamVF H (x s))) s := fun s =>
    ((ka_reeb_contDiffAt H hH (x s) (hxS s)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      s (hx s)
  set w : ℝ → V n := fun s => piXi H (x s) (u s) with hwdef
  set B : ℝ → V n →L[ℝ] V n := fun s => f (x s) • fderiv ℝ (reeb H) (x s) with hBdef
  have hw : ∀ s, HasDerivAt w (B s (w s)) s := fun s => by
    have h := (hu s).sub ((hℓ s).smul (hRx s))
    refine h.congr_deriv ?_
    have hXs := t2b_hamVF_eq_smul_reeb H (ka_reeb_spec H hH _ (hxS s)).1.ne'
    have hdX := t2b_dX H hH (hxS s) (u s)
    have hom : omega0 (hamVF H (x s)) (u s) = 0 := by rw [t2b_omega_hamVF, hg s, neg_zero]
    have hom' : omega0 (u s) (hamVF H (x s)) = 0 := by rw [ka_om_anti, hom, neg_zero]
    rw [hom'] at hdX
    simp only [B, w, piXi, ContinuousLinearMap.smul_apply, map_sub, map_smul]
    have hXs' : fderiv ℝ (reeb H) (x s) (hamVF H (x s)) =
        f (x s) • fderiv ℝ (reeb H) (x s) (reeb H (x s)) := by
      conv_lhs => rw [hXs]
      rw [map_smul]
    rw [hom, hXs']
    simp only [f, ℓ] at hdX ⊢
    linear_combination (norm := module) hdX
  have hBc : Continuous B := by
    refine (hfc.comp hxc).smul (continuous_iff_continuousAt.2 fun s => ?_)
    exact (((ka_reeb_contDiffAt H hH (x s) (hxS s)).fderiv_right (m := 0) (by simp)).continuousAt).comp
      hxc.continuousAt
  -- the time-changed linearized Reeb flow
  set ψ : ℝ → V n := fun s => Φ (σ s) v with hψdef
  have hψ : ∀ s, HasDerivAt ψ (B s (ψ s)) s := fun s => by
    have h1 := ((hΦ.2 (σ s)).scomp s (hσ s)).clm_apply (hasDerivAt_const s v)
    refine h1.congr_deriv ?_
    simp [B, ψ, hQ s, f]
  obtain ⟨z, -, huniq⟩ := AsymptoticOperator.linearODE_existsUnique B hBc v
  have hw0 : w 0 = v := by
    simp only [w, piXi, u, hY0, ContinuousLinearMap.id_apply, hv.1, zero_smul, sub_zero]
  have hψ0 : ψ 0 = v := by
    simp only [ψ, hσ0, hΦ.1, ContinuousLinearMap.id_apply]
  have e1 := huniq w ⟨hw0, hw⟩
  have e2 := huniq ψ ⟨hψ0, hψ⟩
  have := congrFun (e1.trans e2.symm) t
  simpa [w, ψ, u] using this

end FiniteEnergyPlane

namespace FiniteEnergyPlane

theorem hamiltonianFlow_reeb_timeChange_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (x : ℝ → V n)
    (hx : ∀ t, HasDerivAt x (hamVF H (x t)) t) (hxS : ∀ t, x t ∈ energySurface H)
    (Q : ReebOrbit H) (h0 : Q.x 0 = x 0)
    (Y : ℝ → V n →L[ℝ] V n) (hY0 : Y 0 = ContinuousLinearMap.id ℝ (V n))
    (hY : ∀ t, HasDerivAt Y ((fderiv ℝ (hamVF H) (x t)).comp (Y t)) t)
    (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow Q Φ) :
    let σ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, liouville (x s) (hamVF H (x s))
    ∀ t : ℝ, Q.x (σ t) = x t ∧
      ∀ v : V n, IsInXi H (x 0) v → piXi H (x t) (Y t v) = Φ (σ t) v := by
  intro σ
  have hfc : Continuous (fun y => liouville y (hamVF H y)) := (t2b_f_contDiff H hH.1).continuous
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun s => (hx s).continuousAt
  have hfx : Continuous (fun s => liouville (x s) (hamVF H (x s))) := hfc.comp hxc
  have hσ : ∀ t, HasDerivAt σ (liouville (x t) (hamVF H (x t))) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hfx.intervalIntegrable _ _)
      (hfx.stronglyMeasurableAtFilter _ _) hfx.continuousAt
  have hQ : ∀ t, Q.x (σ t) = x t := t2b_orbit H hH x hx hxS Q h0
  intro t
  exact ⟨hQ t, fun v hv => t2b_lin H hH x hx hxS Q σ hσ (by simp [σ]) hQ Y hY0 hY Φ hΦ v hv t⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (x : ℝ → V n)
    (hx : ∀ t, HasDerivAt x (hamVF H (x t)) t) (hxS : ∀ t, x t ∈ energySurface H)
    (Q : ReebOrbit H) (h0 : Q.x 0 = x 0)
    (Y : ℝ → V n →L[ℝ] V n) (hY0 : Y 0 = ContinuousLinearMap.id ℝ (V n))
    (hY : ∀ t, HasDerivAt Y ((fderiv ℝ (hamVF H) (x t)).comp (Y t)) t)
    (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow Q Φ) :
    let σ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, liouville (x s) (hamVF H (x s))
    ∀ t : ℝ, Q.x (σ t) = x t ∧
      ∀ v : V n, IsInXi H (x 0) v → piXi H (x t) (Y t v) = Φ (σ t) v :=
  hamiltonianFlow_reeb_timeChange_aux H hH x hx hxS Q h0 Y hY0 hY Φ hΦ
