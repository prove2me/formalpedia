-- Prove2me | solution 1 for BregmanRelax.IneqConstr.theorem4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:48:20.103643+00:00
-- url     : https://prove2.me/submissions/a287911a-be01-4ad6-a71e-f17e01b02050

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_IneqConstr_Program

set_option autoImplicit false

namespace F63a94e2Aux

open BregmanRelax.IneqConstr BregmanRelax.EqConstr Filter

lemma D_symm_sum {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (x y : EuclideanSpace ℝ (Fin p)) :
    bregmanD f g x y + bregmanD f g y x = inner ℝ (g x - g y) (x - y) := by
  unfold bregmanD
  rw [inner_sub_left]
  have : inner ℝ (g x) (y - x) = - inner ℝ (g x) (x - y) := by
    rw [← inner_neg_right, neg_sub]
  rw [this]; ring

lemma mono {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {A : Fin m → Set (EuclideanSpace ℝ (Fin p))}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hA : BregmanRelax.Cyclic.DConditions A S (bregmanD f g) P)
    {x y : EuclideanSpace ℝ (Fin p)} (hx : x ∈ S) (hy : y ∈ S) (v : EuclideanSpace ℝ (Fin p))
    (hv : g x - g y = v) :
    0 ≤ inner ℝ v (x - y) ∧ (inner ℝ v (x - y) = 0 → x = y) := by
  have h1 := hA.nonneg x hx y hy
  have h2 := hA.nonneg y hy x hx
  have hs := D_symm_sum f g x y
  rw [hv] at hs
  refine ⟨by linarith, fun h0 => ?_⟩
  have : bregmanD f g x y = 0 := by linarith
  exact (hA.eq_zero_iff x hx y hy).1 this

lemma sum_update {p m : ℕ} (u : Fin m → ℝ) (a : Fin m → EuclideanSpace ℝ (Fin p))
    (i : Fin m) (v : ℝ) :
    ∑ j, Function.update u i v j • a j = ∑ j, u j • a j + (v - u i) • a i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => u j • a j) (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, Function.update u i v j • a j
      = ∑ j ∈ Finset.univ.erase i, u j • a j :=
    Finset.sum_congr rfl (fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this, Function.update_self, sub_smul]
  abel

lemma sum_update_mul {p m : ℕ} (u : Fin m → ℝ) (a : Fin m → EuclideanSpace ℝ (Fin p))
    (b : Fin m → ℝ) (y : EuclideanSpace ℝ (Fin p)) (i : Fin m) (v : ℝ) :
    ∑ j, (Function.update u i v j - u j) * (inner ℝ (a j) y - b j)
      = (v - u i) * (inner ℝ (a i) y - b i) := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Function.update_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma phi_diff {p m : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : Fin m → EuclideanSpace ℝ (Fin p)) (b : Fin m → ℝ)
    {x : EuclideanSpace ℝ (Fin p)} {u : Fin m → ℝ} (hg : g x = ∑ j, u j • a j)
    (x' : EuclideanSpace ℝ (Fin p)) (u' : Fin m → ℝ) :
    bregmanD f g x' x = phi f a b x' u' - phi f a b x u
      + ∑ j, (u' j - u j) * (inner ℝ (a j) x' - b j) := by
  unfold bregmanD phi
  rw [hg, sum_inner]
  simp only [real_inner_smul_left, inner_sub_right]
  have e : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      u j * inner ℝ (a j) x' - u j * inner ℝ (a j) x
        = (u' j * (inner ℝ (a j) x' - b j) - u j * (inner ℝ (a j) x - b j))
          - (u' j - u j) * (inner ℝ (a j) x' - b j) := by
    intros; ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

lemma step_props {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    {i : Fin m} {x x' : EuclideanSpace ℝ (Fin p)} {u u' : Fin m → ℝ}
    (hxS : x ∈ S) (hu : ∀ j, 0 ≤ u j) (hg : g x = ∑ j, u j • a j)
    (hstep : IsMethodStep S g a b i x u x' u') :
    x' ∈ S ∧ (∀ j, 0 ≤ u' j) ∧ g x' = ∑ j, u' j • a j ∧ b i ≤ inner ℝ (a i) x' ∧
      ∑ j, (u' j - u j) * (inner ℝ (a j) x' - b j) ≤ 0 := by
  obtain ⟨hx'S, hcase⟩ := hstep
  refine ⟨hx'S, ?_⟩
  rcases hcase with ⟨hlt, lam, hgx, hax, hu'⟩ | ⟨hcond, hx', hu'⟩ |
      ⟨hgt, hupos, μ', y, hyS, hgy, hay, hgx, hu'⟩
  · have hmono := (mono hA hx'S hxS (lam • a i) (by rw [hgx]; abel)).1
    rw [real_inner_smul_left, inner_sub_right, hax] at hmono
    have hpos : 0 < b i - inner ℝ (a i) x := by linarith
    have hlam : 0 ≤ lam := nonneg_of_mul_nonneg_left hmono hpos
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      rw [hu']
      by_cases hj : j = i
      · rw [hj, Function.update_self]; linarith [hu i]
      · simp [Function.update_of_ne hj, hu j]
    · rw [hgx, hu', sum_update, hg]
      congr 2
      ring
    · rw [hax]
    · rw [hu', sum_update_mul, hax]; simp
  · subst hx'
    subst hu'
    refine ⟨hu, hg, ?_, by simp⟩
    rcases hcond with h | ⟨h, _⟩
    · exact h.ge
    · exact h.le
  · obtain ⟨μ, hμ⟩ : ∃ μ, μ = min μ' (u i) := ⟨_, rfl⟩
    rw [← hμ] at hgx hu'
    have hm1 := (mono hA hyS hxS (-(μ' • a i)) (by rw [hgy]; abel)).1
    rw [inner_neg_left, real_inner_smul_left, inner_sub_right, hay] at hm1
    have hμ' : 0 ≤ μ' := by nlinarith
    have hμ0 : 0 ≤ μ := by rw [hμ]; exact le_min hμ' (hu i)
    have hμu : μ ≤ u i := by rw [hμ]; exact min_le_right _ _
    have hm2 := mono hA hx'S hyS ((μ' - μ) • a i) (by rw [hgx, hgy, sub_smul]; abel)
    rw [real_inner_smul_left, inner_sub_right, hay] at hm2
    have h4 : b i ≤ inner ℝ (a i) x' := by
      have hle : μ ≤ μ' := by rw [hμ]; exact min_le_left _ _
      rcases hle.lt_or_eq with hlt | heq
      · have := hm2.1
        nlinarith
      · have h0 : (μ' - μ) * (inner ℝ (a i) x' - b i) = 0 := by rw [heq]; ring
        have := hm2.2 h0
        rw [this, hay]
    refine ⟨?_, ?_, h4, ?_⟩
    · intro j
      rw [hu']
      by_cases hj : j = i
      · rw [hj, Function.update_self]; linarith
      · simp [Function.update_of_ne hj, hu j]
    · rw [hgx, hu', sum_update, hg]
      rw [show u i - μ - u i = -μ by ring, neg_smul, sub_eq_add_neg]
    · rw [hu', sum_update_mul]
      nlinarith

lemma D_nonneg_closure {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {A : Fin m → Set (EuclideanSpace ℝ (Fin p))}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hA : BregmanRelax.Cyclic.DConditions A S (bregmanD f g) P)
    (hfcl : ContinuousOn f (closure S)) {z y : EuclideanSpace ℝ (Fin p)}
    (hz : z ∈ closure S) (hy : y ∈ S) : 0 ≤ bregmanD f g z y := by
  obtain ⟨zk, hzkS, hlim⟩ := mem_closure_iff_seq_limit.1 hz
  have hf : Tendsto (fun k => f (zk k)) atTop (nhds (f z)) :=
    (hfcl z hz).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hlim, Filter.Eventually.of_forall fun k => subset_closure (hzkS k)⟩)
  have hD : Tendsto (fun k => bregmanD f g (zk k) y) atTop (nhds (bregmanD f g z y)) := by
    unfold bregmanD
    exact (hf.sub tendsto_const_nhds).sub (tendsto_const_nhds.inner (hlim.sub tendsto_const_nhds))
  exact ge_of_tendsto' hD (fun k => hA.nonneg _ (hzkS k) _ hy)

lemma step_reset {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    {i : Fin m} {x x' : EuclideanSpace ℝ (Fin p)} {u u' : Fin m → ℝ}
    (hstep : IsMethodStep S g a b i x u x' u') :
    (∀ j, j ≠ i → u' j = u j) ∧
      (b i < inner ℝ (a i) x → b i < inner ℝ (a i) x' → u' i = 0) := by
  obtain ⟨hx'S, hcase⟩ := hstep
  rcases hcase with ⟨hlt, lam, hgx, hax, hu'⟩ | ⟨hcond, hx', hu'⟩ |
      ⟨hgt, hupos, μ', y, hyS, hgy, hay, hgx, hu'⟩
  · refine ⟨fun j hj => by rw [hu', Function.update_of_ne hj], fun h1 _ => ?_⟩
    exact absurd h1 (not_lt.2 hlt.le)
  · refine ⟨fun j _ => by rw [hu'], fun h1 _ => ?_⟩
    rcases hcond with h | ⟨_, h⟩
    · linarith
    · rw [hu']; exact h
  · refine ⟨fun j hj => by rw [hu', Function.update_of_ne hj], fun _ h2 => ?_⟩
    rw [hu', Function.update_self]
    by_cases hle : u i ≤ μ'
    · rw [min_eq_right hle]; ring
    · rw [not_le] at hle
      rw [min_eq_left hle.le] at hgx
      have hgg : g x' - g y = 0 := by rw [hgx, hgy, sub_self]
      have hxy := (mono hA hx'S hyS 0 hgg).2 (by simp)
      rw [hxy] at h2
      linarith

lemma arith {m s : ℕ} (hm : 0 < m) (i : ℕ) (hi : i < m) :
    s ≤ m * (s / m + 2) ∧ m * (s / m + 2) ≤ s + 2 * m ∧
    s ≤ m * (s / m + 1) + i ∧ m * (s / m + 1) + i + 1 ≤ m * (s / m + 2) ∧
    (m * (s / m + 1) + i) % m = i ∧
    ∀ t, m * (s / m + 1) + i < t → t < m * (s / m + 2) → t % m ≠ i := by
  have h := Nat.div_add_mod s m
  have hr := Nat.mod_lt s hm
  obtain ⟨q, hq⟩ : ∃ q, q = s / m := ⟨_, rfl⟩
  rw [← hq] at h ⊢
  obtain ⟨r, hr'⟩ : ∃ r, r = s % m := ⟨_, rfl⟩
  rw [← hr'] at h hr
  obtain ⟨T, hT⟩ : ∃ T, T = m * q := ⟨_, rfl⟩
  have e2 : m * (q + 2) = T + 2 * m := by rw [hT]; ring
  have e1 : m * (q + 1) = T + m := by rw [hT]; ring
  rw [← hT] at h
  rw [e2, e1]
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
  · rw [show T + m + i = i + m * (q + 1) by rw [hT]; ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hi]
  · intro t h1 h2
    obtain ⟨d, hd⟩ : ∃ d, d = t - (T + m) := ⟨_, rfl⟩
    have hdm : d < m := by omega
    have hdi : i < d := by omega
    rw [show t = d + m * (q + 1) by rw [e1]; omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hdm]
    omega

lemma uniq {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {A : Fin m → Set (EuclideanSpace ℝ (Fin p))}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hA : BregmanRelax.Cyclic.DConditions A S (bregmanD f g) P)
    (hfcl : ContinuousOn f (closure S)) {z y' : EuclideanSpace ℝ (Fin p)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)}
    (hz : z ∈ closure S) (hyS : ∀ k, y k ∈ S) (hy : Tendsto y atTop (nhds y'))
    (hD : Tendsto (fun k => bregmanD f g z (y k)) atTop (nhds 0)) : z = y' := by
  have hy'cl : y' ∈ closure S := mem_closure_of_tendsto hy (Eventually.of_forall hyS)
  have hex : ∀ k : ℕ, ∃ w ∈ S, dist w z < 1 / ((k : ℝ) + 1) ∧
      bregmanD f g w (y k) < bregmanD f g z (y k) + 1 / ((k : ℝ) + 1) := by
    intro k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hcont : ContinuousWithinAt (fun w => bregmanD f g w (y k)) (closure S) z := by
      unfold bregmanD
      exact ((hfcl z hz).sub continuousWithinAt_const).sub
        ((continuous_const.inner (continuous_id.sub continuous_const)).continuousWithinAt)
    have h1 : ∀ᶠ w in nhdsWithin z (closure S),
        bregmanD f g w (y k) < bregmanD f g z (y k) + 1 / ((k : ℝ) + 1) :=
      hcont.eventually_mem (Iio_mem_nhds (by linarith))
    have h2 := h1.filter_mono (nhdsWithin_mono z subset_closure)
    have h3 : ∀ᶠ w in nhdsWithin z S, dist w z < 1 / ((k : ℝ) + 1) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hε)
    have : (nhdsWithin z S).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
    obtain ⟨w, hwS, hw1, hw2⟩ :=
      ((eventually_mem_nhdsWithin : ∀ᶠ w in nhdsWithin z S, w ∈ S).and (h3.and h2)).exists
    exact ⟨w, hwS, hw1, hw2⟩
  choose w hwS hwd hwD using hex
  have hw : Tendsto w atTop (nhds z) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun k => dist_nonneg)
      (fun k => (hwd k).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  have hsum : Tendsto (fun k => bregmanD f g z (y k) + 1 / ((k : ℝ) + 1)) atTop (nhds 0) := by
    simpa using hD.add tendsto_one_div_add_atTop_nhds_zero_nat
  have hwD0 : Tendsto (fun k => bregmanD f g (w k) (y k)) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun k => hA.nonneg _ (hwS k) _ (hyS k)) (fun k => (hwD k).le)
  have hball : ∀ n, w n ∈ Metric.closedBall z 1 := by
    intro n
    rw [Metric.mem_closedBall]
    have h0 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := n.cast_nonneg (α := ℝ)
      linarith
    exact (hwd n).le.trans h0
  have := hA.conv w y y' hwS hyS hwD0 hy hy'cl
    ⟨Metric.closedBall z 1, (isCompact_closedBall z 1).isSeqCompact, hball⟩
  exact tendsto_nhds_unique hw this

end F63a94e2Aux

open BregmanRelax.IneqConstr in
theorem solution {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hS : Convex ℝ S) (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x) (hgc : ContinuousOn g S)
    (hfcl : ContinuousOn f (closure S))
    (ha : ∀ i, a i ≠ 0)
    (hRne : (feasibleIneq a b S).Nonempty)
    (hA : BregmanRelax.Cyclic.DConditions (BregmanRelax.EqConstr.hyperplane a b) S (BregmanRelax.EqConstr.bregmanD f g) P)
    (h2 : BregmanRelax.EqConstr.Cond2 S (BregmanRelax.EqConstr.bregmanD f g))
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S)
    (hV : BregmanRelax.Cyclic.CondV S (BregmanRelax.EqConstr.bregmanD f g) (feasibleIneq a b S))
    (hm : 0 < m) (x : ℕ → EuclideanSpace ℝ (Fin p)) (u : ℕ → Fin m → ℝ)
    (hx : IsMethodRun hm S g a b x u) :
    ∃ x' : EuclideanSpace ℝ (Fin p), Filter.Tendsto x Filter.atTop (nhds x') ∧
      x' ∈ feasibleIneq a b S ∧ ∀ y ∈ feasibleIneq a b S, f x' ≤ f y := by
  have hinv : ∀ n, x n ∈ S ∧ (∀ j, 0 ≤ u n j) ∧ g (x n) = ∑ j, u n j • a j := by
    intro n
    induction n with
    | zero => exact ⟨interior_subset hx.1, hx.2.1, hx.2.2.1⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3, -, -⟩ :=
        F63a94e2Aux.step_props hA ih.1 ih.2.1 ih.2.2 (hx.2.2.2 n)
      exact ⟨h1, h2, h3⟩
  have hstepP := fun n =>
    F63a94e2Aux.step_props hA (hinv n).1 (hinv n).2.1 (hinv n).2.2 (hx.2.2.2 n)
  have hres := fun n => F63a94e2Aux.step_reset hA (hx.2.2.2 n)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, Ψ n = phi f a b (x n) (u n) := ⟨_, fun n => rfl⟩
  have hDle : ∀ n, BregmanRelax.EqConstr.bregmanD f g (x (n + 1)) (x n) ≤ Ψ (n + 1) - Ψ n := by
    intro n
    rw [F63a94e2Aux.phi_diff f g a b (hinv n).2.2 (x (n + 1)) (u (n + 1)), hΨ, hΨ]
    linarith [(hstepP n).2.2.2.2]
  have hD0 : ∀ n, 0 ≤ BregmanRelax.EqConstr.bregmanD f g (x (n + 1)) (x n) :=
    fun n => hA.nonneg _ (hinv (n + 1)).1 _ (hinv n).1
  have hmono : Monotone Ψ := monotone_nat_of_le_succ (fun n => by linarith [hDle n, hD0 n])
  have hgap : ∀ z n, f z - Ψ n = BregmanRelax.EqConstr.bregmanD f g z (x n)
      + ∑ j, u n j * (inner ℝ (a j) z - b j) := by
    intro z n
    rw [hΨ, F63a94e2Aux.phi_diff f g a b (hinv n).2.2 z (u n)]
    simp only [sub_self, zero_mul, Finset.sum_const_zero, add_zero]
    unfold phi
    ring
  have hsumR : ∀ z ∈ feasibleIneq a b S, ∀ n, 0 ≤ ∑ j, u n j * (inner ℝ (a j) z - b j) :=
    fun z hz n => Finset.sum_nonneg (fun j _ => mul_nonneg ((hinv n).2.1 j) (by linarith [hz.1 j]))
  have hDR : ∀ z ∈ feasibleIneq a b S, ∀ n,
      0 ≤ BregmanRelax.EqConstr.bregmanD f g z (x n) :=
    fun z hz n => F63a94e2Aux.D_nonneg_closure hA hfcl hz.2 (hinv n).1
  have hΨR : ∀ z ∈ feasibleIneq a b S, ∀ n, Ψ n ≤ f z :=
    fun z hz n => by linarith [hgap z n, hDR z hz n, hsumR z hz n]
  obtain ⟨z, hzR⟩ := hRne
  have hK : ∀ n, x n ∈ {y | y ∈ S ∧ BregmanRelax.EqConstr.bregmanD f g z y ≤ f z - Ψ 0} :=
    fun n => ⟨(hinv n).1, by linarith [hgap z n, hsumR z hzR n, hmono (Nat.zero_le n)]⟩
  have hKc := hV z hzR (f z - Ψ 0)
  have hconv : Filter.Tendsto Ψ Filter.atTop (nhds (⨆ n, Ψ n)) :=
    tendsto_atTop_ciSup hmono ⟨f z, by rintro _ ⟨n, rfl⟩; exact hΨR z hzR n⟩
  have hdiff : Filter.Tendsto (fun n => Ψ (n + 1) - Ψ n) Filter.atTop (nhds 0) := by
    have := ((Filter.tendsto_add_atTop_iff_nat 1).2 hconv).sub hconv
    simpa using this
  have part1 : Filter.Tendsto (fun n => BregmanRelax.EqConstr.bregmanD f g (x (n + 1)) (x n))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff hD0 hDle
  have hshift : ∀ (σ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin p)), StrictMono σ →
      Filter.Tendsto (x ∘ σ) Filter.atTop (nhds x') →
      ∀ j, Filter.Tendsto (fun k => x (σ k + j)) Filter.atTop (nhds x') := by
    intro σ x' hσ hlim j
    have hx'cl : x' ∈ closure S :=
      mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => (hinv (σ k)).1)
    induction j with
    | zero => simpa [Function.comp_def] using hlim
    | succ j ih =>
      have hσj : Filter.Tendsto (fun k => σ k + j) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono (fun k => Nat.le_add_right (σ k) j) hσ.tendsto_atTop
      exact hA.conv (fun k => x (σ k + j + 1)) (fun k => x (σ k + j)) x'
        (fun k => (hinv _).1) (fun k => (hinv _).1) (part1.comp hσj) ih hx'cl
        ⟨_, hKc, fun k => hK _⟩
  have hfeas : ∀ (σ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin p)), StrictMono σ →
      Filter.Tendsto (x ∘ σ) Filter.atTop (nhds x') → x' ∈ feasibleIneq a b S := by
    intro σ x' hσ hlim
    have hx'cl : x' ∈ closure S :=
      mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => (hinv (σ k)).1)
    refine ⟨fun i => ?_, hx'cl⟩
    by_contra hcon
    rw [not_le] at hcon
    have hU : IsOpen {y : EuclideanSpace ℝ (Fin p) | inner ℝ (a i) y < b i} :=
      isOpen_lt (continuous_const.inner continuous_id) continuous_const
    have hev : ∀ᶠ k in Filter.atTop, ∀ j ∈ Finset.range (2 * m + 1),
        x (σ k + j) ∈ {y | inner ℝ (a i) y < b i} :=
      (Filter.eventually_all_finset _).2
        (fun j _ => (hshift σ x' hσ hlim j).eventually (hU.mem_nhds hcon))
    obtain ⟨k, hk⟩ := hev.exists
    obtain ⟨-, -, hle1, hle2, hmod, -⟩ := F63a94e2Aux.arith (s := σ k) hm i.val i.2
    have hj : m * (σ k / m + 1) + i.val + 1 - σ k ∈ Finset.range (2 * m + 1) := by
      rw [Finset.mem_range]
      have := F63a94e2Aux.arith (s := σ k) hm i.val i.2
      omega
    have hx1 := hk _ hj
    rw [show σ k + (m * (σ k / m + 1) + i.val + 1 - σ k) = m * (σ k / m + 1) + i.val + 1 by
      omega] at hx1
    have h4 := (hstepP (m * (σ k / m + 1) + i.val)).2.2.2.1
    have hi : (⟨(m * (σ k / m + 1) + i.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = i := Fin.ext hmod
    rw [hi] at h4
    exact absurd hx1 (not_lt.2 h4)
  -- a limit point
  obtain ⟨xs, -, σ0, hσ0, hlim0⟩ := hKc hK
  have hxsR := hfeas σ0 xs hσ0 hlim0
  have hsh0 := hshift σ0 xs hσ0 hlim0
  -- the reset times
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ, ∀ k, N k = m * (σ0 k / m + 2) := ⟨_, fun k => rfl⟩
  have hreset : ∀ k (i : Fin m), b i < inner ℝ (a i) xs →
      (∀ j ∈ Finset.range (2 * m + 1), x (σ0 k + j) ∈ {y | b i < inner ℝ (a i) y}) →
      u (N k) i = 0 := by
    intro k i _ hk
    obtain ⟨-, hNle, hle1, hle2, hmod, hne⟩ := F63a94e2Aux.arith (s := σ0 k) hm i.val i.2
    obtain ⟨n0, hn0⟩ : ∃ n0, n0 = m * (σ0 k / m + 1) + i.val := ⟨_, rfl⟩
    rw [← hn0] at hle1 hle2 hmod hne
    have hidx : (⟨n0 % m, Nat.mod_lt _ hm⟩ : Fin m) = i := Fin.ext hmod
    have hA0 : x n0 ∈ {y | b i < inner ℝ (a i) y} := by
      have := hk (n0 - σ0 k) (by rw [Finset.mem_range]; omega)
      rwa [show σ0 k + (n0 - σ0 k) = n0 by omega] at this
    have hA1 : x (n0 + 1) ∈ {y | b i < inner ℝ (a i) y} := by
      have := hk (n0 + 1 - σ0 k) (by rw [Finset.mem_range]; omega)
      rwa [show σ0 k + (n0 + 1 - σ0 k) = n0 + 1 by omega] at this
    have hbase : u (n0 + 1) i = 0 := by
      have := (hres n0).2
      rw [hidx] at this
      exact this hA0 hA1
    have hpers : ∀ d, n0 + 1 + d ≤ N k → u (n0 + 1 + d) i = 0 := by
      intro d
      induction d with
      | zero => intro _; simpa using hbase
      | succ d ih =>
        intro hd
        have hne' : (⟨(n0 + 1 + d) % m, Nat.mod_lt _ hm⟩ : Fin m) ≠ i := by
          intro h
          have := congrArg Fin.val h
          exact hne (n0 + 1 + d) (by omega) (by rw [← hN k]; omega) this
        have := (hres (n0 + 1 + d)).1 i (Ne.symm hne')
        rw [show n0 + 1 + (d + 1) = n0 + 1 + d + 1 by ring, this]
        exact ih (by omega)
    have := hpers (N k - (n0 + 1)) (by rw [hN k]; omega)
    rwa [show n0 + 1 + (N k - (n0 + 1)) = N k by rw [hN k]; omega] at this
  -- window eventually
  have hwin : ∀ᶠ k in Filter.atTop, ∀ i : Fin m, b i < inner ℝ (a i) xs →
      ∀ j ∈ Finset.range (2 * m + 1), x (σ0 k + j) ∈ {y | b i < inner ℝ (a i) y} := by
    rw [Filter.eventually_all]
    intro i
    by_cases h : b i < inner ℝ (a i) xs
    · have hU : IsOpen {y : EuclideanSpace ℝ (Fin p) | b i < inner ℝ (a i) y} :=
        isOpen_lt continuous_const (continuous_const.inner continuous_id)
      filter_upwards [(Filter.eventually_all_finset _).2
        (fun j _ => (hsh0 j).eventually (hU.mem_nhds h))] with k hk _ using hk
    · exact Filter.Eventually.of_forall (fun k h' => absurd h' h)
  have hsum0 : ∀ᶠ k in Filter.atTop, ∑ j, u (N k) j * (inner ℝ (a j) xs - b j) = 0 := by
    filter_upwards [hwin] with k hk
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rcases (hxsR.1 i).eq_or_lt with h | h
    · rw [← h, sub_self, mul_zero]
    · rw [hreset k i h (hk i h), zero_mul]
  have hNtop : Filter.Tendsto N Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun k => le_trans (hσ0.id_le k)
      (by rw [hN k]; exact (F63a94e2Aux.arith (s := σ0 k) hm 0 hm).1)) Filter.tendsto_id
  have hxN : Filter.Tendsto (fun k => x (N k)) Filter.atTop (nhds xs) := by
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro V hV
    filter_upwards [(Filter.eventually_all_finset (Finset.range (2 * m + 1))).2
      (fun j _ => (hsh0 j).eventually_mem hV)] with k hk
    obtain ⟨hle, hle', -⟩ := F63a94e2Aux.arith (s := σ0 k) hm 0 hm
    have := hk (N k - σ0 k) (by rw [Finset.mem_range, hN k]; omega)
    rwa [show σ0 k + (N k - σ0 k) = N k by rw [hN k]; omega] at this
  have hDN : Filter.Tendsto (fun k => BregmanRelax.EqConstr.bregmanD f g xs (x (N k)))
      Filter.atTop (nhds 0) :=
    h2 (fun k => x (N k)) xs (fun k => (hinv _).1) hxsR.2 hxN
  have hΨN2 : Filter.Tendsto (fun k => Ψ (N k)) Filter.atTop (nhds (f xs - 0)) := by
    refine (tendsto_const_nhds.sub hDN).congr' ?_
    filter_upwards [hsum0] with k hk
    have := hgap xs (N k)
    rw [hk] at this
    linarith
  have hc : (⨆ n, Ψ n) = f xs := by
    have := tendsto_nhds_unique (hconv.comp hNtop) hΨN2
    rw [this, sub_zero]
  have hopt : ∀ y ∈ feasibleIneq a b S, f xs ≤ f y := by
    intro y hy
    rw [← hc]
    exact ciSup_le (fun n => hΨR y hy n)
  have hgapT : Filter.Tendsto (fun n => f xs - Ψ n) Filter.atTop (nhds 0) := by
    have := (tendsto_const_nhds (x := f xs)).sub hconv
    rwa [hc, sub_self] at this
  have hDall : Filter.Tendsto (fun n => BregmanRelax.EqConstr.bregmanD f g xs (x n))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgapT (hDR xs hxsR)
      (fun n => by linarith [hgap xs n, hsumR xs hxsR n])
  refine ⟨xs, ?_, hxsR, hopt⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨a', -, ms, hms, hlim⟩ := hKc (fun n => hK (ns n))
  refine ⟨ms, ?_⟩
  have hnm : Filter.Tendsto (fun k => ns (ms k)) Filter.atTop Filter.atTop :=
    hns.comp hms.tendsto_atTop
  have heq : xs = a' := F63a94e2Aux.uniq hA hfcl hxsR.2 (fun k => (hinv _).1) hlim
    (hDall.comp hnm)
  rw [heq]
  exact hlim
