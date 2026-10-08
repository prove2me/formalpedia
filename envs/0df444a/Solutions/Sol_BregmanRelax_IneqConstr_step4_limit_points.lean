-- Prove2me | solution 1 for BregmanRelax.IneqConstr.step4_limit_points
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:30:07.80947+00:00
-- url     : https://prove2.me/submissions/4182de5a-5a7e-4d37-8274-0714b4bf9c6d

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_IneqConstr_Program

set_option autoImplicit false

namespace C5bf8549Aux

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

end C5bf8549Aux

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
    Filter.Tendsto (fun n => BregmanRelax.EqConstr.bregmanD f g (x (n + 1)) (x n)) Filter.atTop (nhds 0) ∧
      ∀ (σ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin p)), StrictMono σ →
        Filter.Tendsto (x ∘ σ) Filter.atTop (nhds x') → x' ∈ feasibleIneq a b S := by
  have hinv : ∀ n, x n ∈ S ∧ (∀ j, 0 ≤ u n j) ∧ g (x n) = ∑ j, u n j • a j := by
    intro n
    induction n with
    | zero => exact ⟨interior_subset hx.1, hx.2.1, hx.2.2.1⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3, -, -⟩ :=
        C5bf8549Aux.step_props hA ih.1 ih.2.1 ih.2.2 (hx.2.2.2 n)
      exact ⟨h1, h2, h3⟩
  have hstepP := fun n =>
    C5bf8549Aux.step_props hA (hinv n).1 (hinv n).2.1 (hinv n).2.2 (hx.2.2.2 n)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, Ψ n = phi f a b (x n) (u n) := ⟨_, fun n => rfl⟩
  have hDle : ∀ n, BregmanRelax.EqConstr.bregmanD f g (x (n + 1)) (x n) ≤ Ψ (n + 1) - Ψ n := by
    intro n
    rw [C5bf8549Aux.phi_diff f g a b (hinv n).2.2 (x (n + 1)) (u (n + 1)), hΨ, hΨ]
    linarith [(hstepP n).2.2.2.2]
  have hD0 : ∀ n, 0 ≤ BregmanRelax.EqConstr.bregmanD f g (x (n + 1)) (x n) :=
    fun n => hA.nonneg _ (hinv (n + 1)).1 _ (hinv n).1
  have hmono : Monotone Ψ := monotone_nat_of_le_succ (fun n => by linarith [hDle n, hD0 n])
  obtain ⟨z, hzR⟩ := hRne
  have hphiz : ∀ n, phi f a b z (u n) ≤ f z := by
    intro n
    unfold phi
    have : 0 ≤ ∑ j, u n j * (inner ℝ (a j) z - b j) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg ((hinv n).2.1 j) (by linarith [hzR.1 j]))
    linarith
  have hDz : ∀ n, BregmanRelax.EqConstr.bregmanD f g z (x n) = phi f a b z (u n) - Ψ n := by
    intro n
    rw [C5bf8549Aux.phi_diff f g a b (hinv n).2.2 z (u n), hΨ]
    simp
  have hDz0 : ∀ n, 0 ≤ BregmanRelax.EqConstr.bregmanD f g z (x n) :=
    fun n => C5bf8549Aux.D_nonneg_closure hA hfcl hzR.2 (hinv n).1
  have hΨb : ∀ n, Ψ n ≤ f z := fun n => by linarith [hDz n, hDz0 n, hphiz n]
  have hK : ∀ n, x n ∈ {y | y ∈ S ∧ BregmanRelax.EqConstr.bregmanD f g z y ≤ f z - Ψ 0} :=
    fun n => ⟨(hinv n).1, by linarith [hDz n, hphiz n, hmono (Nat.zero_le n)]⟩
  have hKc := hV z hzR (f z - Ψ 0)
  have hconv : Filter.Tendsto Ψ Filter.atTop (nhds (⨆ n, Ψ n)) :=
    tendsto_atTop_ciSup hmono ⟨f z, by rintro _ ⟨n, rfl⟩; exact hΨb n⟩
  have hdiff : Filter.Tendsto (fun n => Ψ (n + 1) - Ψ n) Filter.atTop (nhds 0) := by
    have := ((Filter.tendsto_add_atTop_iff_nat 1).2 hconv).sub hconv
    simpa using this
  have part1 : Filter.Tendsto (fun n => BregmanRelax.EqConstr.bregmanD f g (x (n + 1)) (x n))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff hD0 hDle
  refine ⟨part1, ?_⟩
  intro σ x' hσ hlim
  have hx'cl : x' ∈ closure S :=
    mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => (hinv (σ k)).1)
  have hshift : ∀ j, Filter.Tendsto (fun k => x (σ k + j)) Filter.atTop (nhds x') := by
    intro j
    induction j with
    | zero => simpa [Function.comp_def] using hlim
    | succ j ih =>
      have hσj : Filter.Tendsto (fun k => σ k + j) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono (fun k => Nat.le_add_right (σ k) j) hσ.tendsto_atTop
      exact hA.conv (fun k => x (σ k + j + 1)) (fun k => x (σ k + j)) x'
        (fun k => (hinv _).1) (fun k => (hinv _).1) (part1.comp hσj) ih hx'cl
        ⟨_, hKc, fun k => hK _⟩
  refine ⟨fun i => ?_, hx'cl⟩
  by_contra hcon
  rw [not_le] at hcon
  have hU : IsOpen {y : EuclideanSpace ℝ (Fin p) | inner ℝ (a i) y < b i} :=
    isOpen_lt (continuous_const.inner continuous_id) continuous_const
  have hev : ∀ᶠ k in Filter.atTop, ∀ j ∈ Finset.range (2 * m + 1),
      x (σ k + j) ∈ {y | inner ℝ (a i) y < b i} :=
    (Filter.eventually_all_finset _).2 (fun j _ => (hshift j).eventually (hU.mem_nhds hcon))
  obtain ⟨k, hk⟩ := hev.exists
  obtain ⟨q, r, t, ht, hr, hdm⟩ : ∃ q r t, t = m * q ∧ r < m ∧ t + r = σ k :=
    ⟨σ k / m, σ k % m, _, rfl, Nat.mod_lt _ hm, Nat.div_add_mod (σ k) m⟩
  have hnmod : (t + m + i.val) % m = i.val := by
    rw [ht, show m * q + m + i.val = i.val + m * (q + 1) by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt i.2]
  have hj : t + m + i.val + 1 - σ k ∈ Finset.range (2 * m + 1) := by
    rw [Finset.mem_range]; have := i.2; omega
  have hx1 := hk _ hj
  rw [show σ k + (t + m + i.val + 1 - σ k) = t + m + i.val + 1 by omega] at hx1
  have h4 := (hstepP (t + m + i.val)).2.2.2.1
  have hi : (⟨(t + m + i.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = i := Fin.ext hnmod
  rw [hi] at h4
  exact absurd hx1 (not_lt.2 h4)
